package dev.hybridserver;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.attribute.PosixFilePermission;
import java.security.DigestInputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.Duration;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HexFormat;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.locks.ReentrantLock;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;
import java.util.zip.GZIPInputStream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

final class Runtime {
    private static final long MAX_ARCHIVE_BYTES = 700L * 1024 * 1024;
    private static final long MAX_EXTRACTED_BYTES = 1_500L * 1024 * 1024;
    private static final int MAX_ARCHIVE_ENTRIES = 200_000;
    private static final HttpClient CLIENT = HttpClient.newBuilder()
            .connectTimeout(Duration.ofSeconds(20))
            .followRedirects(HttpClient.Redirect.NORMAL)
            .build();
    private static final ConcurrentHashMap<String, ReentrantLock> JVM_LOCKS = new ConcurrentHashMap<>();

    private Runtime() {
    }

    static Integer fallbackFeature(String output) {
        Matcher paper = Pattern.compile("(?i)Unsupported Java detected \\([\\d.]+\\)\\. Only up to Java (\\d+) is supported")
                .matcher(output);
        if (paper.find()) return nearestLtsAtOrBelow(Integer.parseInt(paper.group(1)));

        Matcher classVersion = Pattern.compile("(?i)Unsupported class file major version (\\d+)")
                .matcher(output);
        if (classVersion.find()) {
            int feature = Integer.parseInt(classVersion.group(1)) - 44;
            return nearestLtsBelow(feature);
        }

        if (output.contains("NoSuchMethodError: sun.security.util.ManifestEntryVerifier.<init>(Ljava/util/jar/Manifest;)V")) {
            return 8;
        }
        if (output.contains("java.base does not export sun.security.util")) return 8;
        if (output.contains("IllegalAccessError")
                && output.contains("java.base does not export")) return 8;
        return null;
    }

    static boolean isLegacyForgeRuntimeMismatch(String output) {
        return output.contains("sun.security.util.ManifestEntryVerifier")
                && (output.contains("java.base does not export")
                || output.contains("NoSuchMethodError"));
    }

    static Path ensureLegacyForgeFallback(Path root, String javaExecutable, String output)
            throws IOException, InterruptedException {
        int currentFeature = javaFeature(javaExecutable);
        RuntimeTarget target = legacyForgeFallbackTarget(currentFeature, output);
        return ensure(root, target.feature(), target.release());
    }

    static RuntimeTarget legacyForgeFallbackTarget(int currentFeature, String output) {
        if (output.contains("NoSuchMethodError: sun.security.util.ManifestEntryVerifier.<init>(Ljava/util/jar/Manifest;)V")) {
            return switch (currentFeature) {
                case 8 -> new RuntimeTarget(8, "8u312-b07");
                case 11 -> new RuntimeTarget(11, "11.0.13+8");
                case 17 -> new RuntimeTarget(17, "17.0.1+12");
                default -> new RuntimeTarget(8, "8u312-b07");
            };
        }
        return new RuntimeTarget(8, "8u312-b07");
    }

    static Path ensure(Path root, int feature) throws IOException, InterruptedException {
        return ensure(root, feature, null);
    }

    private static Path ensure(Path root, int feature, String release)
            throws IOException, InterruptedException {
        String platform = platformKey();
        String versionKey = release == null ? Integer.toString(feature) : release;
        String key = versionKey + "-" + platform;
        Path runtimes = root.resolve("runtimes").toAbsolutePath().normalize();
        Path install = runtimes.resolve("temurin-" + key);
        Path javaExecutable = findJava(install);
        if (javaExecutable != null && isExpectedFeature(javaExecutable, feature)) return javaExecutable;

        ReentrantLock jvmLock = JVM_LOCKS.computeIfAbsent(key, ignored -> new ReentrantLock());
        jvmLock.lockInterruptibly();
        try {
            Files.createDirectories(runtimes);
            Path lockPath = runtimes.resolve(".temurin-" + key + ".lock");
            try (FileChannel channel = FileChannel.open(lockPath,
                    java.nio.file.StandardOpenOption.CREATE, java.nio.file.StandardOpenOption.WRITE);
                 FileLock ignored = channel.lock()) {
                javaExecutable = findJava(install);
                if (javaExecutable != null && isExpectedFeature(javaExecutable, feature)) return javaExecutable;
                if (Files.exists(install, LinkOption.NOFOLLOW_LINKS)) deleteTree(install);
                installRuntime(runtimes, install, feature, release);
                javaExecutable = findJava(install);
                if (javaExecutable == null || !isExpectedFeature(javaExecutable, feature)) {
                    if (Files.exists(install, LinkOption.NOFOLLOW_LINKS)) deleteTree(install);
                    throw new IOException("Downloaded Temurin runtime does not contain a working Java " + feature
                            + " executable: " + install);
                }
                return javaExecutable;
            }
        } finally {
            jvmLock.unlock();
        }
    }

    private static void installRuntime(Path runtimes, Path install, int feature, String release)
            throws IOException, InterruptedException {
        String os = adoptiumOs();
        String architecture = adoptiumArchitecture();
        String encodedRelease = release == null ? null : release.replace("+", "%2B");
        String endpoint = release == null ? "latest/" + feature + "/hotspot" : "version/" + encodedRelease;
        URI metadataUri = URI.create("https://api.adoptium.net/v3/assets/" + endpoint
                + "?architecture=" + architecture + "&image_type=jre&os=" + os + "&vendor=eclipse");
        HttpRequest request = HttpRequest.newBuilder(metadataUri)
                .timeout(Duration.ofSeconds(30))
                .header("User-Agent", "HybridCore/1.0 (Java runtime manager)")
                .GET().build();
        HttpResponse<String> response = CLIENT.send(request,
                HttpResponse.BodyHandlers.ofString(StandardCharsets.UTF_8));
        if (response.statusCode() != 200) {
            throw new IOException("Temurin runtime lookup failed with HTTP " + response.statusCode()
                    + " for Java " + (release == null ? feature : release)
                    + " (" + os + "/" + architecture + ").");
        }
        RuntimePackage runtimePackage = parsePackage(response.body());
        if (!"https".equalsIgnoreCase(runtimePackage.uri().getScheme())) {
            throw new IOException("Temurin returned a non-HTTPS runtime package URL.");
        }

        Path archive = Files.createTempFile(runtimes, ".temurin-" + feature + "-", ".archive");
        Path staging = runtimes.resolve(".temurin-" + feature + "-staging-" + UUID.randomUUID());
        try {
            download(runtimePackage, archive);
            Files.createDirectory(staging);
            if (runtimePackage.name().toLowerCase(Locale.ROOT).endsWith(".zip")) {
                extractZip(archive, staging);
            } else if (runtimePackage.name().toLowerCase(Locale.ROOT).endsWith(".tar.gz")) {
                extractTarGz(archive, staging);
            } else {
                throw new IOException("Unsupported Temurin archive format: " + runtimePackage.name());
            }
            Path java = findJava(staging);
            if (java == null) throw new IOException("Temurin archive contains no bin/java executable.");
            makeExecutable(java);
            Files.move(staging, install, StandardCopyOption.ATOMIC_MOVE);
            System.out.printf("Installed verified Eclipse Temurin Java %s runtime in %s.%n",
                    release == null ? Integer.toString(feature) : feature + " (" + release + ")", install);
        } catch (java.nio.file.AtomicMoveNotSupportedException unsupported) {
            Files.move(staging, install);
            System.out.printf("Installed verified Eclipse Temurin Java %s runtime in %s.%n",
                    release == null ? Integer.toString(feature) : feature + " (" + release + ")", install);
        } finally {
            Files.deleteIfExists(archive);
            if (Files.exists(staging, LinkOption.NOFOLLOW_LINKS)) deleteTree(staging);
        }
    }

    private static RuntimePackage parsePackage(String json) throws IOException {
        Matcher packageObject = Pattern.compile("\"package\"\\s*:\\s*\\{(.*?)\\}", Pattern.DOTALL)
                .matcher(json);
        if (!packageObject.find()) throw new IOException("Temurin response does not contain a runtime package.");
        String data = packageObject.group(1);
        String name = jsonString(data, "name");
        String link = jsonString(data, "link");
        String checksum = jsonString(data, "checksum");
        if (name == null || link == null || checksum == null || !checksum.matches("(?i)[0-9a-f]{64}")) {
            throw new IOException("Temurin response is missing a valid package name, URL, or SHA-256 checksum.");
        }
        try {
            return new RuntimePackage(name, URI.create(link), checksum.toLowerCase(Locale.ROOT));
        } catch (IllegalArgumentException invalidUri) {
            throw new IOException("Temurin returned an invalid runtime package URL.", invalidUri);
        }
    }

    private static String jsonString(String json, String key) {
        Matcher matcher = Pattern.compile("\"" + Pattern.quote(key) + "\"\\s*:\\s*\"([^\"]*)\"")
                .matcher(json);
        return matcher.find() ? matcher.group(1) : null;
    }

    private static void download(RuntimePackage runtimePackage, Path destination)
            throws IOException, InterruptedException {
        HttpRequest request = HttpRequest.newBuilder(runtimePackage.uri())
                .timeout(Duration.ofMinutes(5))
                .header("User-Agent", "HybridCore/1.0 (Java runtime manager)")
                .GET().build();
        HttpResponse<InputStream> response = CLIENT.send(request, HttpResponse.BodyHandlers.ofInputStream());
        if (response.statusCode() < 200 || response.statusCode() >= 300) {
            try (InputStream ignored = response.body()) {
                throw new IOException("Temurin runtime download failed with HTTP " + response.statusCode() + ".");
            }
        }
        try (InputStream body = response.body()) {
            MessageDigest digest = sha256();
            try (DigestInputStream input = new DigestInputStream(body, digest);
                 OutputStream output = new BufferedOutputStream(Files.newOutputStream(destination))) {
                byte[] buffer = new byte[32 * 1024];
                int read;
                long total = 0;
                while ((read = input.read(buffer)) != -1) {
                    total += read;
                    if (total > MAX_ARCHIVE_BYTES) {
                        throw new IOException("Temurin runtime archive exceeds the 700 MiB download limit.");
                    }
                    output.write(buffer, 0, read);
                }
            }
            String actual = HexFormat.of().formatHex(digest.digest());
            if (!actual.equalsIgnoreCase(runtimePackage.sha256())) {
                throw new IOException("Temurin runtime SHA-256 verification failed for " + runtimePackage.name());
            }
        }
    }

    private static void extractZip(Path archive, Path destination) throws IOException {
        long total = 0;
        int entries = 0;
        try (InputStream input = new BufferedInputStream(Files.newInputStream(archive));
             ZipInputStream zip = new ZipInputStream(input)) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                if (++entries > MAX_ARCHIVE_ENTRIES) throw new IOException("Runtime archive has too many entries.");
                Path target = safeTarget(destination, entry.getName());
                if (entry.isDirectory()) {
                    Files.createDirectories(target);
                } else {
                    Files.createDirectories(target.getParent());
                    try (OutputStream output = Files.newOutputStream(target)) {
                        byte[] buffer = new byte[32 * 1024];
                        int read;
                        while ((read = zip.read(buffer)) != -1) {
                            total += read;
                            if (total > MAX_EXTRACTED_BYTES) {
                                throw new IOException("Extracted Temurin runtime exceeds the 1.5 GiB limit.");
                            }
                            output.write(buffer, 0, read);
                        }
                    }
                }
                zip.closeEntry();
            }
        }
    }

    private static void extractTarGz(Path archive, Path destination) throws IOException {
        long total = 0;
        int entries = 0;
        try (InputStream input = new BufferedInputStream(
                new GZIPInputStream(Files.newInputStream(archive)))) {
            byte[] header = new byte[512];
            while (readFully(input, header)) {
                if (allZero(header)) break;
                if (++entries > MAX_ARCHIVE_ENTRIES) throw new IOException("Runtime archive has too many entries.");
                String name = tarString(header, 0, 100);
                String prefix = tarString(header, 345, 155);
                if (!prefix.isEmpty()) name = prefix + "/" + name;
                long size = parseTarOctal(header, 124, 12);
                long mode = parseTarOctal(header, 100, 8);
                int type = header[156] & 0xff;
                Path target = safeTarget(destination, name);
                if (type == 0 || type == '0') {
                    if (size > MAX_EXTRACTED_BYTES - total) {
                        throw new IOException("Extracted Temurin runtime exceeds the 1.5 GiB limit.");
                    }
                    Files.createDirectories(target.getParent());
                    try (OutputStream output = new BufferedOutputStream(Files.newOutputStream(target))) {
                        copyExactly(input, output, size);
                    }
                    total += size;
                    setMode(target, mode);
                } else if (type == '5') {
                    Files.createDirectories(target);
                } else if (type == '2') {
                    String linkName = tarString(header, 157, 100);
                    Path link = target.getParent().resolve(linkName).normalize();
                    if (!link.startsWith(destination)) {
                        throw new IOException("Unsafe symbolic link in Temurin archive: " + name);
                    }
                    Files.createDirectories(target.getParent());
                    Files.createSymbolicLink(target, target.getParent().relativize(link));
                } else if (type == '1') {
                    throw new IOException("Hard links are not allowed in Temurin runtime archives: " + name);
                } else if (type != 'x' && type != 'g' && type != 'L' && type != 'K') {
                    throw new IOException("Unsupported entry type in Temurin archive: " + name);
                }
                long consumed = (type == 0 || type == '0') ? size : size;
                if (type != 0 && type != '0' && consumed > 0) skipExactly(input, consumed);
                long padding = (512 - (consumed % 512)) % 512;
                if (padding > 0) skipExactly(input, padding);
            }
        }
    }

    private static Path safeTarget(Path root, String entryName) throws IOException {
        String normalizedName = entryName.replace('\\', '/');
        if (normalizedName.isBlank() || normalizedName.startsWith("/")
                || normalizedName.matches("^[A-Za-z]:.*")) {
            throw new IOException("Unsafe path in Temurin archive: " + entryName);
        }
        Path target = root.resolve(normalizedName).normalize();
        if (!target.startsWith(root)) throw new IOException("Unsafe path in Temurin archive: " + entryName);
        return target;
    }

    private static boolean readFully(InputStream input, byte[] buffer) throws IOException {
        int offset = 0;
        while (offset < buffer.length) {
            int read = input.read(buffer, offset, buffer.length - offset);
            if (read < 0) {
                if (offset == 0) return false;
                throw new IOException("Truncated Temurin tar archive.");
            }
            offset += read;
        }
        return true;
    }

    private static void copyExactly(InputStream input, OutputStream output, long size) throws IOException {
        byte[] buffer = new byte[32 * 1024];
        long remaining = size;
        while (remaining > 0) {
            int read = input.read(buffer, 0, (int) Math.min(buffer.length, remaining));
            if (read < 0) throw new IOException("Truncated Temurin tar entry.");
            output.write(buffer, 0, read);
            remaining -= read;
        }
    }

    private static void skipExactly(InputStream input, long size) throws IOException {
        long remaining = size;
        while (remaining > 0) {
            long skipped = input.skip(remaining);
            if (skipped == 0) {
                if (input.read() < 0) throw new IOException("Truncated Temurin tar archive.");
                skipped = 1;
            }
            remaining -= skipped;
        }
    }

    private static String tarString(byte[] header, int offset, int length) {
        int end = offset;
        while (end < offset + length && header[end] != 0) end++;
        return new String(header, offset, end - offset, StandardCharsets.UTF_8);
    }

    private static long parseTarOctal(byte[] header, int offset, int length) throws IOException {
        String value = tarString(header, offset, length).trim();
        if (value.isEmpty()) return 0;
        try {
            return Long.parseLong(value, 8);
        } catch (NumberFormatException invalid) {
            throw new IOException("Invalid numeric field in Temurin tar archive.", invalid);
        }
    }

    private static boolean allZero(byte[] bytes) {
        for (byte value : bytes) if (value != 0) return false;
        return true;
    }

    private static void setMode(Path path, long mode) throws IOException {
        try {
            Set<PosixFilePermission> permissions = EnumSet.noneOf(PosixFilePermission.class);
            if ((mode & 0400) != 0) permissions.add(PosixFilePermission.OWNER_READ);
            if ((mode & 0200) != 0) permissions.add(PosixFilePermission.OWNER_WRITE);
            if ((mode & 0100) != 0) permissions.add(PosixFilePermission.OWNER_EXECUTE);
            if ((mode & 0040) != 0) permissions.add(PosixFilePermission.GROUP_READ);
            if ((mode & 0020) != 0) permissions.add(PosixFilePermission.GROUP_WRITE);
            if ((mode & 0010) != 0) permissions.add(PosixFilePermission.GROUP_EXECUTE);
            if ((mode & 0004) != 0) permissions.add(PosixFilePermission.OTHERS_READ);
            if ((mode & 0002) != 0) permissions.add(PosixFilePermission.OTHERS_WRITE);
            if ((mode & 0001) != 0) permissions.add(PosixFilePermission.OTHERS_EXECUTE);
            Files.setPosixFilePermissions(path, permissions);
        } catch (UnsupportedOperationException ignored) {
            path.toFile().setExecutable((mode & 0111) != 0, false);
        }
    }

    private static void makeExecutable(Path java) throws IOException {
        if (!java.toFile().setExecutable(true, false) && !Files.isExecutable(java)) {
            throw new IOException("Could not mark Java executable: " + java);
        }
    }

    private static Path findJava(Path root) throws IOException {
        if (!Files.isDirectory(root)) return null;
        String executable = isWindows() ? "java.exe" : "java";
        try (Stream<Path> paths = Files.walk(root)) {
            return paths.filter(path -> Files.isRegularFile(path, LinkOption.NOFOLLOW_LINKS)
                            || Files.isSymbolicLink(path))
                    .filter(path -> path.getFileName().toString().equalsIgnoreCase(executable))
                    .filter(Files::isExecutable)
                    .findFirst().orElse(null);
        }
    }

    private static boolean isExpectedFeature(Path javaExecutable, int feature) throws IOException, InterruptedException {
        Process process;
        try {
            process = new ProcessBuilder(javaExecutable.toString(), "-version").redirectErrorStream(true).start();
        } catch (IOException failure) {
            return false;
        }
        String output;
        try (InputStream input = process.getInputStream()) {
            output = new String(input.readAllBytes(), StandardCharsets.UTF_8);
        }
        if (!process.waitFor(15, java.util.concurrent.TimeUnit.SECONDS)) {
            process.destroyForcibly();
            return false;
        }
        Matcher version = Pattern.compile("version \"(?:1\\.)?(\\d+)").matcher(output);
        return process.exitValue() == 0 && version.find() && Integer.parseInt(version.group(1)) == feature;
    }

    private static int javaFeature(String javaExecutable) throws IOException, InterruptedException {
        Process process;
        try {
            process = new ProcessBuilder(javaExecutable, "-version").redirectErrorStream(true).start();
        } catch (IOException failure) {
            throw new IOException("Cannot determine the configured Java version for the Forge fallback: "
                    + javaExecutable, failure);
        }
        String output;
        try (InputStream input = process.getInputStream()) {
            output = new String(input.readAllBytes(), StandardCharsets.UTF_8);
        }
        if (!process.waitFor(15, java.util.concurrent.TimeUnit.SECONDS)) {
            process.destroyForcibly();
            throw new IOException("Timed out checking Java version for the Forge compatibility fallback.");
        }
        Matcher version = Pattern.compile("version \"(?:1\\.)?(\\d+)").matcher(output);
        if (process.exitValue() != 0 || !version.find()) {
            throw new IOException("Cannot determine the configured Java version for the Forge fallback: " + output);
        }
        return Integer.parseInt(version.group(1));
    }

    private static int nearestLtsAtOrBelow(int version) {
        for (int lts : new int[]{25, 21, 17, 11, 8}) if (lts <= version) return lts;
        throw new IllegalArgumentException("No supported Temurin LTS runtime is available at or below Java " + version);
    }

    private static int nearestLtsBelow(int version) {
        for (int lts : new int[]{25, 21, 17, 11, 8}) if (lts < version) return lts;
        throw new IllegalArgumentException("No supported Temurin LTS runtime is available below Java " + version);
    }

    private static String platformKey() {
        return adoptiumOs() + "-" + adoptiumArchitecture();
    }

    private static String adoptiumOs() {
        String os = System.getProperty("os.name").toLowerCase(Locale.ROOT);
        if (os.contains("win")) return "windows";
        if (os.contains("mac") || os.contains("darwin")) return "mac";
        if (os.contains("linux")) return "linux";
        throw new IllegalStateException("Automatic Temurin runtime download does not support this OS: " + os);
    }

    private static String adoptiumArchitecture() {
        return switch (System.getProperty("os.arch").toLowerCase(Locale.ROOT)) {
            case "amd64", "x86_64", "x64" -> "x64";
            case "aarch64", "arm64" -> "aarch64";
            case "x86", "i386", "i486", "i586", "i686" -> "x32";
            default -> throw new IllegalStateException("Automatic Temurin runtime download does not support this architecture: "
                    + System.getProperty("os.arch"));
        };
    }

    private static boolean isWindows() {
        return System.getProperty("os.name").toLowerCase(Locale.ROOT).contains("win");
    }

    private static MessageDigest sha256() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 is unavailable in this Java runtime.", impossible);
        }
    }

    private static void deleteTree(Path path) throws IOException {
        if (!Files.exists(path, LinkOption.NOFOLLOW_LINKS)) return;
        try (Stream<Path> entries = Files.walk(path)) {
            for (Path entry : entries.sorted(java.util.Comparator.reverseOrder()).toList()) {
                Files.deleteIfExists(entry);
            }
        }
    }

    private record RuntimePackage(String name, URI uri, String sha256) {
    }

    record RuntimeTarget(int feature, String release) {
    }
}
