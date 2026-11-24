package dev.hybridserver;

import java.io.IOException;
import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.URI;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.net.URLEncoder;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.SecureRandom;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Comparator;
import java.util.HexFormat;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.jar.JarFile;
import java.util.stream.Stream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

public final class Launcher {
    private static final Duration LOBBY_START_TIMEOUT = Duration.ofSeconds(120);
    private static final Duration PROXY_START_TIMEOUT = Duration.ofSeconds(45);
    private static final Pattern JAVA_MAJOR = Pattern.compile("version \"(?:1\\.)?(\\d+)");
    private static final List<String> PROXY_TYPES = List.of("velocity", "bungeecord", "waterfall");
    private static final List<String> SERVER_TYPES = List.of(
            "paper", "purpur", "spigot", "folia", "pufferfish", "leaf", "leaves",
            "fabric", "forge", "neoforge", "arclight", "mohist", "limbo");
    private static final List<String> PAPER_TYPES = List.of("paper", "purpur", "folia", "pufferfish", "leaf", "leaves");
    private static final List<String> BUKKIT_TYPES = List.of(
            "paper", "purpur", "spigot", "folia", "pufferfish", "leaf", "leaves", "arclight", "mohist");
    private static final List<String> LEGACY_AUTO_FORWARDING_TYPES = List.of("spigot");
    private static final String FABRIC_PROXY_LITE_PROJECT = "8dI2tmqs";
    private static final String FABRIC_API_PROJECT = "P7dR8mSH";
    private static final HttpClient HTTP_CLIENT = HttpClient.newBuilder()
            .connectTimeout(Duration.ofSeconds(15))
            .followRedirects(HttpClient.Redirect.NORMAL)
            .build();

    private Launcher() {
    }

    public static void main(String[] args) throws Exception {
        Path root = Path.of("").toAbsolutePath().normalize();
        Properties config = loadConfig(root.resolve("config/hybrid.properties"));
        String proxyType = normalizeProxy(config.getProperty("proxy.type", "velocity"));
        String lobbyType = normalizeLobby(config.getProperty("lobby.type", "paper"));
        String proxyBind = config.getProperty("proxy.bind", "0.0.0.0:25565").trim();
        int lobbyPort = Integer.parseInt(config.getProperty("lobby.port", "25566"));
        String proxyMemory = config.getProperty("proxy.memory", "1G");
        String proxyJava = config.getProperty("proxy.java", "java");
        boolean onlineMode = Boolean.parseBoolean(config.getProperty("proxy.online-mode", "true"));
        Path proxyDir = root.resolve("run/proxy");
        Path proxyJar = resolve(root, config.getProperty("proxy.jar"));
        List<GameServer> gameServers = loadGameServers(root, config, lobbyType, lobbyPort);
        validatePorts(proxyBind, gameServers);
        prepareDirectories(root, proxyDir, gameServers);
        boolean hasVelocityModernBackend = gameServers.stream()
                .anyMatch(server -> List.of("fabric", "forge", "neoforge").contains(server.type()));
        String velocityMode = proxyType.equals("velocity")
                ? resolveVelocityForwardingMode(proxyDir, gameServers,
                        config.getProperty("proxy.velocity-forwarding-mode", "auto"), hasVelocityModernBackend)
                : "legacy";
        if (hasVelocityModernBackend && !proxyType.equals("velocity")) {
            throw new IllegalArgumentException("Automatic modded forwarding setup requires Velocity modern forwarding. Use Velocity or install and configure a compatible forwarding mod yourself.");
        }
        if (hasVelocityModernBackend && !velocityMode.equals("modern")) {
            throw new IllegalArgumentException("FabricProxy-Lite, NeoVelocity and Proxy Compatible Forge require Velocity modern forwarding. Set player-info-forwarding-mode = \"modern\" in run/proxy/velocity.toml or proxy.velocity-forwarding-mode=modern.");
        }
        if (proxyType.equals("velocity") && velocityMode.equals("modern")
                && gameServers.stream().anyMatch(server -> List.of("arclight", "mohist").contains(server.type()))) {
            System.out.println("Modern forwarding selected for Arclight/Mohist. The launcher configures their native "
                    + "forwarding settings and synchronizes the shared secret.");
        }
        String secret = proxyType.equals("velocity") && velocityMode.equals("modern")
                ? loadOrCreateSecret(proxyDir.resolve("forwarding.secret")) : "";
        for (GameServer server : gameServers) {
            configureLobby(server.directory(), server.type(), server.minecraftVersion(), server.port(), proxyType,
                    onlineMode, secret, velocityMode);
        }
        configureProxy(proxyDir, proxyType, proxyBind, gameServers, onlineMode, velocityMode);
        requireJars(proxyJar, proxyType, gameServers);
        requireJava(proxyJava, proxyType);
        for (GameServer server : gameServers) {
            requireJava(server.java(), server.name());
            if (!server.type().equals("limbo")) requireEulaAccepted(server.directory().resolve("eula.txt"));
        }
        for (GameServer server : gameServers) {
            if (proxyType.equals("velocity")) {
                switch (server.type()) {
                    case "fabric" -> {
                        installFabricProxyLite(server);
                        configureFabricProxyLite(server.directory(), secret);
                    }
                    case "forge" -> {
                        requireSupportedForgeModernVersion(server);
                        installModrinthProject("vDyrHl8l", "forge", server, "proxy-compatible-forge");
                        configureProxyCompatibleForge(server.directory(), secret);
                    }
                    case "neoforge" -> {
                        installNeoForgeForwarding(server, secret);
                    }
                    default -> {
                    }
                }
            }
            validateForwardingConfiguration(server.directory(), proxyDir, server.type(), server.minecraftVersion(),
                    server.port(), proxyType, onlineMode, secret, velocityMode);
        }

        Map<String, List<String>> launchCommands = new LinkedHashMap<>();
        for (GameServer server : gameServers) {
            prepareServerLaunchFiles(server);
            List<String> launchArguments = resolveLaunchArguments(server);
            launchCommands.put(server.name(), launchArguments);
            if (server.launchArgs().equalsIgnoreCase("auto")) {
                System.out.printf("Using automatic %s launch profile for %s: %s%n",
                        title(server.type()), server.name(), String.join(" ", launchArguments));
                System.out.printf("Working directory for %s: %s%n", server.name(), server.directory());
            }
        }

        Files.copy(proxyJar, proxyDir.resolve("proxy.jar"), StandardCopyOption.REPLACE_EXISTING);
        copyPluginJars(root.resolve("plugins/proxy"), proxyDir.resolve("plugins"));
        for (GameServer server : gameServers) {
            copyPluginJars(root.resolve("plugins").resolve(server.name()), server.directory().resolve("plugins"));
        }

        List<RunningServer> runningServers = new ArrayList<>();
        Process proxy = null;
        try {
            for (GameServer server : gameServers) {
                System.out.printf("Starting %s on 127.0.0.1:%d%n", title(server.type()), server.port());
                runningServers.add(startGameServerWithRuntimeFallback(root, server,
                        launchCommands.get(server.name())));
            }

            System.out.printf("Starting %s proxy on %s%n", title(proxyType), proxyBind);
            ProcessBuilder proxyBuilder = new ProcessBuilder(proxyJava, "-Xms256M", "-Xmx" + proxyMemory, "-jar", "proxy.jar");
            proxyBuilder.directory(proxyDir.toFile()).redirectInput(ProcessBuilder.Redirect.PIPE)
                    .redirectOutput(ProcessBuilder.Redirect.INHERIT).redirectError(ProcessBuilder.Redirect.INHERIT);
            proxy = proxyBuilder.start();
            awaitListener(proxy, proxyHealthAddress(proxyBind), PROXY_START_TIMEOUT, title(proxyType));

            Process activeProxy = proxy;
            List<RunningServer> activeServers = List.copyOf(runningServers);
            java.lang.Runtime.getRuntime().addShutdownHook(new Thread(() -> stopAll(activeProxy, activeServers), "launcher-shutdown"));
            startConsoleInput(runningServers);
            System.out.println("Server is ready. Players should connect through the proxy address.");
            while (proxy.isAlive() && runningServers.stream().allMatch(server -> server.process().isAlive())) Thread.sleep(500);
            RunningServer stopped = runningServers.stream().filter(server -> !server.process().isAlive()).findFirst().orElse(null);
            if (stopped != null) throw new IllegalStateException("Game server '" + stopped.name() + "' stopped; stopping the proxy and other game servers.");
            throw new IllegalStateException("Proxy stopped; stopping all game servers.");
        } catch (Throwable failure) {
            stopAll(proxy, runningServers);
            throw failure;
        }
    }

    private static void startConsoleInput(List<RunningServer> gameServers) {
        Thread inputForwarder = new Thread(() -> {
            try {
                BufferedReader console = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
                Map<String, OutputStream> inputs = new ConcurrentHashMap<>();
                for (RunningServer server : gameServers) inputs.put(server.name(), server.process().getOutputStream());
                String command;
                while ((command = console.readLine()) != null) {
                    if (command.isBlank()) continue;
                    if (command.regionMatches(true, 0, "psw ", 0, 4)) {
                        String targetAndCommand = command.substring(4).trim();
                        int separator = targetAndCommand.indexOf(' ');
                        if (separator <= 0 || separator == targetAndCommand.length() - 1) {
                            System.err.println("Usage: psw <server-name> <command>");
                            continue;
                        }
                        String target = targetAndCommand.substring(0, separator).toLowerCase(Locale.ROOT);
                        OutputStream destination = inputs.get(target);
                        if (destination == null) {
                            System.err.println("Unknown game server '" + target + "'. Available: " + String.join(", ", inputs.keySet()));
                            continue;
                        }
                        sendCommand(destination, targetAndCommand.substring(separator + 1));
                    } else {
                        for (Map.Entry<String, OutputStream> entry : inputs.entrySet()) {
                            try {
                                sendCommand(entry.getValue(), command);
                            } catch (IOException error) {
                                System.err.println("Could not forward console input to game server '" + entry.getKey() + "': " + error.getMessage());
                            }
                        }
                    }
                }
            } catch (IOException error) {
                System.err.println("Could not read launcher console input: " + error.getMessage());
            }
        }, "game-server-console-input");
        inputForwarder.setDaemon(true);
        inputForwarder.start();
    }

    private static void sendCommand(OutputStream destination, String command) throws IOException {
        destination.write((command + "\n").getBytes(StandardCharsets.UTF_8));
        destination.flush();
    }

    private static RunningServer startGameServerWithRuntimeFallback(Path root, GameServer server,
                                                                    List<String> launchArguments)
            throws IOException, InterruptedException {
        String javaExecutable = server.java();
        for (int attempt = 0; attempt < 2; attempt++) {
            List<String> command = new ArrayList<>(List.of(javaExecutable, "-Xms256M",
                    "-Xmx" + server.memory()));
            command.addAll(launchArguments);
            ProcessBuilder builder = new ProcessBuilder(command);
            builder.directory(server.directory().toFile())
                    .redirectInput(ProcessBuilder.Redirect.PIPE)
                    .redirectErrorStream(true);
            Process process = builder.start();
            ProcessOutput output = forwardProcessOutput(process, title(server.type()));
            try {
                awaitListener(process, new InetSocketAddress("127.0.0.1", server.port()),
                        LOBBY_START_TIMEOUT, title(server.type()), output);
                return new RunningServer(server.name(), process);
            } catch (IllegalStateException startupFailure) {
                Integer fallback = attempt == 0 ? Runtime.fallbackFeature(output.snapshot()) : null;
                if (fallback == null) {
                    stop(process);
                    throw startupFailure;
                }
                stop(process);
                boolean legacyForgeRuntime = server.type().equals("forge")
                        && Runtime.isLegacyForgeRuntimeMismatch(output.snapshot());
                System.out.printf("%s failed with a recognized Java compatibility error; retrying with "
                                + "%s.%n",
                        title(server.type()), legacyForgeRuntime
                                ? "a compatible pinned Eclipse Temurin runtime"
                                : "Eclipse Temurin Java " + fallback);
                javaExecutable = (legacyForgeRuntime
                        ? Runtime.ensureLegacyForgeFallback(root, javaExecutable, output.snapshot())
                        : Runtime.ensure(root, fallback)).toString();
                requireJava(javaExecutable, server.name());
            }
        }
        throw new IllegalStateException("Runtime fallback exhausted for " + server.name() + ".");
    }

    private static ProcessOutput forwardProcessOutput(Process process, String name) {
        ProcessOutput output = new ProcessOutput();
        Thread reader = new Thread(() -> {
            try (BufferedReader input = new BufferedReader(
                    new InputStreamReader(process.getInputStream(), StandardCharsets.UTF_8))) {
                String line;
                while ((line = input.readLine()) != null) {
                    output.append(line);
                    System.out.println(line);
                }
            } catch (IOException error) {
                if (process.isAlive()) {
                    System.err.println("Could not read " + name + " startup output: " + error.getMessage());
                }
            }
        }, "server-output-" + name.toLowerCase(Locale.ROOT));
        reader.setDaemon(true);
        reader.start();
        output.setReader(reader);
        return output;
    }

    private static final class ProcessOutput {
        private static final int MAX_CHARS = 1_000_000;
        private final StringBuilder content = new StringBuilder();
        private volatile Thread reader;

        private synchronized void append(String line) {
            content.append(line).append('\n');
            if (content.length() > MAX_CHARS) content.delete(0, content.length() - MAX_CHARS);
        }

        private synchronized String snapshot() {
            return content.toString();
        }

        private void setReader(Thread reader) {
            this.reader = reader;
        }

        private void awaitReader() throws InterruptedException {
            Thread outputReader = reader;
            if (outputReader != null) outputReader.join(1000);
        }
    }

    private static Properties loadConfig(Path path) throws IOException {
        Files.createDirectories(path.getParent());
        Properties properties = new Properties();
        if (Files.exists(path)) {
            try (InputStream input = Files.newInputStream(path)) {
                properties.load(input);
            }
        }
        boolean changed = false;
        changed |= setDefault(properties, "proxy.type", null, "velocity");
        changed |= setDefault(properties, "proxy.jar", "velocity.jar", "server-libs/velocity.jar");
        changed |= setDefault(properties, "proxy.java", "velocity.java", "java");
        changed |= setDefault(properties, "proxy.memory", "velocity.memory", "1G");
        changed |= setDefault(properties, "proxy.bind", null, "0.0.0.0:25565");
        changed |= setDefault(properties, "proxy.online-mode", null, "true");
        changed |= setDefault(properties, "proxy.velocity-forwarding-mode", null, "auto");
        changed |= setDefault(properties, "lobby.type", null, "paper");
        changed |= setDefault(properties, "lobby.jar", "paper.jar", "server-libs/paper.jar");
        changed |= setDefault(properties, "lobby.java", "paper.java", "java");
        changed |= setDefault(properties, "lobby.memory", "paper.memory", "4G");
        changed |= setDefault(properties, "lobby.port", "paper.port", "25566");
        changed |= setDefault(properties, "lobby.launch-args", null, "auto");
        changed |= setDefault(properties, "lobby.minecraft-version", null, "");
        changed |= setDefault(properties, "plugin-servers", null, "");
        if (changed) {
            try (OutputStream output = Files.newOutputStream(path)) {
                properties.store(output, "Hybrid Server settings. Use JDK 25-compatible server builds.");
            }
        }
        return properties;
    }

    private static boolean setDefault(Properties properties, String key, String legacyKey, String defaultValue) {
        String current = properties.getProperty(key);
        if (current != null && !current.isBlank()) return false;
        String legacyValue = legacyKey == null ? null : properties.getProperty(legacyKey);
        properties.setProperty(key, legacyValue == null || legacyValue.isBlank() ? defaultValue : legacyValue);
        return true;
    }

    private static String resolveVelocityForwardingMode(Path proxyDir, List<GameServer> servers,
                                                        String configuredMode,
                                                        boolean hasVelocityModernBackend) throws IOException {
        String requested = configuredMode == null ? "auto" : configuredMode.trim().toLowerCase(Locale.ROOT);
        if (!requested.equals("auto")) return validateVelocityForwardingMode(requested);
        if (hasVelocityModernBackend) return "modern";
        if (servers.stream().anyMatch(server -> LEGACY_AUTO_FORWARDING_TYPES.contains(server.type()))) return "legacy";

        Path velocityConfig = proxyDir.resolve("velocity.toml");
        if (Files.isRegularFile(velocityConfig)) {
            return validateVelocityForwardingMode(readTomlValue(velocityConfig, "player-info-forwarding-mode")
                    .toLowerCase(Locale.ROOT));
        }
        return "modern";
    }

    private static String validateVelocityForwardingMode(String mode) {
        if (!List.of("modern", "legacy", "none").contains(mode)) {
            throw new IllegalArgumentException("Velocity forwarding mode must be one of: auto, modern, legacy, none; got '"
                    + mode + "'.");
        }
        return mode;
    }

    private static String normalizeProxy(String value) {
        String type = value.trim().toLowerCase(Locale.ROOT).replace("-", "");
        if (type.equals("bungee")) type = "bungeecord";
        if (!PROXY_TYPES.contains(type)) throw new IllegalArgumentException("proxy.type must be one of: " + String.join(", ", PROXY_TYPES));
        return type;
    }

    private static String normalizeLobby(String value) {
        String type = value.trim().toLowerCase(Locale.ROOT).replace(" ", "");
        if (!SERVER_TYPES.contains(type)) throw new IllegalArgumentException("Server type must be one of: " + String.join(", ", SERVER_TYPES));
        return type;
    }

    private static String normalizeLaunchArgs(String type, String value) {
        String arguments = value == null ? "" : value.trim();
        if (arguments.isEmpty() || arguments.equalsIgnoreCase("auto")) {
            return "auto";
        }
        if (List.of("forge", "neoforge").contains(type)) {
            List<String> parsed = parseArguments(arguments);
            for (int i = 0; i + 1 < parsed.size(); i++) {
                if (parsed.get(i).equals("-jar") && parsed.get(i + 1).equalsIgnoreCase("server.jar")) {
                    return "auto";
                }
            }
        }
        return arguments;
    }

    private static Path resolve(Path root, String value) {
        if (value == null || value.isBlank()) throw new IllegalArgumentException("A server jar path is missing in config/hybrid.properties.");
        Path path = Path.of(value.trim());
        return (path.isAbsolute() ? path : root.resolve(path)).normalize();
    }

    private static Path resolveOptional(Path root, String value) {
        if (value == null || value.isBlank() || value.trim().equalsIgnoreCase("none")) return null;
        return resolve(root, value);
    }

    private static List<GameServer> loadGameServers(Path root, Properties config, String lobbyType, int lobbyPort) throws IOException {
        String lobbyLaunchArgs = normalizeLaunchArgs(lobbyType, config.getProperty("lobby.launch-args", "auto"));
        List<GameServer> servers = new ArrayList<>();
        Path lobbyJar = resolveOptional(root, config.getProperty("lobby.jar"));
        servers.add(new GameServer("lobby", lobbyType, lobbyJar,
                config.getProperty("lobby.java", "java"), config.getProperty("lobby.memory", "4G"),
                lobbyPort, root.resolve("run/lobby"), lobbyLaunchArgs,
                resolveMinecraftVersion(config.getProperty("lobby.minecraft-version"), lobbyJar,
                        root.resolve("run/lobby"), lobbyType),
                resolveOptional(root, config.getProperty("lobby.libs"))));
        validateJarLaunchArgument("lobby", servers.getFirst());
        String configuredNames = config.getProperty("plugin-servers", "");
        List<String> names = configuredNames.isBlank() ? List.of() : List.of(configuredNames.split(","));
        int nextPort = lobbyPort + 1;
        for (String configuredName : names) {
            String name = configuredName.trim().toLowerCase(Locale.ROOT);
            if (!name.matches("[a-z0-9_-]+") || name.equals("lobby") || name.equals("proxy")) {
                throw new IllegalArgumentException("Invalid plugin server name '" + configuredName.trim() + "'. Use letters, numbers, '_' or '-', and do not use lobby or proxy.");
            }
            if (servers.stream().anyMatch(server -> server.name().equals(name))) {
                throw new IllegalArgumentException("Duplicate game server name in plugin-servers: " + name);
            }
            String prefix = "plugin." + name + ".";
            String type = normalizeLobby(config.getProperty(prefix + "type", "paper"));
            int port = Integer.parseInt(config.getProperty(prefix + "port", Integer.toString(nextPort)));
            Path jar = resolveOptional(root, config.getProperty(prefix + "jar", "server-libs/" + name + ".jar"));
            GameServer server = new GameServer(name, type,
                    jar,
                    config.getProperty(prefix + "java", config.getProperty("lobby.java", "java")),
                    config.getProperty(prefix + "memory", "2G"), port, root.resolve("run").resolve(name),
                    normalizeLaunchArgs(type, config.getProperty(prefix + "launch-args", "auto")),
                    resolveMinecraftVersion(config.getProperty(prefix + "minecraft-version"), jar,
                            root.resolve("run").resolve(name), type),
                    resolveOptional(root, config.getProperty(prefix + "libs")));
            validateJarLaunchArgument(name, server);
            servers.add(server);
            nextPort = port + 1;
        }
        return List.copyOf(servers);
    }

    private static String resolveMinecraftVersion(String configured, Path jar, Path serverDirectory, String type)
            throws IOException {
        String installed = detectInstalledMinecraftVersion(serverDirectory, type);
        String declared = configured != null && !configured.isBlank()
                ? normalizeMinecraftVersion(configured.trim())
                : jar == null ? null : detectMinecraftVersion(jar);
        if (installed != null && declared != null && !installed.equals(declared)) {
            throw new IllegalArgumentException("Configured/detected Minecraft version " + declared
                    + " does not match the installed " + title(type) + " server version " + installed
                    + " in " + serverDirectory + ". Set " + (serverDirectory.endsWith("lobby")
                    ? "lobby.minecraft-version" : "plugin.<name>.minecraft-version")
                    + "=" + installed + ", or install a matching server build.");
        }
        return installed != null ? installed : declared;
    }

    private static String detectInstalledMinecraftVersion(Path serverDirectory, String type) throws IOException {
        if (!List.of("forge", "neoforge").contains(type)) return null;
        Path serverLibraries = serverDirectory.resolve("libraries/net/minecraft/server");
        if (!Files.isDirectory(serverLibraries)) return null;
        Pattern versionedServer = Pattern.compile("^(1\\.\\d+(?:\\.\\d+)?|26\\.\\d+(?:\\.\\d+)?)-");
        List<String> versions = new ArrayList<>();
        try (Stream<Path> paths = Files.list(serverLibraries)) {
            for (Path versionDirectory : paths.filter(Files::isDirectory).toList()) {
                Matcher version = versionedServer.matcher(versionDirectory.getFileName().toString());
                if (!version.find()) continue;
                try (Stream<Path> artifacts = Files.list(versionDirectory)) {
                    if (artifacts.anyMatch(path -> Files.isRegularFile(path)
                            && path.getFileName().toString().startsWith("server-" + version.group(1) + "-")
                            && path.getFileName().toString().endsWith(".jar"))) {
                        versions.add(normalizeMinecraftVersion(version.group(1)));
                    }
                }
            }
        }
        List<String> detected = versions.stream().distinct().toList();
        if (detected.size() > 1) {
            throw new IllegalStateException("Multiple installed Minecraft versions were found for " + title(type)
                    + " in " + serverLibraries + ": " + String.join(", ", detected)
                    + ". Keep one installation or configure a separate run directory per version.");
        }
        return detected.isEmpty() ? null : detected.getFirst();
    }

    private static String normalizeMinecraftVersion(String version) {
        if (!version.matches("(?:1\\.\\d+(?:\\.\\d+)?|\\d+\\.\\d+(?:\\.\\d+)?)")) {
            throw new IllegalArgumentException("Invalid Minecraft version: " + version);
        }
        return version.matches("1\\.\\d+\\.0") ? version.substring(0, version.length() - 2) : version;
    }

    private static String detectMinecraftVersion(Path jar) throws IOException {
        Matcher filename = Pattern.compile("(?<!\\d)(1\\.\\d+(?:\\.\\d+)?|26\\.\\d+(?:\\.\\d+)?)(?!\\d)")
                .matcher(jar.getFileName().toString());
        if (filename.find()) return normalizeMinecraftVersion(filename.group(1));
        if (!Files.isRegularFile(jar)) return null;
        try (JarFile archive = new JarFile(jar.toFile())) {
            var entries = archive.entries();
            while (entries.hasMoreElements()) {
                String name = entries.nextElement().getName();
                Matcher bundledServer = Pattern.compile("(?:^|/)server-(1\\.\\d+(?:\\.\\d+)?|26\\.\\d+(?:\\.\\d+)?)\\.jar$")
                        .matcher(name);
                if (bundledServer.find()) return normalizeMinecraftVersion(bundledServer.group(1));
                if (name.equals("version.json") || name.endsWith("/version.json")) {
                    try (InputStream input = archive.getInputStream(archive.getJarEntry(name))) {
                        String json = new String(input.readAllBytes(), StandardCharsets.UTF_8);
                        Matcher id = Pattern.compile("\"id\"\\s*:\\s*\"(1\\.\\d+(?:\\.\\d+)?|26\\.\\d+(?:\\.\\d+)?)\"").matcher(json);
                        if (id.find()) return normalizeMinecraftVersion(id.group(1));
                    }
                }
            }
        }
        return null;
    }

    private static void installModrinthProject(String projectId, String loader, GameServer server, String managedName)
            throws IOException, InterruptedException {
        String minecraftVersion = requireMinecraftVersion(server);
        Path mods = server.directory().resolve("mods");
        Files.createDirectories(mods);
        Path marker = mods.resolve(".hybrid-" + managedName + ".properties");
        Properties previous = new Properties();
        if (Files.isRegularFile(marker)) {
            try (InputStream input = Files.newInputStream(marker)) {
                previous.load(input);
            }
            String oldFile = previous.getProperty("file");
            String oldHash = previous.getProperty("sha512");
            if (minecraftVersion.equals(previous.getProperty("minecraft-version"))
                    && oldFile != null && oldHash != null && isSafeJarName(oldFile)
                    && Files.isRegularFile(mods.resolve(oldFile))
                    && oldHash.equalsIgnoreCase(sha512(mods.resolve(oldFile)))
                    && (!managedName.equals("neovelocity")
                    || isNeoVelocityCompatible(mods.resolve(oldFile), minecraftVersion))) {
                return;
            }
        }

        List<String> candidates = fetchModrinthVersions(projectId, minecraftVersion, loader);
        ModrinthArtifact artifact = selectModrinthArtifact(candidates, minecraftVersion, loader, managedName);
        Path destination = mods.resolve(artifact.filename());
        String oldFile = previous.getProperty("file");
        String filePrefix = managedFilePrefix(managedName);
        try (Stream<Path> entries = Files.list(mods)) {
            boolean unmanagedConflict = entries.filter(Files::isRegularFile)
                    .map(path -> path.getFileName().toString())
                    .anyMatch(filename -> filename.toLowerCase(Locale.ROOT).startsWith(filePrefix)
                            && !filename.equals(oldFile));
            if (unmanagedConflict) {
                throw new IllegalStateException("A manually installed " + managedName + " JAR exists in " + mods
                        + ". Remove or update it manually before enabling automatic installation; the launcher will not overwrite user files.");
            }
        }
        if (Files.isRegularFile(destination) && sha512(destination).equalsIgnoreCase(artifact.sha512())) {
            if (managedName.equals("neovelocity") && !isNeoVelocityCompatible(destination, minecraftVersion)) {
                throw new UnsupportedModReleaseException("NeoVelocity release " + artifact.filename()
                        + " is tagged for Minecraft " + minecraftVersion + " but its embedded NeoForge metadata "
                        + "does not declare that Minecraft version as supported.");
            }
            writeModrinthMarker(marker, minecraftVersion, artifact);
            return;
        }
        Path temporary = Files.createTempFile(mods, ".hybrid-download-", ".tmp");
        try {
            HttpRequest request = HttpRequest.newBuilder(URI.create(artifact.url()))
                    .timeout(Duration.ofSeconds(60))
                    .header("User-Agent", "HybridServerLauncher/1.0 (automatic compatible mod installer)")
                    .GET().build();
            HttpResponse<byte[]> response = HTTP_CLIENT.send(request, HttpResponse.BodyHandlers.ofByteArray());
            if (response.statusCode() < 200 || response.statusCode() >= 300) {
                throw new IOException("Modrinth file download failed with HTTP " + response.statusCode() + ": " + artifact.url());
            }
            byte[] data = response.body();
            if (data.length > 128 * 1024 * 1024) {
                throw new IOException("Refusing to install unexpectedly large mod file: " + artifact.filename());
            }
            String actualHash = sha512(data);
            if (!actualHash.equalsIgnoreCase(artifact.sha512())) {
                throw new IOException("SHA-512 verification failed for downloaded mod " + artifact.filename());
            }
            Files.write(temporary, data);
            if (managedName.equals("neovelocity") && !isNeoVelocityCompatible(temporary, minecraftVersion)) {
                throw new UnsupportedModReleaseException("NeoVelocity release " + artifact.filename()
                        + " is tagged for Minecraft " + minecraftVersion + " but its embedded NeoForge metadata "
                        + "does not declare that Minecraft version as supported.");
            }
            try {
                Files.move(temporary, destination, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
            } catch (java.nio.file.AtomicMoveNotSupportedException unsupported) {
                Files.move(temporary, destination, StandardCopyOption.REPLACE_EXISTING);
            }
            writeModrinthMarker(marker, minecraftVersion, artifact);
            if (oldFile != null && isSafeJarName(oldFile) && !oldFile.equals(artifact.filename())) {
                Files.deleteIfExists(mods.resolve(oldFile));
            }
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    private static List<String> fetchModrinthVersions(String projectId, String minecraftVersion, String loader)
            throws IOException, InterruptedException {
        String gameVersions = URLEncoder.encode("[\"" + minecraftVersion + "\"]", StandardCharsets.UTF_8);
        String loaders = URLEncoder.encode("[\"" + loader + "\"]", StandardCharsets.UTF_8);
        URI uri = URI.create("https://api.modrinth.com/v2/project/" + projectId
                + "/version?game_versions=" + gameVersions + "&loaders=" + loaders + "&version_type=release");
        HttpRequest request = HttpRequest.newBuilder(uri).timeout(Duration.ofSeconds(20))
                .header("User-Agent", "HybridServerLauncher/1.0 (automatic compatible mod installer)")
                .GET().build();
        HttpResponse<String> response = HTTP_CLIENT.send(request, HttpResponse.BodyHandlers.ofString(StandardCharsets.UTF_8));
        if (response.statusCode() != 200) {
            throw new IOException("Modrinth version lookup failed with HTTP " + response.statusCode() + " for "
                    + loader + " Minecraft " + minecraftVersion + ".");
        }
        return extractJsonObjects(response.body());
    }

    private static ModrinthArtifact selectModrinthArtifact(List<String> versions, String minecraftVersion,
                                                           String loader, String managedName) {
        for (String version : versions) {
            List<String> gameVersions = jsonStringArray(version, "game_versions");
            List<String> loaders = jsonStringArray(version, "loaders");
            if (!gameVersions.contains(minecraftVersion) || !loaders.contains(loader)) continue;
            List<String> files = jsonObjectArray(version, "files");
            files.sort((first, second) -> Boolean.compare(
                    Boolean.parseBoolean(jsonBooleanField(second, "primary")),
                    Boolean.parseBoolean(jsonBooleanField(first, "primary"))));
            for (String file : files) {
                String filename = jsonStringField(file, "filename");
                String url = jsonStringField(file, "url");
                String hash = jsonStringField(jsonObjectField(file, "hashes"), "sha512");
                String scheme = url == null ? null : URI.create(url).getScheme();
                if (filename == null || !filename.toLowerCase(Locale.ROOT).endsWith(".jar")
                        || !isSafeJarName(filename) || !"https".equalsIgnoreCase(scheme)
                        || hash == null || !hash.matches("(?i)[0-9a-f]{128}")) {
                    continue;
                }
                return new ModrinthArtifact(filename, url, hash, jsonStringField(version, "id"));
            }
        }
        throw new UnsupportedModReleaseException("No verified release of " + managedName + " is available for " + loader
                + " Minecraft " + minecraftVersion + ". Check the mod's published version support; the launcher's "
                + "general Minecraft range does not imply that every loader mod supports every version.");
    }

    private static List<String> extractJsonObjects(String json) {
        List<String> objects = new ArrayList<>();
        int depth = 0;
        int start = -1;
        boolean inString = false;
        boolean escaped = false;
        for (int i = 0; i < json.length(); i++) {
            char current = json.charAt(i);
            if (inString) {
                if (escaped) escaped = false;
                else if (current == '\\') escaped = true;
                else if (current == '"') inString = false;
                continue;
            }
            if (current == '"') inString = true;
            else if (current == '{') {
                if (depth++ == 0) start = i;
            } else if (current == '}' && depth > 0 && --depth == 0 && start >= 0) {
                objects.add(json.substring(start, i + 1));
            }
        }
        return objects;
    }

    private static List<String> jsonStringArray(String json, String key) {
        int start = json.indexOf("\"" + key + "\"");
        if (start < 0) return List.of();
        start = json.indexOf('[', start);
        if (start < 0) return List.of();
        int end = json.indexOf(']', start);
        if (end < 0) return List.of();
        Matcher matcher = Pattern.compile("\"((?:\\\\.|[^\"\\\\])*)\"").matcher(json.substring(start + 1, end));
        List<String> values = new ArrayList<>();
        while (matcher.find()) values.add(unescapeJson(matcher.group(1)));
        return values;
    }

    private static List<String> jsonObjectArray(String json, String key) {
        int start = json.indexOf("\"" + key + "\"");
        if (start < 0) return List.of();
        start = json.indexOf('[', start);
        if (start < 0) return List.of();
        int end = matchingJsonEnd(json, start, '[', ']');
        return end < 0 ? List.of() : extractJsonObjects(json.substring(start + 1, end));
    }

    private static String jsonObjectField(String json, String key) {
        int start = json.indexOf("\"" + key + "\"");
        if (start < 0) return null;
        start = json.indexOf('{', start);
        if (start < 0) return null;
        int end = matchingJsonEnd(json, start, '{', '}');
        return end < 0 ? null : json.substring(start, end + 1);
    }

    private static String jsonStringField(String json, String key) {
        Matcher matcher = Pattern.compile("\"" + Pattern.quote(key) + "\"\\s*:\\s*\"((?:\\\\.|[^\"\\\\])*)\"")
                .matcher(json);
        return matcher.find() ? unescapeJson(matcher.group(1)) : null;
    }

    private static String jsonBooleanField(String json, String key) {
        Matcher matcher = Pattern.compile("\"" + Pattern.quote(key) + "\"\\s*:\\s*(true|false)")
                .matcher(json);
        return matcher.find() ? matcher.group(1) : null;
    }

    private static int matchingJsonEnd(String json, int start, char opening, char closing) {
        int depth = 0;
        boolean inString = false;
        boolean escaped = false;
        for (int i = start; i < json.length(); i++) {
            char current = json.charAt(i);
            if (inString) {
                if (escaped) escaped = false;
                else if (current == '\\') escaped = true;
                else if (current == '"') inString = false;
                continue;
            }
            if (current == '"') inString = true;
            else if (current == opening) depth++;
            else if (current == closing && --depth == 0) return i;
        }
        return -1;
    }

    private static String unescapeJson(String value) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < value.length(); i++) {
            char current = value.charAt(i);
            if (current != '\\' || i + 1 >= value.length()) {
                result.append(current);
                continue;
            }
            char escaped = value.charAt(++i);
            switch (escaped) {
                case '"', '\\', '/' -> result.append(escaped);
                case 'b' -> result.append('\b');
                case 'f' -> result.append('\f');
                case 'n' -> result.append('\n');
                case 'r' -> result.append('\r');
                case 't' -> result.append('\t');
                case 'u' -> {
                    if (i + 4 >= value.length()) throw new IllegalArgumentException("Invalid JSON unicode escape.");
                    result.append((char) Integer.parseInt(value.substring(i + 1, i + 5), 16));
                    i += 4;
                }
                default -> throw new IllegalArgumentException("Invalid JSON escape sequence.");
            }
        }
        return result.toString();
    }

    private static boolean isSafeJarName(String filename) {
        return filename.matches("[A-Za-z0-9._+-]+\\.jar");
    }

    private static String sha512(Path path) throws IOException {
        try (InputStream input = Files.newInputStream(path)) {
            MessageDigest digest = MessageDigest.getInstance("SHA-512");
            byte[] buffer = new byte[8192];
            int read;
            while ((read = input.read(buffer)) != -1) digest.update(buffer, 0, read);
            return HexFormat.of().formatHex(digest.digest());
        } catch (java.security.NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-512 is unavailable in this Java runtime.", impossible);
        }
    }

    private static String sha512(byte[] data) {
        try {
            return HexFormat.of().formatHex(MessageDigest.getInstance("SHA-512").digest(data));
        } catch (java.security.NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-512 is unavailable in this Java runtime.", impossible);
        }
    }

    private static String requireMinecraftVersion(GameServer server) {
        if (server.minecraftVersion() == null) {
            throw new IllegalStateException("Set " + (server.name().equals("lobby") ? "lobby" : "plugin." + server.name())
                    + ".minecraft-version in config/hybrid.properties so the launcher can select an exact compatible forwarding mod.");
        }
        return server.minecraftVersion();
    }

    private static void requireSupportedForgeModernVersion(GameServer server) {
        String version = requireMinecraftVersion(server);
        if (compareVersions(version, "1.13") < 0) {
            throw new IllegalStateException("Automatic Proxy Compatible Forge setup for Forge " + version
                    + " is unavailable with the standard Velocity launcher: these older Forge versions require a modified Velocity proxy. "
                    + "Use a compatible manually configured proxy/mod, or select a supported Forge version.");
        }
    }

    private static int compareVersions(String first, String second) {
        String[] left = first.split("\\.");
        String[] right = second.split("\\.");
        for (int i = 0; i < Math.max(left.length, right.length); i++) {
            int a = i < left.length ? Integer.parseInt(left[i]) : 0;
            int b = i < right.length ? Integer.parseInt(right[i]) : 0;
            if (a != b) return Integer.compare(a, b);
        }
        return 0;
    }

    private static void installFabricProxyLite(GameServer server) throws IOException, InterruptedException {
        installModrinthProject(FABRIC_PROXY_LITE_PROJECT, "fabric", server, "fabricproxy-lite");
        installModrinthProject(FABRIC_API_PROJECT, "fabric", server, "fabric-api");
    }

    private static void configureFabricProxyLite(Path serverDir, String secret) throws IOException {
        Path config = serverDir.resolve("config/FabricProxy-Lite.toml");
        Files.createDirectories(config.getParent());
        ensureTomlRootKey(config, "secret", "\"" + escapeToml(secret) + "\"",
                "hackOnlineMode = true\nhackEarlySend = false\nhackMessageChain = false\n"
                        + "disconnectMessage = \"This server requires you to connect with Velocity.\"\n");
    }

    private static void configureNeoVelocity(Path serverDir, String secret) throws IOException {
        Path config = serverDir.resolve("config/neovelocity-common.toml");
        Files.createDirectories(config.getParent());
        ensureTomlSectionKey(config, "forwarding", "forwarding-secret", "\"" + escapeToml(secret) + "\"",
                "[forwarding]\nforwarding-secret-type = \"IN_LINE\"\n");
        ensureTomlSectionKey(config, "forwarding", "forwarding-secret-type", "\"IN_LINE\"", "[forwarding]\n");
    }

    private static void installNeoForgeForwarding(GameServer server, String secret)
            throws IOException, InterruptedException {
        try {
            installModrinthProject("RT18TcxA", "neoforge", server, "neovelocity");
            configureNeoVelocity(server.directory(), secret);
            removeManagedMod(server.directory(), "proxy-compatible-forge");
        } catch (UnsupportedModReleaseException noNeoVelocityRelease) {
            System.out.println("No NeoVelocity release with embedded metadata compatible with Minecraft "
                    + requireMinecraftVersion(server) + "; trying Proxy Compatible Forge.");
            try {
                installModrinthProject("vDyrHl8l", "neoforge", server, "proxy-compatible-forge");
                validateProxyCompatibleForgeCompatibility(
                        server.directory().resolve("mods")
                                .resolve(managedModFile(server.directory(), "proxy-compatible-forge")),
                        requireMinecraftVersion(server));
            } catch (UnsupportedModReleaseException noPcfRelease) {
                noPcfRelease.addSuppressed(noNeoVelocityRelease);
                throw noPcfRelease;
            }
            configureProxyCompatibleForge(server.directory(), secret);
            removeManagedMod(server.directory(), "neovelocity");
        }
    }

    private static String managedModFile(Path serverDir, String managedName) throws IOException {
        Path marker = serverDir.resolve("mods/.hybrid-" + managedName + ".properties");
        if (!Files.isRegularFile(marker)) {
            throw new IllegalStateException("Managed mod marker is missing: " + marker);
        }
        Properties properties = new Properties();
        try (InputStream input = Files.newInputStream(marker)) {
            properties.load(input);
        }
        String file = properties.getProperty("file");
        if (file == null || !isSafeJarName(file)) {
            throw new IllegalStateException("Managed mod marker has an invalid JAR filename: " + marker);
        }
        return file;
    }

    private static void validateProxyCompatibleForgeCompatibility(Path jar, String minecraftVersion)
            throws IOException {
        try (JarFile archive = new JarFile(jar.toFile())) {
            var entry = archive.getJarEntry("META-INF/neoforge.mods.toml");
            if (entry == null) return;
            String metadata;
            try (InputStream input = archive.getInputStream(entry)) {
                metadata = new String(input.readAllBytes(), StandardCharsets.UTF_8);
            }
            Matcher dependency = Pattern.compile(
                    "(?ms)^\\[\\[dependencies\\.pcf]]\\s*(.*?)(?=^\\[\\[|\\z)")
                    .matcher(metadata);
            while (dependency.find()) {
                String block = dependency.group(1);
                Matcher modId = Pattern.compile("(?m)^\\s*modId\\s*=\\s*\"minecraft\"\\s*$").matcher(block);
                Matcher range = Pattern.compile("(?m)^\\s*versionRange\\s*=\\s*\"([^\"]+)\"\\s*$").matcher(block);
                if (!modId.find() || !range.find()) continue;
                if (!isMinecraftVersionInRange(minecraftVersion, range.group(1))) {
                    throw new UnsupportedModReleaseException("Proxy Compatible Forge " + jar.getFileName()
                            + " does not support installed Minecraft " + minecraftVersion
                            + "; its embedded NeoForge metadata requires Minecraft " + range.group(1) + ".");
                }
                return;
            }
        } catch (java.util.zip.ZipException corruptJar) {
            throw new IOException("Downloaded Proxy Compatible Forge is not a valid JAR: " + jar, corruptJar);
        }
    }

    private static boolean isNeoVelocityCompatible(Path jar, String minecraftVersion) throws IOException {
        String metadata;
        try (JarFile archive = new JarFile(jar.toFile())) {
            var entry = archive.getJarEntry("META-INF/neoforge.mods.toml");
            if (entry == null) return false;
            try (InputStream input = archive.getInputStream(entry)) {
                metadata = new String(input.readAllBytes(), StandardCharsets.UTF_8);
            }
        } catch (java.util.zip.ZipException corruptJar) {
            return false;
        }

        Matcher dependency = Pattern.compile(
                "(?ms)^\\[\\[dependencies\\.neovelocity]]\\s*(.*?)(?=^\\[\\[|\\z)")
                .matcher(metadata);
        while (dependency.find()) {
            String block = dependency.group(1);
            Matcher modId = Pattern.compile("(?m)^\\s*modId\\s*=\\s*\"minecraft\"\\s*$").matcher(block);
            Matcher range = Pattern.compile("(?m)^\\s*versionRange\\s*=\\s*\"([^\"]+)\"\\s*$").matcher(block);
            if (modId.find() && range.find()) return isMinecraftVersionInRange(minecraftVersion, range.group(1));
        }
        return false;
    }

    private static boolean isMinecraftVersionInRange(String version, String range) {
        String normalized = range.trim();
        if (normalized.length() < 2
                || !((normalized.charAt(0) == '[' || normalized.charAt(0) == '(')
                && (normalized.charAt(normalized.length() - 1) == ']' || normalized.charAt(normalized.length() - 1) == ')'))) {
            return compareVersions(version, normalized) == 0;
        }
        String[] bounds = normalized.substring(1, normalized.length() - 1).split(",", -1);
        if (bounds.length != 2) return false;
        String lower = bounds[0].trim();
        String upper = bounds[1].trim();
        if (!lower.isEmpty()) {
            int comparison = compareVersions(version, lower);
            if (comparison < 0 || (comparison == 0 && normalized.charAt(0) == '(')) return false;
        }
        if (!upper.isEmpty()) {
            int comparison = compareVersions(version, upper);
            if (comparison > 0 || (comparison == 0 && normalized.charAt(normalized.length() - 1) == ')')) return false;
        }
        return true;
    }

    private static void removeManagedMod(Path serverDir, String managedName) throws IOException {
        Path mods = serverDir.resolve("mods");
        Path marker = mods.resolve(".hybrid-" + managedName + ".properties");
        if (!Files.isRegularFile(marker)) return;
        Properties installed = new Properties();
        try (InputStream input = Files.newInputStream(marker)) {
            installed.load(input);
        }
        String filename = installed.getProperty("file");
        String expectedHash = installed.getProperty("sha512");
        if (filename != null && expectedHash != null && isSafeJarName(filename)) {
            Path jar = mods.resolve(filename);
            if (Files.isRegularFile(jar) && expectedHash.equalsIgnoreCase(sha512(jar))) {
                Files.delete(jar);
            }
        }
        Files.delete(marker);
    }

    private static boolean isManagedModInstalled(Path serverDir, String managedName) throws IOException {
        Path mods = serverDir.resolve("mods");
        Path marker = mods.resolve(".hybrid-" + managedName + ".properties");
        if (!Files.isRegularFile(marker)) return false;
        Properties installed = new Properties();
        try (InputStream input = Files.newInputStream(marker)) {
            installed.load(input);
        }
        String filename = installed.getProperty("file");
        String expectedHash = installed.getProperty("sha512");
        if (filename == null || expectedHash == null || !isSafeJarName(filename)) return false;
        Path jar = mods.resolve(filename);
        return Files.isRegularFile(jar) && expectedHash.equalsIgnoreCase(sha512(jar));
    }

    private static void validateProxyCompatibleForge(Path serverDir, String secret) throws IOException {
        Path config = serverDir.resolve("config/proxy-compatible-forge.toml");
        if (!secret.equals(readTomlSectionValue(config, "forwarding", "secret"))
                || !"true".equalsIgnoreCase(readTomlSectionValue(config, "forwarding", "enabled"))
                || !"MODERN".equalsIgnoreCase(readTomlSectionValue(config, "forwarding", "mode"))) {
            throw new IllegalStateException("Proxy Compatible Forge forwarding must use the Velocity secret in MODERN mode.");
        }
    }

    private static void configureProxyCompatibleForge(Path serverDir, String secret) throws IOException {
        Path config = serverDir.resolve("config/proxy-compatible-forge.toml");
        Files.createDirectories(config.getParent());
        ensureTomlSectionKey(config, "forwarding", "secret", "\"" + escapeToml(secret) + "\"",
                "version = 2.0\n\n[forwarding]\nenabled = true\nmode = \"MODERN\"\napprovedProxyHosts = []\n");
        ensureTomlSectionKey(config, "forwarding", "enabled", "true", "[forwarding]\n");
        ensureTomlSectionKey(config, "forwarding", "mode", "\"MODERN\"", "[forwarding]\n");
    }

    private static void ensureTomlRootKey(Path path, String key, String value, String defaults) throws IOException {
        List<String> lines = Files.exists(path) ? Files.readAllLines(path, StandardCharsets.UTF_8) : new ArrayList<>();
        if (lines.isEmpty() && !defaults.isEmpty()) lines.addAll(List.of(defaults.stripTrailing().split("\\R")));
        boolean found = false;
        for (int i = 0; i < lines.size(); i++) {
            String trimmed = lines.get(i).trim();
            if (!trimmed.startsWith("[") && tomlKey(trimmed).equals(key)) {
                lines.set(i, key + " = " + value);
                found = true;
            }
        }
        if (!found) lines.add(key + " = " + value);
        Files.write(path, lines, StandardCharsets.UTF_8);
    }

    private static void ensureTomlSectionKey(Path path, String sectionName, String key, String value, String defaults)
            throws IOException {
        List<String> lines = Files.exists(path) ? Files.readAllLines(path, StandardCharsets.UTF_8) : new ArrayList<>();
        if (lines.isEmpty() && !defaults.isEmpty()) lines.addAll(List.of(defaults.stripTrailing().split("\\R")));
        int section = -1;
        int end = lines.size();
        for (int i = 0; i < lines.size(); i++) {
            String trimmed = lines.get(i).trim();
            if (trimmed.equals("[" + sectionName + "]")) {
                section = i;
                end = lines.size();
            } else if (section >= 0 && trimmed.startsWith("[") && trimmed.endsWith("]")) {
                end = i;
                break;
            }
        }
        if (section < 0) {
            if (!lines.isEmpty() && !lines.getLast().isBlank()) lines.add("");
            lines.add("[" + sectionName + "]");
            section = lines.size() - 1;
            end = lines.size();
        }
        for (int i = section + 1; i < end; i++) {
            if (tomlKey(lines.get(i).trim()).equals(key)) {
                lines.set(i, key + " = " + value);
                Files.write(path, lines, StandardCharsets.UTF_8);
                return;
            }
        }
        lines.add(end, key + " = " + value);
        Files.write(path, lines, StandardCharsets.UTF_8);
    }

    private static String tomlKey(String line) {
        int equals = line.indexOf('=');
        return equals < 0 || line.startsWith("#") ? "" : line.substring(0, equals).trim();
    }

    private static String managedFilePrefix(String managedName) {
        return switch (managedName) {
            case "fabric-api" -> "fabric-api-";
            case "fabricproxy-lite" -> "fabricproxy-lite-";
            case "neovelocity" -> "neovelocity-";
            case "proxy-compatible-forge" -> "proxy-compatible-forge-";
            default -> throw new IllegalArgumentException("Unknown launcher-managed mod: " + managedName);
        };
    }

    private static void writeModrinthMarker(Path marker, String minecraftVersion, ModrinthArtifact artifact)
            throws IOException {
        Properties installed = new Properties();
        installed.setProperty("minecraft-version", minecraftVersion);
        installed.setProperty("file", artifact.filename());
        installed.setProperty("sha512", artifact.sha512());
        if (artifact.versionId() != null) installed.setProperty("modrinth-version-id", artifact.versionId());
        try (OutputStream output = Files.newOutputStream(marker)) {
            installed.store(output, "Managed by Hybrid Server");
        }
    }

    private record ModrinthArtifact(String filename, String url, String sha512, String versionId) {
    }

    private static final class UnsupportedModReleaseException extends IllegalStateException {
        private UnsupportedModReleaseException(String message) {
            super(message);
        }
    }

    private static void validateJarLaunchArgument(String name, GameServer server) {
        List<String> arguments = parseArguments(server.launchArgs());
        boolean referencesJar = false;
        for (int i = 0; i < arguments.size(); i++) {
            String argument = arguments.get(i);
            if (argument.equals("server.jar") || argument.endsWith("/server.jar")
                    || (argument.equals("-jar") && i + 1 < arguments.size()
                    && (arguments.get(i + 1).equals("server.jar") || arguments.get(i + 1).endsWith("/server.jar")))) {
                referencesJar = true;
                break;
            }
        }
        if (server.jar() == null && referencesJar) {
            throw new IllegalArgumentException("Server '" + name + "' has no JAR configured, but its launch-args reference server.jar. Set a JAR path or use launch arguments that do not require one.");
        }
    }

    private static List<String> parseArguments(String value) {
        List<String> arguments = new ArrayList<>();
        StringBuilder current = new StringBuilder();
        char quote = 0;
        boolean escaped = false;
        boolean tokenStarted = false;
        for (int i = 0; i < value.length(); i++) {
            char character = value.charAt(i);
            if (escaped) {
                current.append(character);
                escaped = false;
                tokenStarted = true;
            } else if (character == '\\' && quote != '\'') {
                if (i + 1 < value.length()) {
                    char next = value.charAt(i + 1);
                    if (Character.isWhitespace(next) || next == '"' || next == '\\') escaped = true;
                    else {
                        current.append(character);
                        tokenStarted = true;
                    }
                } else {
                    current.append(character);
                    tokenStarted = true;
                }
            } else if (quote != 0) {
                if (character == quote) quote = 0;
                else current.append(character);
                tokenStarted = true;
            } else if (character == '"' || character == '\'') {
                quote = character;
                tokenStarted = true;
            } else if (Character.isWhitespace(character)) {
                if (tokenStarted) {
                    arguments.add(current.toString());
                    current.setLength(0);
                    tokenStarted = false;
                }
            } else {
                current.append(character);
                tokenStarted = true;
            }
        }
        if (escaped) current.append('\\');
        if (quote != 0) throw new IllegalArgumentException("Unclosed quote in launch-args: " + value);
        if (tokenStarted) arguments.add(current.toString());
        if (arguments.isEmpty()) throw new IllegalArgumentException("launch-args cannot be empty.");
        return List.copyOf(arguments);
    }

    private static void validatePorts(String proxyBind, List<GameServer> servers) {
        int proxyPort = portFromBind(proxyBind);
        Map<Integer, String> ports = new LinkedHashMap<>();
        ports.put(proxyPort, "proxy");
        for (GameServer server : servers) {
            if (server.port() < 1 || server.port() > 65535) throw new IllegalArgumentException("Invalid port for game server '" + server.name() + "': " + server.port());
            String previous = ports.putIfAbsent(server.port(), server.name());
            if (previous != null) throw new IllegalArgumentException("Port " + server.port() + " is shared by '" + previous + "' and '" + server.name() + "'.");
        }
    }

    private static void prepareDirectories(Path root, Path proxyDir, List<GameServer> gameServers) throws IOException {
        Files.createDirectories(root.resolve("server-libs"));
        Files.createDirectories(root.resolve("plugins/proxy"));
        Files.createDirectories(proxyDir.resolve("plugins"));
        for (GameServer server : gameServers) {
            Files.createDirectories(server.directory().resolve("plugins"));
            Files.createDirectories(root.resolve("plugins").resolve(server.name()));
            if (server.type().equals("limbo")) continue;
            Path eula = server.directory().resolve("eula.txt");
            if (!Files.exists(eula)) Files.writeString(eula, "# Review https://aka.ms/MinecraftEULA before accepting.\neula=false\n", StandardCharsets.UTF_8);
        }
    }

    private static void requireJars(Path proxyJar, String proxyType, List<GameServer> gameServers) {
        List<String> missing = new ArrayList<>();
        if (!Files.isRegularFile(proxyJar)) missing.add(title(proxyType) + ": " + proxyJar);
        for (GameServer server : gameServers) {
            if (server.jar() != null && !Files.isRegularFile(server.jar())) missing.add(title(server.type()) + " (" + server.name() + "): " + server.jar());
            if (server.libsArchive() != null && !Files.isRegularFile(server.libsArchive())) {
                missing.add(title(server.type()) + " libraries archive (" + server.name() + "): " + server.libsArchive());
            }
            if (server.libsArchive() != null && !List.of("forge", "neoforge").contains(server.type())) {
                throw new IllegalArgumentException(server.name() + ".libs is only supported for Forge/NeoForge backends.");
            }
        }
        if (!missing.isEmpty()) throw new IllegalStateException("Setup files were created. Add the selected official server jars to these paths, then run the launcher again:\n  - " + String.join("\n  - ", missing));
    }

    private static void prepareServerLaunchFiles(GameServer server) throws IOException, InterruptedException {
        if (server.jar() == null) {
            if (List.of("forge", "neoforge").contains(server.type())) {
                installLibrariesArchive(server);
                ensureLoaderInstallationComplete(server);
            }
            return;
        }
        if (!isServerInstaller(server.jar())) {
            Files.copy(server.jar(), server.directory().resolve("server.jar"), StandardCopyOption.REPLACE_EXISTING);
            if (List.of("forge", "neoforge").contains(server.type())) {
                installLibrariesArchive(server);
                ensureLoaderInstallationComplete(server);
            }
            return;
        }

        if (!List.of("forge", "neoforge").contains(server.type())) {
            throw new IllegalStateException("The selected " + title(server.type()) + " file appears to be an installer, "
                    + "but automatic installer setup is not implemented for this software. Install it into "
                    + server.directory() + " first, then set " + server.name() + ".jar=none and launch-args=auto.");
        }
        List<Path> missing = missingLoaderLibraries(server);
        if ((findLoaderLaunchProfile(server) != null || findLegacyForgeServerJar(server) != null) && missing.isEmpty()) {
            System.out.println("Detected a complete " + title(server.type()) + " server installation for " + server.name() + "; skipping installer.");
            installLibrariesArchive(server);
            ensureLoaderInstallationComplete(server);
            return;
        }

        System.out.println((missing.isEmpty() ? "Installing " : "Repairing incomplete ")
                + title(server.type()) + " server files for " + server.name() + "...");
        Process installer = new ProcessBuilder(server.java(), "-jar", server.jar().toString(), "--installServer")
                .directory(server.directory().toFile())
                .redirectInput(ProcessBuilder.Redirect.PIPE)
                .redirectOutput(ProcessBuilder.Redirect.INHERIT)
                .redirectError(ProcessBuilder.Redirect.INHERIT)
                .start();
        boolean timedOut = !installer.waitFor(10, TimeUnit.MINUTES);
        if (timedOut) {
            installer.destroyForcibly();
            installer.waitFor(5, TimeUnit.SECONDS);
        }
        int installerExitCode = timedOut ? -1 : installer.exitValue();
        installLibrariesArchive(server);
        if (findLoaderLaunchProfile(server) == null && findLegacyForgeServerJar(server) == null) {
            String result = timedOut ? "timed out" : "failed with exit code " + installerExitCode;
            throw new IllegalStateException(title(server.type()) + " installer " + result + " for " + server.name()
                    + " and did not create a recognized server launch profile in " + server.directory()
                    + ". Check installer output and the configured libraries archive.");
        }
        if (timedOut || installerExitCode != 0) {
            System.err.println(title(server.type()) + " installer did not complete successfully ("
                    + (timedOut ? "timed out" : "exit code " + installerExitCode)
                    + "); checking whether the configured libraries archive completed the installation.");
        }
        ensureLoaderInstallationComplete(server);
    }

    private static void installLibrariesArchive(GameServer server) throws IOException {
        if (server.libsArchive() == null) return;
        if (!List.of("forge", "neoforge").contains(server.type())) {
            throw new IllegalArgumentException(server.name() + ".libs is only supported for Forge/NeoForge backends.");
        }
        if (!Files.isRegularFile(server.libsArchive())) {
            throw new IllegalStateException("Configured libraries archive does not exist: " + server.libsArchive());
        }

        Path serverRoot = server.directory().toAbsolutePath().normalize();
        int extracted = 0;
        long totalBytes = 0;
        int entries = 0;
        try (InputStream input = Files.newInputStream(server.libsArchive());
             ZipInputStream zip = new ZipInputStream(input, StandardCharsets.UTF_8)) {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                if (++entries > 100_000) {
                    throw new IOException("Libraries archive contains too many entries: " + server.libsArchive());
                }
                String name = entry.getName().replace('\\', '/');
                while (name.startsWith("./")) name = name.substring(2);
                if (name.isBlank() || name.startsWith("/") || name.matches("^[A-Za-z]:.*")) {
                    throw new IOException("Unsafe path in libraries archive: " + entry.getName());
                }
                Path relative = Path.of(name).normalize();
                if (relative.isAbsolute() || relative.startsWith("..")) {
                    throw new IOException("Unsafe path in libraries archive: " + entry.getName());
                }
                if (relative.getNameCount() > 0 && relative.getName(0).toString().equalsIgnoreCase("libraries")) {
                    relative = relative.getNameCount() == 1 ? Path.of("") : relative.subpath(1, relative.getNameCount());
                }
                if (relative.toString().isBlank()) {
                    zip.closeEntry();
                    continue;
                }
                Path destination = serverRoot.resolve("libraries").resolve(relative).normalize();
                Path librariesRoot = serverRoot.resolve("libraries").normalize();
                if (!destination.startsWith(librariesRoot)) {
                    throw new IOException("Unsafe path in libraries archive: " + entry.getName());
                }
                if (entry.isDirectory()) {
                    Files.createDirectories(destination);
                    zip.closeEntry();
                    continue;
                }

                Files.createDirectories(destination.getParent());
                Path temporary = Files.createTempFile(destination.getParent(), ".hybrid-library-", ".tmp");
                try {
                    try (OutputStream output = Files.newOutputStream(temporary)) {
                        byte[] buffer = new byte[8192];
                        int read;
                        long entryBytes = 0;
                        while ((read = zip.read(buffer)) != -1) {
                            entryBytes += read;
                            totalBytes += read;
                            if (entryBytes > 256L * 1024 * 1024 || totalBytes > 4L * 1024 * 1024 * 1024) {
                                throw new IOException("Libraries archive exceeds extraction size limits: " + server.libsArchive());
                            }
                            output.write(buffer, 0, read);
                        }
                    }
                    if (name.toLowerCase(Locale.ROOT).endsWith(".jar")) {
                        try (JarFile ignored = new JarFile(temporary.toFile())) {
                        } catch (java.util.zip.ZipException corruptJar) {
                            throw new IOException("Libraries archive contains an invalid JAR at " + name
                                    + ". Rebuild the archive from a completed installation of the exact "
                                    + "Forge/NeoForge version.", corruptJar);
                        }
                    }
                    Files.move(temporary, destination, StandardCopyOption.REPLACE_EXISTING);
                    extracted++;
                } finally {
                    Files.deleteIfExists(temporary);
                }
                zip.closeEntry();
            }
        }
        System.out.printf("Installed %d library files from %s for %s.%n",
                extracted, server.libsArchive(), server.name());
    }

    private static void ensureLoaderInstallationComplete(GameServer server) throws IOException {
        Path serverJar = server.directory().resolve("server.jar");
        if (List.of("forge", "neoforge").contains(server.type())
                && Files.isRegularFile(serverJar) && isForgeBootstrapJar(serverJar)
                && findLoaderLaunchProfile(server) == null && findLegacyForgeServerJar(server) == null) {
            throw new IllegalStateException("The file " + serverJar + " is a Forge/NeoForge bootstrap shim, not a complete "
                    + "server installation, and no generated unix_args.txt launch profile was found. Configure the "
                    + "matching server installer as " + (server.name().equals("lobby") ? "lobby.jar" : "plugin." + server.name() + ".jar")
                    + " and use launch-args=auto so the installer can populate libraries/, or install the server fully "
                    + "in this run directory. The launcher will not try to start the shim as a standalone server.");
        }
        List<Path> missing = missingLoaderLibraries(server);
        if (!missing.isEmpty()) {
            String installerHint = server.jar() != null && isServerInstaller(server.jar())
                    ? "The launcher retried the installer, but required files are still missing. Check installer network/download errors."
                    : "Provide the matching Forge/NeoForge server installer as the configured JAR so the launcher can repair the installation.";
            throw new IllegalStateException("Incomplete " + title(server.type()) + " installation for " + server.name()
                    + ". Missing or invalid files referenced by its launch profile:\n  - "
                    + String.join("\n  - ", missing.stream().map(Path::toString).toList()) + "\n" + installerHint);
        }
    }

    private static boolean isForgeBootstrapJar(Path jar) throws IOException {
        try (JarFile archive = new JarFile(jar.toFile())) {
            if (archive.getEntry("net/minecraftforge/bootstrap/shim/Main.class") != null
                    || archive.getEntry("net/neoforged/bootstrap/shim/Main.class") != null) {
                return true;
            }
            if (archive.getManifest() == null) return false;
            String mainClass = archive.getManifest().getMainAttributes().getValue("Main-Class");
            return "net.minecraftforge.bootstrap.shim.Main".equals(mainClass)
                    || "net.neoforged.bootstrap.shim.Main".equals(mainClass);
        }
    }

    private static List<Path> missingLoaderLibraries(GameServer server) throws IOException {
        Path profile = findLoaderLaunchProfile(server);
        if (profile != null) {
            List<Path> missing = new ArrayList<>();
            collectMissingArgfileDependencies(server.directory().resolve(profile), server.directory(), new ArrayList<>(), missing);
            return missing.stream().distinct().toList();
        }
        Path serverJar = findLegacyForgeServerJar(server);
        if (serverJar == null) {
            Path configuredServerJar = server.directory().resolve("server.jar");
            if (!Files.isRegularFile(configuredServerJar)) return List.of();
            serverJar = server.directory().relativize(configuredServerJar);
        }
        Path serverJarPath = server.directory().resolve(serverJar);
        if (!isValidJar(serverJarPath)) return List.of(displayPath(server.directory(), serverJarPath));
        try (JarFile archive = new JarFile(serverJarPath.toFile())) {
            if (archive.getManifest() == null) return List.of();
            String classPath = archive.getManifest().getMainAttributes().getValue("Class-Path");
            if (classPath == null || classPath.isBlank()) return List.of();
            List<Path> missing = new ArrayList<>();
            for (String entry : classPath.trim().split("\\s+")) {
                if (!entry.toLowerCase(Locale.ROOT).endsWith(".jar")) continue;
                Path dependency = resolveDependencyPath(server.directory(), entry);
                if (dependency != null && (!Files.isRegularFile(dependency) || !isValidJar(dependency))) {
                    missing.add(displayPath(server.directory(), dependency));
                }
            }
            return missing.stream().distinct().toList();
        }
    }

    private static void collectMissingArgfileDependencies(Path argfile, Path workingDirectory,
                                                          List<Path> visited, List<Path> missing) throws IOException {
        if (argfile == null) return;
        Path normalized = argfile.toAbsolutePath().normalize();
        if (visited.contains(normalized) || !Files.isRegularFile(normalized)) {
            if (!Files.isRegularFile(normalized)) missing.add(displayPath(workingDirectory, normalized));
            return;
        }
        visited.add(normalized);
        String contents = Files.readString(normalized, StandardCharsets.UTF_8);
        List<String> arguments = parseArguments(contents);
        for (int i = 0; i < arguments.size(); i++) {
            String token = arguments.get(i);
            if (token.startsWith("@")) {
                collectMissingArgfileDependencies(resolveDependencyPath(workingDirectory, token.substring(1)),
                        workingDirectory, visited, missing);
                continue;
            }
            if (List.of("-p", "--module-path", "--class-path", "-classpath", "-cp").contains(token)) {
                if (i + 1 < arguments.size()) {
                    collectJarPathList(arguments.get(++i), workingDirectory, missing, false);
                }
                continue;
            }
            if (token.startsWith("-DlegacyClassPath=")) {
                collectJarPathList(token.substring(token.indexOf('=') + 1), workingDirectory, missing, true);
                continue;
            }
            if (token.startsWith("--module-path=") || token.startsWith("--class-path=")) {
                collectJarPathList(token.substring(token.indexOf('=') + 1), workingDirectory, missing, false);
                continue;
            }
            if (token.startsWith("--add-opens=") || token.startsWith("--add-exports=")
                    || (token.startsWith("-") && token.contains("="))) {
                continue;
            }
            collectJarPathList(token, workingDirectory, missing, false);
        }
    }

    private static void collectJarPathList(String value, Path workingDirectory, List<Path> missing,
                                           boolean resolveBareNamesFromLibraries) throws IOException {
        for (String commaEntry : value.split(",")) {
            for (String reference : commaEntry.split(Pattern.quote(java.io.File.pathSeparator))) {
                if (!reference.toLowerCase(Locale.ROOT).endsWith(".jar")) continue;
                Path dependency = resolveDependencyPath(workingDirectory, reference);
                if (dependency == null) continue;
                if (Files.isRegularFile(dependency) && isValidJar(dependency)) continue;
                if (resolveBareNamesFromLibraries && !Path.of(reference).isAbsolute()
                        && Path.of(reference).getNameCount() == 1
                        && containsValidLibraryJar(workingDirectory.resolve("libraries"), reference)) {
                    continue;
                }
                missing.add(displayPath(workingDirectory, dependency));
            }
        }
    }

    private static boolean containsValidLibraryJar(Path libraries, String filename) throws IOException {
        if (!Files.isDirectory(libraries)) return false;
        try (Stream<Path> paths = Files.walk(libraries)) {
            for (Path path : paths.filter(Files::isRegularFile)
                    .filter(candidate -> candidate.getFileName().toString().equals(filename)).toList()) {
                if (isValidJar(path)) return true;
            }
        }
        return false;
    }

    private static Path displayPath(Path workingDirectory, Path path) {
        Path base = workingDirectory.toAbsolutePath().normalize();
        Path normalized = path.toAbsolutePath().normalize();
        return normalized.startsWith(base) ? base.relativize(normalized) : normalized;
    }

    private static boolean isValidJar(Path path) throws IOException {
        if (!Files.isRegularFile(path)) return false;
        try (JarFile ignored = new JarFile(path.toFile())) {
            return true;
        } catch (java.util.zip.ZipException corruptJar) {
            return false;
        }
    }

    private static Path resolveDependencyPath(Path workingDirectory, String reference) {
        String normalized = reference.replace('\\', '/');
        int assignment = normalized.lastIndexOf('=');
        if (assignment >= 0) normalized = normalized.substring(assignment + 1);
        while (normalized.startsWith("@")) normalized = normalized.substring(1);
        if (normalized.isBlank() || normalized.contains("://")) return null;
        Path path;
        try {
            path = Path.of(normalized);
        } catch (java.nio.file.InvalidPathException invalidPath) {
            return null;
        }
        if (path.isAbsolute()) return path.normalize();
        return workingDirectory.resolve(path).normalize();
    }

    private static boolean isServerInstaller(Path jar) throws IOException {
        if (!Files.isRegularFile(jar)) return false;
        try (JarFile archive = new JarFile(jar.toFile())) {
            if (archive.getEntry("install_profile.json") == null
                    && archive.getEntry("install_profile") == null) return false;
            var entries = archive.entries();
            while (entries.hasMoreElements()) {
                String name = entries.nextElement().getName().toLowerCase(Locale.ROOT);
                if (name.startsWith("net/minecraftforge/installer/")
                        || name.startsWith("net/neoforged/installer/")
                        || name.startsWith("net/fabricmc/installer/")) return true;
            }
        }
        return false;
    }

    private static Path findLoaderLaunchProfile(GameServer server) throws IOException {
        List<Path> roots = switch (server.type()) {
            case "forge" -> List.of(server.directory().resolve("libraries/net/minecraftforge/forge"));
            case "neoforge" -> List.of(server.directory().resolve("libraries/net/neoforged/neoforge"));
            default -> List.of();
        };
        for (Path root : roots) {
            if (!Files.isDirectory(root)) continue;
            try (Stream<Path> paths = Files.walk(root, 5)) {
                Path match = paths.filter(Files::isRegularFile)
                        .filter(path -> path.getFileName().toString().equals("unix_args.txt"))
                        .max(Comparator.comparing(Path::toString))
                        .orElse(null);
                if (match != null) return server.directory().relativize(match);
            }
        }
        if (server.type().equals("fabric")) {
            Path fabricLaunch = server.directory().resolve("fabric-server-launch.jar");
            if (Files.isRegularFile(fabricLaunch)) return server.directory().relativize(fabricLaunch);
        }
        return null;
    }

    private static Path findLegacyForgeServerJar(GameServer server) throws IOException {
        if (!server.type().equals("forge")) return null;
        try (Stream<Path> paths = Files.list(server.directory())) {
            List<Path> serverJars = paths.filter(Files::isRegularFile)
                    .filter(path -> isLegacyForgeJarName(path.getFileName().toString()))
                    .sorted(Comparator.comparing((Path path) ->
                            !path.getFileName().toString().endsWith("-server.jar"))
                            .thenComparing(Path::toString))
                    .toList();
            if (!serverJars.isEmpty()) return server.directory().relativize(serverJars.getFirst());
        }
        return null;
    }

    private static boolean isLegacyForgeJarName(String filename) {
        String normalized = filename.toLowerCase(Locale.ROOT);
        return normalized.startsWith("forge-") && normalized.endsWith(".jar")
                && !normalized.contains("-installer")
                && !normalized.contains("-sources")
                && !normalized.contains("-javadoc");
    }

    private static List<String> resolveLaunchArguments(GameServer server) throws IOException {
        if (!server.launchArgs().equalsIgnoreCase("auto")) {
            return repairLegacyForgeJarArgument(server, parseArguments(server.launchArgs()));
        }

        Path profile = findLoaderLaunchProfile(server);
        if (profile != null && server.type().equals("fabric")) {
            return List.of("-jar", profile.toString(), "nogui");
        }
        if (profile != null) {
            List<String> arguments = new ArrayList<>();
            Path userJvmArgs = server.directory().resolve("user_jvm_args.txt");
            if (Files.isRegularFile(userJvmArgs)) arguments.add("@user_jvm_args.txt");
            arguments.add("@" + profile.toString().replace('\\', '/'));
            arguments.add("nogui");
            return List.copyOf(arguments);
        }

        Path legacyForgeJar = findLegacyForgeServerJar(server);
        if (legacyForgeJar != null) {
            return repairLegacyForgeJarArgument(server, List.of("-jar", legacyForgeJar.toString(), "nogui"));
        }

        Path genericServerJar = server.directory().resolve("server.jar");
        if (Files.isRegularFile(genericServerJar)) {
            if (List.of("forge", "neoforge").contains(server.type()) && server.jar() != null
                    && isServerInstaller(server.jar())) {
                throw new IllegalStateException(title(server.type()) + " installer is still being treated as server.jar "
                        + "and no generated libraries/ launch profile exists. The installer must complete in "
                        + server.directory() + " before the server can start.");
            }
            return repairLegacyForgeJarArgument(server, List.of("-jar", "server.jar", "nogui"));
        }

        if (List.of("forge", "neoforge").contains(server.type())) {
            throw new IllegalStateException("No installed " + title(server.type()) + " launch profile was found for "
                    + server.name() + ". Provide its server installer in the configured JAR path so the launcher can "
                    + "run --installServer, or install it into " + server.directory()
                    + " and use jar=none with launch-args=auto.");
        }
        throw new IllegalStateException("No automatic launch JAR/profile was found for " + title(server.type())
                + " server '" + server.name() + "' in " + server.directory()
                + ". Set its launch-args explicitly or provide a server JAR.");
    }

    private static List<String> repairLegacyForgeJarArgument(GameServer server, List<String> arguments)
            throws IOException {
        if (!server.type().equals("forge")) return arguments;
        List<String> repaired = new ArrayList<>(arguments);
        for (int i = 0; i + 1 < repaired.size(); i++) {
            if (!repaired.get(i).equals("-jar")) continue;
            Path target = resolveDependencyPath(server.directory(), repaired.get(i + 1));
            if (target == null || (Files.isRegularFile(target) && isValidJar(target))) continue;

            Path forgeLibraries = server.directory().resolve("libraries/net/minecraftforge/forge");
            String filename;
            try {
                filename = Path.of(repaired.get(i + 1)).getFileName().toString();
            } catch (java.nio.file.InvalidPathException invalidPath) {
                throw new IllegalStateException("Invalid Forge -jar path: " + repaired.get(i + 1), invalidPath);
            }
            List<Path> candidates = new ArrayList<>();
            if (Files.isDirectory(forgeLibraries)) {
                try (Stream<Path> paths = Files.walk(forgeLibraries, 5)) {
                    for (Path path : paths.filter(Files::isRegularFile)
                            .filter(path -> path.getFileName().toString().equals(filename)).toList()) {
                        if (isValidJar(path)) candidates.add(path);
                    }
                }
            }
            if (candidates.size() != 1) {
                String reason = candidates.isEmpty()
                        ? "No matching valid Forge JAR was found under " + forgeLibraries + "."
                        : "Multiple matching Forge JARs were found; cannot safely choose one: "
                                + String.join(", ", candidates.stream().map(Path::toString).toList());
                throw new IllegalStateException("Forge launch JAR does not exist or is invalid: " + target
                        + ". " + reason + " Check the libraries ZIP paths and use the exact Forge build.");
            }
            String correctedPath = server.directory().relativize(candidates.getFirst())
                    .toString().replace('\\', '/');
            System.out.printf("Corrected missing Forge JAR path for %s: %s -> %s%n",
                    server.name(), repaired.get(i + 1), correctedPath);
            repaired.set(i + 1, correctedPath);
        }
        return List.copyOf(repaired);
    }

    private static void requireJava(String executable, String software) throws IOException, InterruptedException {
        Process process;
        try {
            process = new ProcessBuilder(executable, "-version").redirectErrorStream(true).start();
        } catch (IOException failure) {
            throw new IllegalStateException("Cannot start the configured Java executable '" + executable
                    + "' for " + title(software) + ". Set " + software
                    + ".java to an installed Java executable (for example, 'java' if it is on PATH, or the real "
                    + "path supplied by the host). Do not use an example placeholder path.", failure);
        }
        String output = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        if (!process.waitFor(10, TimeUnit.SECONDS)) {
            process.destroyForcibly();
            throw new IllegalStateException("Timed out checking Java executable: " + executable);
        }
        Matcher matcher = JAVA_MAJOR.matcher(output);
        if (process.exitValue() != 0 || !matcher.find()) throw new IllegalStateException("Cannot read Java version from " + executable + ": " + output);
        int major = Integer.parseInt(matcher.group(1));
        if (major < 8) throw new IllegalStateException(title(software) + " requires Java 8 or newer, but "
                + executable + " is Java " + major + ". Select a runtime compatible with this server build.");
    }

    private static void requireEulaAccepted(Path path) throws IOException {
        if (!Files.readAllLines(path, StandardCharsets.UTF_8).stream().map(String::trim).anyMatch(line -> line.equalsIgnoreCase("eula=true"))) {
            throw new IllegalStateException("Review Mojang's EULA, then set eula=true in " + path + " and start again.");
        }
    }

    private static void configureLobby(Path dir, String type, String minecraftVersion, int port, String proxyType,
                                       boolean onlineMode, String secret, String velocityMode) throws IOException {
        if (type.equals("limbo")) {
            configureLimbo(dir, port, proxyType, secret, velocityMode);
            return;
        }
        Path serverProperties = dir.resolve("server.properties");
        Properties properties = new Properties();
        if (Files.exists(serverProperties)) {
            try (InputStream input = Files.newInputStream(serverProperties)) { properties.load(input); }
        }
        properties.setProperty("server-ip", "127.0.0.1");
        properties.setProperty("server-port", Integer.toString(port));
        properties.setProperty("online-mode", "false");
        try (OutputStream output = Files.newOutputStream(serverProperties)) {
            properties.store(output, "Managed by Hybrid Server. Backend is private behind its proxy.");
        }

        if (!BUKKIT_TYPES.contains(type)) return;
        Path spigotConfig = dir.resolve("spigot.yml");
        boolean legacyForwarding = !proxyType.equals("velocity") || velocityMode.equals("legacy");
        if (!Files.exists(spigotConfig)) {
            Files.writeString(spigotConfig, "settings:\n  bungeecord: " + legacyForwarding + "\n",
                    StandardCharsets.UTF_8);
        }
        setYamlValue(spigotConfig, legacyForwarding, "settings", "bungeecord");
        if (type.equals("arclight")) {
            boolean modernVelocity = proxyType.equals("velocity") && velocityMode.equals("modern");
            Path arclightConfig = dir.resolve("arclight.conf");
            setHoconValue(arclightConfig, "velocity", "enable", Boolean.toString(modernVelocity));
            setHoconValue(arclightConfig, "velocity", "secret", hoconQuote(modernVelocity ? secret : ""));
        }
        if (type.equals("mohist")) {
            boolean modernVelocity = proxyType.equals("velocity") && velocityMode.equals("modern");
            Path mohistConfig = dir.resolve("mohist-config/mohist.yml");
            setYamlValue(mohistConfig, modernVelocity, "velocity", "enabled");
            setYamlValue(mohistConfig, onlineMode, "velocity", "onlineMode");
            setYamlValue(mohistConfig, modernVelocity ? secret : "", "velocity", "secret");
        }

        if (PAPER_TYPES.contains(type)) {
            if (proxyType.equals("velocity")) {
                configurePaperVelocity(dir, minecraftVersion, velocityMode.equals("modern"),
                        onlineMode, velocityMode.equals("modern") ? secret : "");
            }
            if (isPaperGlobalConfig(minecraftVersion, dir)) {
                Path globalConfig = paperConfigPath(dir, minecraftVersion);
                Files.createDirectories(globalConfig.getParent());
                setYamlValue(globalConfig, onlineMode, "proxies", "bungee-cord", "online-mode");
            }
        }
    }

    private static void configureLimbo(Path dir, int port, String proxyType, String secret,
                                       String velocityMode) throws IOException {
        Path config = dir.resolve("server.properties");
        Properties properties = new Properties();
        if (Files.isRegularFile(config)) {
            try (InputStream input = Files.newInputStream(config)) {
                properties.load(input);
            }
        }

        boolean velocity = proxyType.equals("velocity");
        boolean modernVelocity = velocity && velocityMode.equals("modern");
        boolean legacyForwarding = !velocity || velocityMode.equals("legacy");
        properties.setProperty("server-ip", "127.0.0.1");
        properties.setProperty("server-port", Integer.toString(port));
        properties.setProperty("bungeecord", Boolean.toString(legacyForwarding));
        properties.setProperty("velocity-modern", Boolean.toString(modernVelocity));
        properties.setProperty("bungee-guard", "false");
        properties.setProperty("forwarding-secrets", modernVelocity ? secret : "");
        try (OutputStream output = Files.newOutputStream(config)) {
            properties.store(output, "Managed by Hybrid Server. Backend is private behind its proxy.");
        }
    }

    private static void configurePaperVelocity(Path dir, String minecraftVersion, boolean enabled,
                                               boolean onlineMode, String secret) throws IOException {
        Path config = paperConfigPath(dir, minecraftVersion);
        if (isPaperGlobalConfig(minecraftVersion, dir)) {
            setYamlValue(config, enabled, "proxies", "velocity", "enabled");
            setYamlValue(config, onlineMode, "proxies", "velocity", "online-mode");
            setYamlValue(config, secret, "proxies", "velocity", "secret");
        } else {
            setYamlValue(config, enabled, "settings", "velocity-support", "enabled");
            setYamlValue(config, onlineMode, "settings", "velocity-support", "online-mode");
            setYamlValue(config, secret, "settings", "velocity-support", "secret");
        }
    }

    private static Path paperConfigPath(Path dir, String minecraftVersion) {
        return isPaperGlobalConfig(minecraftVersion, dir)
                ? dir.resolve("config/paper-global.yml")
                : dir.resolve("paper.yml");
    }

    private static boolean isPaperGlobalConfig(String minecraftVersion, Path dir) {
        if (minecraftVersion != null && !minecraftVersion.isBlank()) {
            return compareMinecraftVersions(minecraftVersion, "1.19.4") >= 0;
        }
        boolean globalExists = Files.isRegularFile(dir.resolve("config/paper-global.yml"));
        boolean legacyExists = Files.isRegularFile(dir.resolve("paper.yml"));
        if (globalExists != legacyExists) return globalExists;
        throw new IllegalStateException("Cannot determine the Paper configuration format for " + dir
                + ". Set the exact Minecraft version in lobby.minecraft-version or plugin.<name>.minecraft-version.");
    }

    private static int compareMinecraftVersions(String left, String right) {
        String[] leftParts = normalizeMinecraftVersion(left).split("\\.");
        String[] rightParts = normalizeMinecraftVersion(right).split("\\.");
        int length = Math.max(leftParts.length, rightParts.length);
        for (int i = 0; i < length; i++) {
            int leftPart = i < leftParts.length ? Integer.parseInt(leftParts[i]) : 0;
            int rightPart = i < rightParts.length ? Integer.parseInt(rightParts[i]) : 0;
            int comparison = Integer.compare(leftPart, rightPart);
            if (comparison != 0) return comparison;
        }
        return 0;
    }

    private static void setYamlValue(Path path, String value, String... keys) throws IOException {
        writeYamlScalar(path, yamlQuote(value), keys);
    }

    private static void setYamlValue(Path path, boolean value, String... keys) throws IOException {
        writeYamlScalar(path, Boolean.toString(value), keys);
    }

    private static void writeYamlScalar(Path path, String scalar, String... keys) throws IOException {
        List<String> lines = Files.exists(path)
                ? new ArrayList<>(Files.readAllLines(path, StandardCharsets.UTF_8))
                : new ArrayList<>();
        List<String> parents = new ArrayList<>();
        List<Integer> indents = new ArrayList<>();
        int deepestPrefixLength = 0;
        int deepestPrefixIndent = -1;
        int deepestPrefixLine = -1;
        boolean found = false;
        for (int i = 0; i < lines.size(); i++) {
            String line = lines.get(i);
            String stripped = stripYamlComment(line);
            if (stripped.isBlank()) continue;
            int indent = 0;
            while (indent < stripped.length() && stripped.charAt(indent) == ' ') indent++;
            String item = stripped.substring(indent).trim();
            int colon = item.indexOf(':');
            if (colon < 1) continue;
            String key = item.substring(0, colon).trim();
            String currentValue = item.substring(colon + 1).trim();
            while (!indents.isEmpty() && indents.getLast() >= indent) {
                indents.removeLast();
                parents.removeLast();
            }
            List<String> currentPath = new ArrayList<>(parents);
            currentPath.add(key);
            if (currentValue.isEmpty() && currentPath.size() <= keys.length
                    && currentPath.equals(List.of(keys).subList(0, currentPath.size()))) {
                if (currentPath.size() > deepestPrefixLength) {
                    deepestPrefixLength = currentPath.size();
                    deepestPrefixIndent = indent;
                    deepestPrefixLine = i;
                }
                parents.add(key);
                indents.add(indent);
                continue;
            }
            if (currentPath.equals(List.of(keys))) {
                int uncommentedLength = stripYamlComment(line).length();
                int commentIndex = uncommentedLength < line.length() ? uncommentedLength : -1;
                String comment = commentIndex >= 0 ? " " + line.substring(commentIndex).trim() : "";
                lines.set(i, line.substring(0, line.indexOf(key)) + key + ": " + scalar + comment);
                found = true;
            }
        }
        if (!found) {
            int insertAt = deepestPrefixLine < 0 ? lines.size() : deepestPrefixLine + 1;
            if (deepestPrefixLine >= 0) {
                while (insertAt < lines.size()) {
                    String stripped = stripYamlComment(lines.get(insertAt));
                    if (!stripped.isBlank()) {
                        int indent = 0;
                        while (indent < stripped.length() && stripped.charAt(indent) == ' ') indent++;
                        if (indent <= deepestPrefixIndent) break;
                    }
                    insertAt++;
                }
            } else if (!lines.isEmpty() && !lines.getLast().isBlank()) {
                lines.add("");
                insertAt++;
            }
            List<String> additions = new ArrayList<>();
            for (int i = deepestPrefixLength; i < keys.length; i++) {
                String indent = "  ".repeat(i);
                additions.add(indent + keys[i] + (i == keys.length - 1 ? ": " + scalar : ":"));
            }
            lines.addAll(insertAt, additions);
        }
        Files.createDirectories(path.getParent());
        Files.write(path, lines, StandardCharsets.UTF_8);
    }

    private static String yamlQuote(String value) {
        return "\"" + value.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    private static void setHoconValue(Path path, String sectionName, String key, String value) throws IOException {
        List<String> lines = Files.exists(path)
                ? new ArrayList<>(Files.readAllLines(path, StandardCharsets.UTF_8))
                : new ArrayList<>();
        int section = -1;
        int sectionIndent = 0;
        int depth = 0;
        for (int i = 0; i < lines.size(); i++) {
            String content = stripHoconComment(lines.get(i));
            String trimmed = content.trim();
            if (depth == 0 && trimmed.matches(Pattern.quote(sectionName) + "\\s*\\{")) {
                section = i;
                sectionIndent = content.length() - content.stripLeading().length();
                depth = countHoconBraces(content);
                break;
            }
            depth += countHoconBraces(content);
        }

        if (section < 0) {
            if (!lines.isEmpty() && !lines.getLast().isBlank()) lines.add("");
            lines.add(sectionName + " {");
            lines.add("  " + key + " = " + value);
            lines.add("}");
        } else {
            boolean found = false;
            int currentDepth = countHoconBraces(stripHoconComment(lines.get(section)));
            int closing = -1;
            for (int i = section + 1; i < lines.size(); i++) {
                String line = lines.get(i);
                String content = stripHoconComment(line);
                if (currentDepth == 1) {
                    Matcher setting = Pattern.compile("^(\\s*)" + Pattern.quote(key)
                            + "\\s*=\\s*(.*?)\\s*$").matcher(content);
                    if (setting.matches()) {
                        int commentIndex = content.length() < line.length() ? content.length() : -1;
                        String comment = commentIndex >= 0 ? " " + line.substring(commentIndex).trim() : "";
                        lines.set(i, setting.group(1) + key + " = " + value + comment);
                        found = true;
                    }
                }
                currentDepth += countHoconBraces(content);
                if (currentDepth == 0) {
                    closing = i;
                    break;
                }
            }
            if (!found) {
                if (closing < 0) {
                    throw new IllegalStateException("Unclosed '" + sectionName + "' section in " + path);
                }
                lines.add(closing, " ".repeat(sectionIndent + 2) + key + " = " + value);
            }
        }
        Files.write(path, lines, StandardCharsets.UTF_8);
    }

    private static String stripHoconComment(String line) {
        boolean quoted = false;
        boolean escaped = false;
        for (int i = 0; i < line.length(); i++) {
            char current = line.charAt(i);
            if (quoted) {
                if (escaped) escaped = false;
                else if (current == '\\') escaped = true;
                else if (current == '"') quoted = false;
            } else if (current == '"') {
                quoted = true;
            } else if (current == '#'
                    || current == '/' && i + 1 < line.length() && line.charAt(i + 1) == '/') {
                return line.substring(0, i);
            }
        }
        return line;
    }

    private static int countHoconBraces(String line) {
        boolean quoted = false;
        boolean escaped = false;
        int count = 0;
        for (int i = 0; i < line.length(); i++) {
            char current = line.charAt(i);
            if (quoted) {
                if (escaped) escaped = false;
                else if (current == '\\') escaped = true;
                else if (current == '"') quoted = false;
            } else if (current == '"') {
                quoted = true;
            } else if (current == '{') {
                count++;
            } else if (current == '}') {
                count--;
            }
        }
        return count;
    }

    private static String hoconQuote(String value) {
        return "\"" + value.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    private static void configureProxy(Path dir, String type, String bind, List<GameServer> gameServers,
                                       boolean onlineMode, String velocityMode) throws IOException {
        if (type.equals("velocity")) {
            Path config = dir.resolve("velocity.toml");
            if (!Files.exists(config)) {
                String toml = "# Generated by Hybrid Server. Edit to add proxy settings.\nconfig-version = \"2.9\"\nbind = \"" + escapeToml(bind)
                        + "\"\nmotd = \"Hybrid Server\"\nshow-max-players = 500\nonline-mode = " + onlineMode
                        + "\nforce-key-authentication = true\nprevent-client-proxy-connections = false\nplayer-info-forwarding-mode = \""
                        + velocityMode + "\"\n"
                        + (velocityMode.equals("modern") ? "forwarding-secret-file = \"forwarding.secret\"\n" : "")
                        + "announce-forge = false\nkick-existing-players = false\nsample-players-in-ping = false\n"
                        + "enable-player-address-logging = true\n\n[servers]\ntry = [\"lobby\"]\n";
                Files.writeString(config, toml, StandardCharsets.UTF_8);
            }
            ensureTomlRootKey(config, "player-info-forwarding-mode", "\"" + velocityMode + "\"", "");
            if (velocityMode.equals("modern")) {
                ensureTomlRootKey(config, "forwarding-secret-file", "\"forwarding.secret\"", "");
            }
            ensureVelocityServers(config, gameServers);
        } else {
            Path config = dir.resolve("config.yml");
            if (!Files.exists(config)) {
                String yaml = "server_connect_timeout: 5000\nlisteners:\n- query_port: " + portFromBind(bind)
                        + "\n  motd: '&1Hybrid Server'\n  tab_list: GLOBAL_PING\n  query_enabled: false\n  proxy_protocol: false\n  forced_hosts: {}\n"
                        + "  ping_passthrough: false\n  priorities:\n  - lobby\n  bind_local_address: true\n  host: " + bind
                        + "\n  max_players: 100\n  tab_size: 60\n  force_default_server: false\nremote_ping_cache: -1\nnetwork_compression_threshold: 256\n"
                        + "permissions:\n  default: []\n  admin: []\nlog_pings: true\nconnection_throttle: -1\nstats: ''\nonline_mode: " + onlineMode + "\nip_forward: true\n";
                Files.writeString(config, yaml, StandardCharsets.UTF_8);
            }
            ensureBungeeServers(config, gameServers);
        }
    }

    private static void ensureVelocityServers(Path config, List<GameServer> gameServers) throws IOException {
        List<String> lines = Files.readAllLines(config, StandardCharsets.UTF_8);
        int section = -1;
        int end = lines.size();
        for (int i = 0; i < lines.size(); i++) {
            String trimmed = lines.get(i).trim();
            if (trimmed.equals("[servers]")) section = i;
            else if (section >= 0 && trimmed.startsWith("[") && trimmed.endsWith("]")) {
                end = i;
                break;
            }
        }
        if (section < 0) {
            lines.add("");
            lines.add("[servers]");
            section = lines.size() - 1;
            end = lines.size();
        }
        List<String> additions = new ArrayList<>();
        for (GameServer server : gameServers) {
            String key = server.name() + " =";
            String entry = server.name() + " = \"127.0.0.1:" + server.port() + "\"";
            int existing = -1;
            for (int i = section + 1; i < end; i++) {
                if (lines.get(i).trim().startsWith(key)) {
                    existing = i;
                    break;
                }
            }
            if (existing < 0) additions.add(entry);
            else lines.set(existing, entry);
        }
        lines.addAll(end, additions);
        Files.write(config, lines, StandardCharsets.UTF_8);
    }

    private static void ensureBungeeServers(Path config, List<GameServer> gameServers) throws IOException {
        List<String> lines = Files.readAllLines(config, StandardCharsets.UTF_8);
        int section = -1;
        int end = lines.size();
        for (int i = 0; i < lines.size(); i++) {
            String line = lines.get(i);
            if (line.equals("servers:")) section = i;
            else if (section >= 0 && !line.isBlank() && !Character.isWhitespace(line.charAt(0))) {
                end = i;
                break;
            }
        }
        if (section < 0) {
            lines.add("");
            lines.add("servers:");
            section = lines.size() - 1;
            end = lines.size();
        }
        List<String> additions = new ArrayList<>();
        for (GameServer server : gameServers) {
            String key = "  " + server.name() + ":";
            int existing = -1;
            for (int i = section + 1; i < end; i++) {
                if (lines.get(i).equals(key)) {
                    existing = i;
                    break;
                }
            }
            if (existing < 0) {
                additions.add(key);
                additions.add("    motd: '&1" + server.name() + "'");
                additions.add("    address: 127.0.0.1:" + server.port());
                additions.add("    restricted: false");
            } else {
                boolean addressFound = false;
                for (int i = existing + 1; i < end && lines.get(i).startsWith("    "); i++) {
                    if (lines.get(i).trim().startsWith("address:")) {
                        lines.set(i, "    address: 127.0.0.1:" + server.port());
                        addressFound = true;
                        break;
                    }
                }
                if (!addressFound) {
                    lines.add(existing + 1, "    address: 127.0.0.1:" + server.port());
                    end++;
                }
            }
        }
        lines.addAll(end, additions);
        Files.write(config, lines, StandardCharsets.UTF_8);
    }

    private static void validateForwardingConfiguration(Path lobbyDir, Path proxyDir, String lobbyType,
                                                        String minecraftVersion, int port, String proxyType,
                                                        boolean onlineMode, String secret,
                                                        String velocityMode) throws IOException {
        if (proxyType.equals("velocity")) {
            Path proxyConfig = proxyDir.resolve("velocity.toml");
            if (!velocityMode.equalsIgnoreCase(readTomlValue(proxyConfig, "player-info-forwarding-mode"))) {
                throw new IllegalStateException("Set player-info-forwarding-mode = \"" + velocityMode + "\" in "
                        + proxyConfig + " or configure proxy.velocity-forwarding-mode accordingly.");
            }
            if (!Boolean.toString(onlineMode).equalsIgnoreCase(readTomlValue(proxyConfig, "online-mode"))) throw new IllegalStateException("proxy.online-mode must match online-mode in " + proxyConfig);
            if (lobbyType.equals("limbo")) {
                if (velocityMode.equals("modern")) {
                    Path secretFile = proxyDir.resolve(readTomlValue(proxyConfig, "forwarding-secret-file")).normalize();
                    if (!secretFile.startsWith(proxyDir.toAbsolutePath().normalize()) || !Files.isRegularFile(secretFile)
                            || !Files.readString(secretFile, StandardCharsets.UTF_8).trim().equals(secret)) {
                        throw new IllegalStateException("Velocity forwarding-secret-file must use the launcher-managed forwarding.secret in " + proxyConfig);
                    }
                }
                validateLimboForwarding(lobbyDir, port, proxyType, secret, velocityMode);
                return;
            }
            if (velocityMode.equals("legacy")) {
                if (!BUKKIT_TYPES.contains(lobbyType)) return;
                Path spigotConfig = lobbyDir.resolve("spigot.yml");
                if (!"true".equalsIgnoreCase(readYamlValue(spigotConfig, "settings", "bungeecord"))) throw new IllegalStateException("Set settings.bungeecord: true in " + spigotConfig);
                if (lobbyType.equals("arclight")
                        && !"false".equalsIgnoreCase(readHoconValue(
                        lobbyDir.resolve("arclight.conf"), "velocity", "enable"))) {
                    throw new IllegalStateException("Disable native modern Velocity forwarding with velocity.enable = false in "
                            + lobbyDir.resolve("arclight.conf") + " when using legacy forwarding.");
                }
                if (lobbyType.equals("mohist")
                        && !"false".equalsIgnoreCase(readYamlValue(
                        lobbyDir.resolve("mohist-config/mohist.yml"), "velocity", "enabled"))) {
                    throw new IllegalStateException("Disable native Velocity forwarding with velocity.enabled: false in "
                            + lobbyDir.resolve("mohist-config/mohist.yml") + " when using legacy forwarding.");
                }
                return;
            }
            if (velocityMode.equals("none")) {
                if (lobbyType.equals("arclight")
                        && !"false".equalsIgnoreCase(readHoconValue(
                        lobbyDir.resolve("arclight.conf"), "velocity", "enable"))) {
                    throw new IllegalStateException("Disable native Velocity forwarding with velocity.enable = false in "
                            + lobbyDir.resolve("arclight.conf") + " when forwarding is disabled.");
                }
                if (lobbyType.equals("mohist")
                        && !"false".equalsIgnoreCase(readYamlValue(
                        lobbyDir.resolve("mohist-config/mohist.yml"), "velocity", "enabled"))) {
                    throw new IllegalStateException("Disable native Velocity forwarding with velocity.enabled: false in "
                            + lobbyDir.resolve("mohist-config/mohist.yml") + " when forwarding is disabled.");
                }
                return;
            }
            if (!velocityMode.equals("modern")) return;
            Path secretFile = proxyDir.resolve(readTomlValue(proxyConfig, "forwarding-secret-file")).normalize();
            if (!secretFile.startsWith(proxyDir.toAbsolutePath().normalize()) || !Files.isRegularFile(secretFile) || !Files.readString(secretFile, StandardCharsets.UTF_8).trim().equals(secret)) {
                throw new IllegalStateException("Velocity forwarding-secret-file must use the launcher-managed forwarding.secret in " + proxyConfig);
            }
            if (lobbyType.equals("arclight")
                    && (!"true".equalsIgnoreCase(readHoconValue(
                    lobbyDir.resolve("arclight.conf"), "velocity", "enable"))
                    || !secret.equals(readHoconValue(lobbyDir.resolve("arclight.conf"), "velocity", "secret")))) {
                throw new IllegalStateException("Enable Arclight Velocity forwarding and match its secret in "
                        + lobbyDir.resolve("arclight.conf") + ".");
            }
            if (lobbyType.equals("mohist")
                    && (!"true".equalsIgnoreCase(readYamlValue(
                    lobbyDir.resolve("mohist-config/mohist.yml"), "velocity", "enabled"))
                    || !Boolean.toString(onlineMode).equalsIgnoreCase(readYamlValue(
                    lobbyDir.resolve("mohist-config/mohist.yml"), "velocity", "onlineMode"))
                    || !secret.equals(readYamlValue(
                    lobbyDir.resolve("mohist-config/mohist.yml"), "velocity", "secret")))) {
                throw new IllegalStateException("Enable Mohist Velocity forwarding and match its onlineMode and secret in "
                        + lobbyDir.resolve("mohist-config/mohist.yml") + ".");
            }
            if (lobbyType.equals("fabric")
                    && !secret.equals(readTomlValue(lobbyDir.resolve("config/FabricProxy-Lite.toml"), "secret"))) {
                throw new IllegalStateException("FabricProxy-Lite's secret must match Velocity forwarding.secret.");
            }
            if (lobbyType.equals("neoforge")) {
                if (isManagedModInstalled(lobbyDir, "neovelocity")) {
                    if (!secret.equals(readTomlSectionValue(lobbyDir.resolve("config/neovelocity-common.toml"),
                            "forwarding", "forwarding-secret"))
                            || !"IN_LINE".equalsIgnoreCase(readTomlSectionValue(
                            lobbyDir.resolve("config/neovelocity-common.toml"), "forwarding",
                            "forwarding-secret-type"))) {
                        throw new IllegalStateException("NeoVelocity's inline forwarding secret must match Velocity forwarding.secret.");
                    }
                } else if (isManagedModInstalled(lobbyDir, "proxy-compatible-forge")) {
                    validateProxyCompatibleForge(lobbyDir, secret);
                } else {
                    throw new IllegalStateException("No launcher-managed NeoForge forwarding mod is installed.");
                }
            }
            if (lobbyType.equals("forge")) {
                if (!isManagedModInstalled(lobbyDir, "proxy-compatible-forge")) {
                    throw new IllegalStateException("Proxy Compatible Forge is not installed in " + lobbyDir.resolve("mods"));
                }
                validateProxyCompatibleForge(lobbyDir, secret);
            }
            if (!BUKKIT_TYPES.contains(lobbyType)) return;
            if (!PAPER_TYPES.contains(lobbyType)) return;
            Path paperConfig = paperConfigPath(lobbyDir, minecraftVersion);
            String[] velocityPath = isPaperGlobalConfig(minecraftVersion, lobbyDir)
                    ? new String[]{"proxies", "velocity"} : new String[]{"settings", "velocity-support"};
            if (!"true".equalsIgnoreCase(readYamlValue(paperConfig, append(velocityPath, "enabled")))
                    || !Boolean.toString(onlineMode).equalsIgnoreCase(readYamlValue(paperConfig, append(velocityPath, "online-mode")))
                    || !secret.equals(readYamlValue(paperConfig, append(velocityPath, "secret")))) {
                throw new IllegalStateException("Enable Paper modern forwarding and match its online-mode and secret in " + paperConfig);
            }
        } else {
            Path proxyConfig = proxyDir.resolve("config.yml");
            if (!"true".equalsIgnoreCase(readYamlValue(proxyConfig, "ip_forward")) || !Boolean.toString(onlineMode).equalsIgnoreCase(readYamlValue(proxyConfig, "online_mode"))) {
                throw new IllegalStateException("Set ip_forward: true and match online_mode in " + proxyConfig);
            }
            if (lobbyType.equals("limbo")) {
                validateLimboForwarding(lobbyDir, port, proxyType, secret, velocityMode);
                return;
            }
            if (!BUKKIT_TYPES.contains(lobbyType)) return;
            Path spigotConfig = lobbyDir.resolve("spigot.yml");
            if (!"true".equalsIgnoreCase(readYamlValue(spigotConfig, "settings", "bungeecord"))) throw new IllegalStateException("Set settings.bungeecord: true in " + spigotConfig);
            if (lobbyType.equals("arclight")
                    && !"false".equalsIgnoreCase(readHoconValue(
                    lobbyDir.resolve("arclight.conf"), "velocity", "enable"))) {
                throw new IllegalStateException("Disable native Velocity forwarding with velocity.enable = false in "
                        + lobbyDir.resolve("arclight.conf") + " when using BungeeCord/Waterfall forwarding.");
            }
            if (lobbyType.equals("mohist")
                    && !"false".equalsIgnoreCase(readYamlValue(
                    lobbyDir.resolve("mohist-config/mohist.yml"), "velocity", "enabled"))) {
                throw new IllegalStateException("Disable native Velocity forwarding with velocity.enabled: false in "
                        + lobbyDir.resolve("mohist-config/mohist.yml") + " when using BungeeCord/Waterfall forwarding.");
            }
            if (PAPER_TYPES.contains(lobbyType) && isPaperGlobalConfig(minecraftVersion, lobbyDir)) {
                Path paperConfig = paperConfigPath(lobbyDir, minecraftVersion);
                if (!Boolean.toString(onlineMode).equalsIgnoreCase(readYamlValue(paperConfig, "proxies", "bungee-cord", "online-mode"))) {
                    throw new IllegalStateException("Match proxies.bungee-cord.online-mode to proxy.online-mode in " + paperConfig);
                }
            }
        }
    }

    private static void validateLimboForwarding(Path lobbyDir, int port, String proxyType, String secret,
                                                String velocityMode) throws IOException {
        Path config = lobbyDir.resolve("server.properties");
        Properties properties = new Properties();
        try (InputStream input = Files.newInputStream(config)) {
            properties.load(input);
        }

        boolean velocity = proxyType.equals("velocity");
        boolean modernVelocity = velocity && velocityMode.equals("modern");
        boolean legacyForwarding = !velocity || velocityMode.equals("legacy");
        if (!"127.0.0.1".equals(properties.getProperty("server-ip"))
                || !Integer.toString(port).equals(properties.getProperty("server-port"))
                || !Boolean.toString(legacyForwarding).equalsIgnoreCase(properties.getProperty("bungeecord"))
                || !Boolean.toString(modernVelocity).equalsIgnoreCase(properties.getProperty("velocity-modern"))
                || !"false".equalsIgnoreCase(properties.getProperty("bungee-guard"))
                || !(modernVelocity ? secret : "").equals(properties.getProperty("forwarding-secrets"))) {
            throw new IllegalStateException("Limbo forwarding settings in " + config
                    + " do not match the selected proxy and forwarding mode.");
        }
    }

    private static String loadOrCreateSecret(Path path) throws IOException {
        if (Files.isRegularFile(path)) {
            String existing = Files.readString(path, StandardCharsets.UTF_8).trim();
            if (!existing.isEmpty()) return existing;
        }
        byte[] bytes = new byte[32];
        new SecureRandom().nextBytes(bytes);
        String secret = Base64.getUrlEncoder().withoutPadding().encodeToString(bytes);
        Files.writeString(path, secret + System.lineSeparator(), StandardCharsets.UTF_8);
        return secret;
    }

    private static String readTomlValue(Path path, String key) throws IOException {
        for (String line : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            String trimmed = line.trim();
            if (trimmed.isEmpty() || trimmed.startsWith("#")) continue;
            int comment = trimmed.indexOf('#');
            if (comment >= 0) trimmed = trimmed.substring(0, comment).trim();
            int equals = trimmed.indexOf('=');
            if (equals < 0 || !trimmed.substring(0, equals).trim().equals(key)) continue;
            String value = trimmed.substring(equals + 1).trim();
            if (value.length() >= 2 && value.startsWith("\"") && value.endsWith("\"")) value = value.substring(1, value.length() - 1).replace("\\\"", "\"").replace("\\\\", "\\");
            return value;
        }
        throw new IllegalStateException("Missing setting '" + key + "' in " + path);
    }

    private static String readTomlSectionValue(Path path, String sectionName, String key) throws IOException {
        boolean inSection = false;
        for (String line : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            String trimmed = line.trim();
            if (trimmed.startsWith("[") && trimmed.endsWith("]")) {
                inSection = trimmed.equals("[" + sectionName + "]");
                continue;
            }
            if (!inSection || trimmed.isEmpty() || trimmed.startsWith("#")) continue;
            int comment = trimmed.indexOf('#');
            if (comment >= 0) trimmed = trimmed.substring(0, comment).trim();
            int equals = trimmed.indexOf('=');
            if (equals < 0 || !trimmed.substring(0, equals).trim().equals(key)) continue;
            String value = trimmed.substring(equals + 1).trim();
            if (value.length() >= 2 && value.startsWith("\"") && value.endsWith("\"")) {
                value = value.substring(1, value.length() - 1).replace("\\\"", "\"").replace("\\\\", "\\");
            }
            return value;
        }
        throw new IllegalStateException("Missing setting '" + sectionName + "." + key + "' in " + path);
    }

    private static String readYamlValue(Path path, String... keys) throws IOException {
        List<String> parents = new ArrayList<>();
        List<Integer> indents = new ArrayList<>();
        for (String line : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            String stripped = stripYamlComment(line);
            if (stripped.isBlank()) continue;
            int indent = 0;
            while (indent < stripped.length() && stripped.charAt(indent) == ' ') indent++;
            String item = stripped.substring(indent).trim();
            int colon = item.indexOf(':');
            if (colon < 1) continue;
            String key = item.substring(0, colon).trim();
            String value = item.substring(colon + 1).trim();
            while (!indents.isEmpty() && indents.get(indents.size() - 1) >= indent) {
                indents.remove(indents.size() - 1);
                parents.remove(parents.size() - 1);
            }
            if (value.isEmpty()) {
                parents.add(key);
                indents.add(indent);
            } else {
                List<String> pathKeys = new ArrayList<>(parents);
                pathKeys.add(key);
                if (pathKeys.equals(List.of(keys))) return unquote(value);
            }
        }
        return null;
    }

    private static String readHoconValue(Path path, String sectionName, String key) throws IOException {
        List<String> lines = Files.readAllLines(path, StandardCharsets.UTF_8);
        int depth = 0;
        boolean inSection = false;
        for (String line : lines) {
            String content = stripHoconComment(line);
            String trimmed = content.trim();
            if (!inSection && depth == 0
                    && trimmed.matches(Pattern.quote(sectionName) + "\\s*\\{")) {
                inSection = true;
                depth = countHoconBraces(content);
                continue;
            }
            if (inSection && depth == 1) {
                Matcher setting = Pattern.compile("^\\s*" + Pattern.quote(key) + "\\s*=\\s*(.*?)\\s*$")
                        .matcher(content);
                if (setting.matches()) return unquote(setting.group(1));
            }
            depth += countHoconBraces(content);
            if (inSection && depth == 0) break;
        }
        throw new IllegalStateException("Missing setting '" + sectionName + "." + key + "' in " + path);
    }

    private static String[] append(String[] prefix, String key) {
        String[] result = new String[prefix.length + 1];
        System.arraycopy(prefix, 0, result, 0, prefix.length);
        result[prefix.length] = key;
        return result;
    }

    private static String stripYamlComment(String line) {
        char quote = 0;
        for (int i = 0; i < line.length(); i++) {
            char current = line.charAt(i);
            if ((current == '"' || current == '\'') && (i == 0 || line.charAt(i - 1) != '\\')) quote = quote == 0 ? current : quote == current ? 0 : quote;
            else if (current == '#' && quote == 0) return line.substring(0, i);
        }
        return line;
    }

    private static String unquote(String value) {
        if (value.length() >= 2 && ((value.startsWith("\"") && value.endsWith("\"")) || (value.startsWith("'") && value.endsWith("'")))) return value.substring(1, value.length() - 1);
        return value;
    }

    private static String escapeToml(String value) {
        return value.replace("\\", "\\\\").replace("\"", "\\\"");
    }

    private static int portFromBind(String bind) {
        int separator = bind.lastIndexOf(':');
        if (separator < 0) throw new IllegalArgumentException("proxy.bind must be host:port: " + bind);
        return Integer.parseInt(bind.substring(separator + 1).trim());
    }

    private static InetSocketAddress proxyHealthAddress(String bind) throws IOException {
        int separator = bind.lastIndexOf(':');
        if (separator < 0) throw new IllegalArgumentException("proxy.bind must be host:port: " + bind);
        String host = bind.substring(0, separator).trim();
        int port = Integer.parseInt(bind.substring(separator + 1).trim());
        if (host.startsWith("[") && host.endsWith("]")) host = host.substring(1, host.length() - 1);
        if (host.equals("0.0.0.0") || host.equals("*")) host = "127.0.0.1";
        if (host.equals("::")) host = "::1";
        return new InetSocketAddress(InetAddress.getByName(host), port);
    }

    private static void awaitListener(Process process, InetSocketAddress address, Duration timeout, String name) throws IOException, InterruptedException {
        awaitListener(process, address, timeout, name, null);
    }

    private static void awaitListener(Process process, InetSocketAddress address, Duration timeout, String name,
                                      ProcessOutput output) throws IOException, InterruptedException {
        long deadline = System.nanoTime() + timeout.toNanos();
        while (System.nanoTime() < deadline) {
            if (!process.isAlive()) {
                if (output != null) output.awaitReader();
                throw new IllegalStateException(name + " exited before becoming ready. Check its startup log and configuration.");
            }
            try (Socket socket = new Socket()) {
                socket.connect(address, 500);
                return;
            } catch (IOException ignored) {
                Thread.sleep(300);
            }
        }
        throw new IllegalStateException(name + " did not open " + address + " within " + timeout.toSeconds() + " seconds.");
    }

    private static void copyPluginJars(Path source, Path destination) throws IOException {
        try (Stream<Path> entries = Files.list(source)) {
            for (Path jar : entries.filter(path -> Files.isRegularFile(path, LinkOption.NOFOLLOW_LINKS))
                    .filter(path -> path.getFileName().toString().toLowerCase(Locale.ROOT).endsWith(".jar")).toList()) {
                Files.copy(jar, destination.resolve(jar.getFileName()), StandardCopyOption.REPLACE_EXISTING);
            }
        }
    }

    private static String title(String type) {
        return switch (type) {
            case "bungeecord" -> "BungeeCord";
            case "waterfall" -> "Waterfall";
            case "pufferfish" -> "Pufferfish";
            case "neoforge" -> "NeoForge";
            case "arclight" -> "Arclight";
            case "mohist" -> "Mohist";
            case "leaf" -> "Leaf";
            case "leaves" -> "Leaves";
            case "limbo" -> "Limbo";
            default -> type.substring(0, 1).toUpperCase(Locale.ROOT) + type.substring(1);
        };
    }

    private record GameServer(String name, String type, Path jar, String java, String memory, int port, Path directory,
                              String launchArgs, String minecraftVersion, Path libsArchive) {
    }

    private record RunningServer(String name, Process process) {
    }

    private static void stopAll(Process proxy, List<RunningServer> gameServers) {
        stop(proxy);
        for (RunningServer server : gameServers) stop(server.process());
    }

    private static void stop(Process process) {
        if (process == null || !process.isAlive()) return;
        process.destroy();
        try {
            if (!process.waitFor(15, TimeUnit.SECONDS)) {
                process.destroyForcibly();
                process.waitFor(5, TimeUnit.SECONDS);
            }
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            process.destroyForcibly();
        }
    }
}