package benchmark.generators.tools.runners.difffold;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/** Runs difffold's {@code ted_map} binary on two Java sources and parses its JSON output. */
public class DifffoldBinary {
    /** A matched node pair as byte ranges and tree-sitter kinds. */
    public record Pair(int bs, int be, String bkind, int as, int ae, String akind) {}

    /** The matched pairs plus the byte ranges of every node of both trees. */
    public record Result(List<Pair> pairs, int[][] beforeRanges, int[][] afterRanges) {}

    public static String binaryPath() {
        String p = System.getProperty("difffold.bin", System.getenv("DIFFFOLD_TED_MAP"));
        if (p == null) throw new IllegalStateException("set -Ddifffold.bin or DIFFFOLD_TED_MAP to the ted_map binary");
        return p;
    }

    public static long timeoutSeconds() {
        return Long.getLong("difffold.timeout", 120L);
    }

    /** Thrown when the binary fails or times out. */
    public static class ToolFailure extends RuntimeException {
        public ToolFailure(String m) { super(m); }
    }

    public static Result run(String algo, byte[] before, byte[] after) throws IOException, InterruptedException {
        Path dir = Files.createTempDirectory("dfbin");
        try {
            Path b = dir.resolve("before.java");
            Path a = dir.resolve("after.java");
            Path out = dir.resolve("out.json");
            Files.write(b, before);
            Files.write(a, after);
            Process proc = new ProcessBuilder(binaryPath(), "--algo", algo, b.toString(), a.toString())
                    .redirectOutput(out.toFile())
                    .redirectError(ProcessBuilder.Redirect.DISCARD)
                    .start();
            if (!proc.waitFor(timeoutSeconds(), TimeUnit.SECONDS)) {
                proc.destroyForcibly();
                throw new ToolFailure("timeout after " + timeoutSeconds() + "s");
            }
            if (proc.exitValue() != 0) throw new ToolFailure("exit " + proc.exitValue());
            JsonNode root = new ObjectMapper().readTree(out.toFile());
            List<Pair> pairs = new ArrayList<>();
            for (JsonNode p : root.get("pairs"))
                pairs.add(new Pair(p.get(0).asInt(), p.get(1).asInt(), p.get(2).asText(),
                        p.get(3).asInt(), p.get(4).asInt(), p.get(5).asText()));
            return new Result(pairs, ranges(root.get("bn")), ranges(root.get("an")));
        } finally {
            for (File f : dir.toFile().listFiles()) f.delete();
            dir.toFile().delete();
        }
    }

    private static int[][] ranges(JsonNode arr) {
        int[][] r = new int[arr.size()][2];
        for (int i = 0; i < r.length; i++) {
            r[i][0] = arr.get(i).get(0).asInt();
            r[i][1] = arr.get(i).get(1).asInt();
        }
        return r;
    }

    /** UTF-8 byte offset to UTF-16 char index, as JDT positions are char indices. */
    public static int[] byteToChar(String s) {
        byte[] bytes = s.getBytes(StandardCharsets.UTF_8);
        int[] map = new int[bytes.length + 1];
        int bi = 0;
        for (int ci = 0; ci < s.length(); ) {
            int cp = s.codePointAt(ci);
            int nb = cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;
            int nc = Character.charCount(cp);
            for (int k = 0; k < nb; k++) map[bi + k] = ci;
            bi += nb;
            ci += nc;
        }
        map[bytes.length] = s.length();
        return map;
    }
}
