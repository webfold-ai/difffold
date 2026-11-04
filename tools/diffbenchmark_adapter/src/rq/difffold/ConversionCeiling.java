package rq.difffold;

import benchmark.generators.tools.runners.difffold.ConversionStats;
import benchmark.generators.tools.runners.difffold.DifffoldMatcher;
import com.github.gumtreediff.matchers.MappingStore;
import com.github.gumtreediff.tree.Tree;
import org.refactoringminer.astDiff.models.ASTDiff;
import org.refactoringminer.astDiff.models.ProjectASTDiff;
import org.refactoringminer.rm1.GitHistoryRefactoringMinerImpl;

import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

/**
 * Measures the loss of the byte-range to JDT conversion alone: each fixture's before file is diffed
 * against itself plus a trailing comment (RefactoringMiner reports no diff for identical files), so every JDT node has a true counterpart. The fraction of JDT nodes (outside
 * comments) that stay unmapped is the ceiling the conversion puts on any difffold result.
 *
 * usage: ConversionCeiling FIXTURES_DIR OUT_CSV [limit]
 */
public class ConversionCeiling {
    public static void main(String[] args) throws Exception {
        Path fixtures = Path.of(args[0]);
        int limit = args.length > 2 && Integer.parseInt(args[2]) > 0 ? Integer.parseInt(args[2]) : Integer.MAX_VALUE;
        List<Path> dirs = new ArrayList<>();
        try (var ds = Files.newDirectoryStream(fixtures)) {
            for (Path d : ds) if (Files.exists(d.resolve("before.java.test"))) dirs.add(d);
        }
        Collections.sort(dirs);
        long nodes = 0, mapped = 0;
        int files = 0;
        Map<String, long[]> byType = new TreeMap<>();
        ConversionStats cs = new ConversionStats();
        for (Path d : dirs) {
            if (files >= limit) break;
            Path tmp = Files.createTempDirectory("ceil");
            try {
                Path b = tmp.resolve("b"), a = tmp.resolve("a");
                Files.createDirectories(b);
                Files.createDirectories(a);
                Files.copy(d.resolve("before.java.test"), b.resolve("F.java"));
                Files.writeString(a.resolve("F.java"), Files.readString(d.resolve("before.java.test")) + "\n// ceiling\n");
                ProjectASTDiff p = new GitHistoryRefactoringMinerImpl().diffAtDirectories(b, a);
                ASTDiff diff = p.getDiffSet().iterator().next();
                String content = p.getFileContentsBefore().get(diff.getSrcPath());
                String after = p.getFileContentsAfter().get(diff.getDstPath());
                MappingStore ms = new DifffoldMatcher("topdown", content, after, cs).match(diff.src.getRoot(), diff.dst.getRoot());
                for (Tree t : diff.src.getRoot().preOrder()) {
                    boolean comment = false;
                    for (Tree x = t; x != null; x = x.getParent()) {
                        String n = x.getType().name;
                        if (n.equals("Javadoc") || n.equals("LineComment") || n.equals("BlockComment")) comment = true;
                    }
                    if (comment) continue;
                    long[] c = byType.computeIfAbsent(t.getType().name, k -> new long[2]);
                    c[0]++;
                    nodes++;
                    if (ms.isSrcMapped(t)) { c[1]++; mapped++; }
                }
                files++;
            } catch (Throwable t) {
                System.err.println("skip " + d.getFileName() + ": " + t);
            } finally {
                deleteRec(tmp.toFile());
            }
        }
        try (PrintWriter w = new PrintWriter(args[1])) {
            w.println("jdt_type,nodes,mapped,unmapped");
            w.println("ALL," + nodes + "," + mapped + "," + (nodes - mapped));
            byType.entrySet().stream().sorted((x, y) -> Long.compare(y.getValue()[0] - y.getValue()[1], x.getValue()[0] - x.getValue()[1]))
                    .forEach(e -> w.println(e.getKey() + "," + e.getValue()[0] + "," + e.getValue()[1] + "," + (e.getValue()[0] - e.getValue()[1])));
        }
        System.out.println("files=" + files + " nodes=" + nodes + " mapped=" + mapped + " ceiling=" + (double) mapped / nodes + " " + cs);
    }

    static void deleteRec(java.io.File f) {
        java.io.File[] kids = f.listFiles();
        if (kids != null) for (java.io.File k : kids) deleteRec(k);
        f.delete();
    }
}
