import com.github.gumtreediff.matchers.Mapping;
import com.github.gumtreediff.tree.Tree;
import org.refactoringminer.astDiff.models.ASTDiff;
import org.refactoringminer.astDiff.models.ProjectASTDiff;
import org.refactoringminer.rm1.GitHistoryRefactoringMinerImpl;

import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;

/**
 * RefactoringMiner AST-diff harness. Same dump format as Eval.java (nodes + id pairs + times), matcher name
 * "refactoringminer". Each fixture is diffed with diffAtFileContents on a one-file project.
 * usage: RMEval run fixtures.tsv out-dir reps timeoutSec warmup
 */
public class RMEval {
    static int[] charToByte(String s) {
        int[] m = new int[s.length() + 1];
        int b = 0;
        for (int i = 0; i < s.length(); i++) {
            m[i] = b;
            char c = s.charAt(i);
            if (c < 0x80) b += 1;
            else if (c < 0x800) b += 2;
            else if (Character.isHighSurrogate(c) && i + 1 < s.length() && Character.isLowSurrogate(s.charAt(i + 1))) { m[i + 1] = b; b += 4; i++; }
            else if (Character.isSurrogate(c)) b += 1;
            else b += 3;
        }
        m[s.length()] = b;
        return m;
    }

    static ProjectASTDiff diff(String a, String b) throws Exception {
        Map<String, String> x = new LinkedHashMap<>(), y = new LinkedHashMap<>();
        x.put("src/main/java/Fx.java", a);
        y.put("src/main/java/Fx.java", b);
        return new GitHistoryRefactoringMinerImpl().diffAtFileContents(x, y);
    }

    public static void main(String[] a) throws Exception {
        List<String[]> fx = new ArrayList<>();
        for (String l : Files.readAllLines(Path.of(a[1]))) if (!l.isBlank()) fx.add(l.split("\t"));
        Path out = Path.of(a[2]);
        int reps = Integer.parseInt(a[3]), timeout = Integer.parseInt(a[4]), warm = Integer.parseInt(a[5]);
        String gen = "java-jdt-rm";
        Files.createDirectories(out.resolve(gen).resolve("nodes"));
        Files.createDirectories(out.resolve(gen).resolve("refactoringminer"));
        ExecutorService ex = Executors.newCachedThreadPool(r -> { Thread t = new Thread(null, r, "m", 512L << 20); t.setDaemon(true); return t; });
        for (int w = 0; w < Math.min(warm, fx.size()); w++) {
            try { String s1 = Files.readString(Path.of(fx.get(w)[1])), s2 = Files.readString(Path.of(fx.get(w)[2])); ex.submit(() -> diff(s1, s2)).get(timeout, TimeUnit.SECONDS); } catch (Throwable e) { }
        }
        Path tp = out.resolve(gen).resolve("times.tsv");
        try (PrintWriter tw = new PrintWriter(Files.newBufferedWriter(tp, StandardOpenOption.CREATE, StandardOpenOption.APPEND))) {
            if (Files.size(tp) == 0) tw.println("key\tmatcher\tparse_src_us\tparse_dst_us\tmatch_us\tstatus\tnS\tnD\tnPairs");
            for (String[] f : fx) {
                String key = f[0];
                String ssrc = new String(Files.readAllBytes(Path.of(f[1])), StandardCharsets.UTF_8);
                String sdst = new String(Files.readAllBytes(Path.of(f[2])), StandardCharsets.UTF_8);
                long best = -1; ProjectASTDiff pd = null; String status = "ok";
                for (int r = 0; r < reps; r++) {
                    Callable<ProjectASTDiff> c = () -> diff(ssrc, sdst);
                    long t0 = System.nanoTime();
                    Future<ProjectASTDiff> fu = ex.submit(c);
                    try {
                        pd = fu.get(timeout, TimeUnit.SECONDS);
                        long us = (System.nanoTime() - t0) / 1000;
                        best = best < 0 ? us : Math.min(best, us);
                        if (us > 1_000_000) break;
                    } catch (TimeoutException e) { fu.cancel(true); status = "timeout"; break; }
                    catch (ExecutionException e) { status = "error:" + e.getCause().getClass().getSimpleName() + ":" + String.valueOf(e.getCause().getMessage()).replace('\t', ' ').replace('\n', ' '); break; }
                }
                if (!status.equals("ok")) { tw.println(key + "\trefactoringminer\t0\t0\t-1\t" + status + "\t0\t0\t0"); tw.flush(); continue; }
                ASTDiff d = null;
                for (ASTDiff x : pd.getDiffSet()) { d = x; break; }
                if (d == null) { tw.println(key + "\trefactoringminer\t0\t0\t" + best + "\tno_astdiff\t0\t0\t0"); tw.flush(); continue; }
                Tree src = d.src.getRoot(), dst = d.dst.getRoot();
                int[] cb = charToByte(ssrc), cd = charToByte(sdst);
                IdentityHashMap<Tree, Integer> sid = new IdentityHashMap<>(), did = new IdentityHashMap<>();
                int ns = 0, nd = 0;
                for (Tree t : src.preOrder()) sid.put(t, ns++);
                for (Tree t : dst.preOrder()) did.put(t, nd++);
                try (PrintWriter nw = new PrintWriter(Files.newBufferedWriter(out.resolve(gen).resolve("nodes").resolve(key + ".nodes")))) {
                    nw.println(ns + " " + nd);
                    for (Tree t : src.preOrder()) nw.println("S " + sid.get(t) + " " + cb[t.getPos()] + " " + cb[t.getEndPos()] + " " + t.getType() + " 0");
                    for (Tree t : dst.preOrder()) nw.println("D " + did.get(t) + " " + cd[t.getPos()] + " " + cd[t.getEndPos()] + " " + t.getType() + " 0");
                }
                int np = 0;
                Set<String> seen = new HashSet<>();
                try (PrintWriter pw = new PrintWriter(Files.newBufferedWriter(out.resolve(gen).resolve("refactoringminer").resolve(key + ".pairs")))) {
                    for (Mapping mp : d.getAllMappings()) {
                        Integer i = sid.get(mp.first), j = did.get(mp.second);
                        if (i == null || j == null) continue;
                        if (seen.add(i + " " + j)) { pw.println(i + " " + j); np++; }
                    }
                }
                tw.println(key + "\trefactoringminer\t0\t0\t" + best + "\tok\t" + ns + "\t" + nd + "\t" + np + (pd.getDiffSet().size() > 1 ? "" : ""));
                tw.flush();
            }
        }
        System.exit(0);
    }
}
