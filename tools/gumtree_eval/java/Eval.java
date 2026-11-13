import com.github.gumtreediff.gen.TreeGenerators;
import com.github.gumtreediff.matchers.Mapping;
import com.github.gumtreediff.matchers.MappingStore;
import com.github.gumtreediff.matchers.Matcher;
import com.github.gumtreediff.matchers.Matchers;
import com.github.gumtreediff.tree.Tree;
import com.github.gumtreediff.tree.TreeContext;

import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;

/**
 * GumTree evaluation harness. Parses before/after with a given GumTree generator, runs every requested
 * matcher in-process, and dumps (a) node tables with UTF-8 byte ranges and (b) mapped node-id pairs plus timings.
 *
 * usage: Eval list <generator-id> | Eval run <fixtures.tsv> <out-dir> <generator-id> <matchers,comma|all> <reps> <timeoutSec> <warmup>
 * fixtures.tsv lines: key TAB beforePath TAB afterPath
 * outputs:
 *   out/<gen>/nodes/<key>.nodes    : first line "nS nD", then "S|D id start end type depth" per node (preorder ids, byte offsets)
 *   out/<gen>/<matcher>/<key>.pairs: "srcId dstId" lines
 *   out/<gen>/times.tsv            : key matcher parse_src_ms parse_dst_ms match_ms status nS nD nPairs
 */
public class Eval {
    static int[] charToByte(String s) {
        int[] m = new int[s.length() + 1];
        int b = 0;
        for (int i = 0; i < s.length(); i++) {
            m[i] = b;
            char c = s.charAt(i);
            int len;
            if (c < 0x80) len = 1;
            else if (c < 0x800) len = 2;
            else if (Character.isHighSurrogate(c) && i + 1 < s.length() && Character.isLowSurrogate(s.charAt(i + 1))) {
                m[i + 1] = b; len = 4; b += len; i++; continue;
            } else if (Character.isSurrogate(c)) len = 1;
            else len = 3;
            b += len;
        }
        m[s.length()] = b;
        return m;
    }

    static long nowMs(long t0) { return (System.nanoTime() - t0) / 1000; } // microseconds

    public static void main(String[] a) throws Exception {
        // GumTree 4.0.0-beta4 fills its registries from the command-line entry point only.
        com.github.gumtreediff.client.Run.initGenerators();
        com.github.gumtreediff.client.Run.initMatchers();
        if (a[0].equals("list")) {
            for (var e : Matchers.getInstance().getEntries()) System.out.println("matcher " + e.id + " prio=" + e.priority + " " + e.toString());
            System.out.println("default matcher: " + Matchers.getInstance().getMatcher().getClass().getName());
            for (var e : TreeGenerators.getInstance().getEntries()) System.out.println("generator " + e.id + " prio=" + e.priority);
            return;
        }
        List<String[]> fx = new ArrayList<>();
        for (String l : Files.readAllLines(Path.of(a[1]))) { if (!l.isBlank()) fx.add(l.split("\t")); }
        Path out = Path.of(a[2]);
        String gen = a[3];
        List<String> matchers = new ArrayList<>();
        if (a[4].equals("all")) { for (var e : Matchers.getInstance().getEntries()) matchers.add(e.id); }
        else matchers.addAll(Arrays.asList(a[4].split(",")));
        int reps = Integer.parseInt(a[5]);
        int timeout = Integer.parseInt(a[6]);
        int warm = Integer.parseInt(a[7]);
        Files.createDirectories(out.resolve(gen).resolve("nodes"));
        ExecutorService ex = Executors.newCachedThreadPool(r -> { Thread t = new Thread(null, r, "m", 512L << 20); t.setDaemon(true); return t; });
        Set<String> dead = new HashSet<>(); // matchers that timed out on a smaller fixture are skipped on bigger ones
        Map<String, Long> deadAt = new HashMap<>();
        try (PrintWriter tw = new PrintWriter(Files.newBufferedWriter(out.resolve(gen).resolve("times.tsv"), StandardOpenOption.CREATE, StandardOpenOption.APPEND))) {
            if (Files.size(out.resolve(gen).resolve("times.tsv")) == 0) tw.println("key\tmatcher\tparse_src_us\tparse_dst_us\tmatch_us\tstatus\tnS\tnD\tnPairs");
            // warm-up: run all matchers on the first `warm` fixtures, discard
            for (int w = 0; w < Math.min(warm, fx.size()); w++) {
                String[] f = fx.get(w);
                try {
                    TreeContext cs = TreeGenerators.getInstance().getTree(f[1], gen), cd = TreeGenerators.getInstance().getTree(f[2], gen);
                    for (String m : matchers) {
                        if (m.equals("rted-theta") || m.equals("change-distiller") || m.equals("change-distiller-theta")) { if (cs.getRoot().getMetrics().size > 400) continue; }
                        Future<?> fu = ex.submit(() -> Matchers.getInstance().getMatcher(m).match(cs.getRoot(), cd.getRoot()));
                        try { fu.get(timeout, TimeUnit.SECONDS); } catch (Exception e) { fu.cancel(true); }
                    }
                } catch (Exception e) { }
            }
            for (String[] f : fx) {
                String key = f[0];
                String ssrc = new String(Files.readAllBytes(Path.of(f[1])), StandardCharsets.UTF_8);
                String sdst = new String(Files.readAllBytes(Path.of(f[2])), StandardCharsets.UTF_8);
                int[] cb = charToByte(ssrc), cd2 = charToByte(sdst);
                TreeContext cs = null, cd = null;
                long ps = -1, pd = -1;
                try {
                    for (int r = 0; r < reps; r++) {
                        long t0 = System.nanoTime(); cs = TreeGenerators.getInstance().getTree(f[1], gen); long x = nowMs(t0);
                        t0 = System.nanoTime(); cd = TreeGenerators.getInstance().getTree(f[2], gen); long y = nowMs(t0);
                        ps = ps < 0 ? x : Math.min(ps, x); pd = pd < 0 ? y : Math.min(pd, y);
                    }
                } catch (Throwable e) {
                    for (String m : matchers) tw.println(key + "\t" + m + "\t-1\t-1\t-1\tparse_error:" + e.getClass().getSimpleName() + "\t0\t0\t0");
                    tw.flush();
                    continue;
                }
                Tree src = cs.getRoot(), dst = cd.getRoot();
                IdentityHashMap<Tree, Integer> sid = new IdentityHashMap<>(), did = new IdentityHashMap<>();
                try (PrintWriter nw = new PrintWriter(Files.newBufferedWriter(out.resolve(gen).resolve("nodes").resolve(key + ".nodes")))) {
                    int ns = 0, nd = 0;
                    for (Tree t : src.preOrder()) sid.put(t, ns++);
                    for (Tree t : dst.preOrder()) did.put(t, nd++);
                    nw.println(ns + " " + nd);
                    for (Tree t : src.preOrder()) nw.println("S " + sid.get(t) + " " + cb[t.getPos()] + " " + cb[t.getEndPos()] + " " + t.getType() + " " + t.getMetrics().depth);
                    for (Tree t : dst.preOrder()) nw.println("D " + did.get(t) + " " + cd2[t.getPos()] + " " + cd2[t.getEndPos()] + " " + t.getType() + " " + t.getMetrics().depth);
                }
                long size = (long) sid.size() * did.size();
                for (String m : matchers) {
                    Long da = deadAt.get(m);
                    if (da != null && size >= da) { tw.println(key + "\t" + m + "\t" + ps + "\t" + pd + "\t-1\tskipped_after_timeout\t" + sid.size() + "\t" + did.size() + "\t0"); continue; }
                    long best = -1; MappingStore ms = null; String status = "ok";
                    for (int r = 0; r < reps; r++) {
                        final Tree s2 = src, d2 = dst;
                        Callable<MappingStore> c = () -> { Matcher mt = Matchers.getInstance().getMatcher(m); long t0 = System.nanoTime(); MappingStore res = mt.match(s2, d2); lastNs.set(System.nanoTime() - t0); return res; };
                        Future<MappingStore> fu = ex.submit(c);
                        try {
                            ms = fu.get(timeout, TimeUnit.SECONDS);
                            long us = lastNs.get() / 1000;
                            best = best < 0 ? us : Math.min(best, us);
                            if (us > 1_000_000) break;
                        } catch (TimeoutException e) { fu.cancel(true); status = "timeout"; deadAt.merge(m, size, Math::min); break; }
                        catch (ExecutionException e) { status = "error:" + e.getCause().getClass().getSimpleName() + ":" + String.valueOf(e.getCause().getMessage()).replace('\t', ' ').replace('\n', ' '); break; }
                    }
                    int np = 0;
                    if (status.equals("ok") && ms != null) {
                        Path d = out.resolve(gen).resolve(m); Files.createDirectories(d);
                        try (PrintWriter pw = new PrintWriter(Files.newBufferedWriter(d.resolve(key + ".pairs")))) {
                            for (Mapping mp : ms) { pw.println(sid.get(mp.first) + " " + did.get(mp.second)); np++; }
                        }
                    }
                    tw.println(key + "\t" + m + "\t" + ps + "\t" + pd + "\t" + best + "\t" + status + "\t" + sid.size() + "\t" + did.size() + "\t" + np);
                }
                tw.flush();
            }
        }
        System.exit(0);
    }
    static final java.util.concurrent.atomic.AtomicLong lastNs = new java.util.concurrent.atomic.AtomicLong();
}
