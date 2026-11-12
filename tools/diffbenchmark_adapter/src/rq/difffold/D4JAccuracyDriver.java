package rq.difffold;

import benchmark.data.dataset.IBenchmarkDataset;
import benchmark.data.diffcase.IBenchmarkCase;
import benchmark.generators.hrd.GenerationStrategy;
import benchmark.generators.tools.ASTDiffToolEnum;
import benchmark.generators.tools.runners.difffold.ConversionStats;
import benchmark.generators.tools.runners.difffold.DifffoldASTDiffProvider;
import benchmark.metrics.computers.filters.CalculationFilter;
import benchmark.metrics.computers.filters.FilterDuringGeneration;
import benchmark.metrics.computers.filters.FilterDuringMetricsCalculation;
import benchmark.metrics.computers.filters.HumanReadableDiffFilter;
import benchmark.metrics.computers.vanilla.BenchmarkComparisonInput;
import benchmark.metrics.computers.vanilla.HRDBenchmarkComputer;
import benchmark.metrics.models.BaseDiffComparisonResult;
import benchmark.metrics.models.DiffStats;
import benchmark.metrics.models.FileDiffComparisonResult;
import benchmark.metrics.writers.MetricsCsvWriter;
import benchmark.models.hrd.HumanReadableDiff;
import benchmark.models.selector.QueryBySrcPath;
import org.refactoringminer.astDiff.models.ASTDiff;
import org.refactoringminer.astDiff.models.ProjectASTDiff;
import org.refactoringminer.rm1.GitHistoryRefactoringMinerImpl;

import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.*;
import java.util.concurrent.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Scores tools against DiffBenchmark's Defects4J oracle (hrd-oracle/adb-paper/d4j-exp, one GOD.json
 * per changed file). The before/after sources are the OmniDiff Defects4J fixtures, which are the
 * exact texts the oracle offsets index into. Each Defects4J bug becomes one case, as in
 * DiffBenchmark's D4JCase: all changed files of the bug are placed in one before and one after
 * directory, RefactoringMiner builds the ProjectASTDiff, and each tool maps each file pair. Tool
 * outputs are rendered with DiffBenchmark's HRDGen3 (NO_COMMENTS_AND_JAVADOCS) and scored against
 * GOD.json with DiffBenchmark's HRDBenchmarkComputer.
 *
 * usage: D4JAccuracyDriver --oracle DIR --fixtures DIR --out DIR [--tools A,B] [--threads N]
 *        [--shard i/n] [--limit K]
 */
public class D4JAccuracyDriver {
    record Fixture(Path dir, String project, String bug, String flat) {}

    static class Case implements IBenchmarkCase {
        final String project, bug;
        final Path before, after;
        ProjectASTDiff cached;

        Case(String project, String bug, Path before, Path after) {
            this.project = project; this.bug = bug; this.before = before; this.after = after;
        }
        @Override public String getRepo() { return project; }
        @Override public String getCommit() { return bug; }
        @Override public String getID() { return project + "/" + bug; }
        @Override public IBenchmarkDataset getDataset() { return null; }
        @Override public synchronized ProjectASTDiff getProjectASTDiff() {
            if (cached == null) cached = new GitHistoryRefactoringMinerImpl().diffAtDirectories(before, after);
            return cached;
        }
    }

    static final boolean KEEP_HRD = Boolean.getBoolean("difffold.keephrd");
    static final Pattern FILE = Pattern.compile("\\*\\*File:\\*\\* `([^`]+)`");
    static final Pattern BUG = Pattern.compile("Defects4J bug \\*\\*([A-Za-z]+)-(\\d+)\\*\\*");

    public static void main(String[] argv) throws Exception {
        Map<String, String> a = new HashMap<>();
        for (int i = 0; i + 1 < argv.length; i += 2) a.put(argv[i], argv[i + 1]);
        Path oracle = Path.of(a.get("--oracle"));
        Path fixtures = Path.of(a.get("--fixtures"));
        Path out = Path.of(a.get("--out"));
        int threads = Integer.parseInt(a.getOrDefault("--threads", "3"));
        int limit = Integer.parseInt(a.getOrDefault("--limit", "0"));
        int shardI = 0, shardN = 1;
        if (a.containsKey("--shard")) {
            shardI = Integer.parseInt(a.get("--shard").split("/")[0]);
            shardN = Integer.parseInt(a.get("--shard").split("/")[1]);
        }
        List<ASTDiffToolEnum> tools = new ArrayList<>();
        for (String t : a.getOrDefault("--tools", "RMD,GTG,GTS,DFT_TD,DFT_TED,DFT_RF").split(","))
            tools.add(ASTDiffToolEnum.valueOf(t));
        Files.createDirectories(out);

        // Index fixtures by (project, bug, flattened file name) as named in the oracle.
        Map<String, Fixture> fx = new HashMap<>();
        try (var ds = Files.newDirectoryStream(fixtures)) {
            for (Path d : ds) {
                Path readme = d.resolve("README.md");
                if (!Files.exists(readme)) continue;
                String txt = Files.readString(readme);
                Matcher mf = FILE.matcher(txt), mb = BUG.matcher(txt);
                if (!mf.find() || !mb.find()) continue;
                String flat = mf.group(1).replace('/', '_').replaceAll("\\.java$", "");
                fx.put(mb.group(1) + "/" + mb.group(2) + "/" + flat, new Fixture(d, mb.group(1), mb.group(2), flat));
            }
        }
        // Enumerate oracle entries grouped by bug.
        Map<String, List<String>> bugs = new TreeMap<>();
        int oracleFiles = 0;
        try (var ps = Files.newDirectoryStream(oracle)) {
            for (Path p : ps) {
                if (!Files.isDirectory(p)) continue;
                try (var bs = Files.newDirectoryStream(p)) {
                    for (Path b : bs) {
                        try (var fs = Files.newDirectoryStream(b)) {
                            for (Path f : fs) {
                                bugs.computeIfAbsent(p.getFileName() + "/" + b.getFileName(), k -> new ArrayList<>()).add(f.getFileName().toString());
                                oracleFiles++;
                            }
                        }
                    }
                }
            }
        }
        System.out.println("oracle files=" + oracleFiles + " bugs=" + bugs.size() + " fixtures=" + fx.size());
        List<String> bugKeys = new ArrayList<>();
        int idx = 0;
        for (String k : bugs.keySet()) if (idx++ % shardN == shardI) bugKeys.add(k);
        if (limit > 0 && bugKeys.size() > limit) bugKeys = bugKeys.subList(0, limit);

        Sink sink = new Sink(out, tools);
        Set<String> done = sink.loadDone();
        ExecutorService pool = Executors.newFixedThreadPool(threads);
        List<Future<?>> futs = new ArrayList<>();
        List<String> todo = new ArrayList<>();
        for (String k : bugKeys) if (!done.contains(k)) todo.add(k);
        int total = todo.size();
        System.out.println("bugs to run=" + total + " already done=" + (bugKeys.size() - total));
        ConcurrentHashMap<String, Integer> progress = new ConcurrentHashMap<>();
        for (String bugKey : todo) {
            futs.add(pool.submit(() -> {
                try {
                    runBug(bugKey, bugs.get(bugKey), fx, oracle, out, tools, sink);
                    sink.markDone(bugKey);
                } catch (Throwable t) {
                    sink.failure(bugKey + ",*,case," + t.toString().replace(',', ';').replace('\n', ' '));
                    t.printStackTrace();
                }
                int n = progress.merge("n", 1, Integer::sum);
                if (n % 20 == 0) System.out.println("progress " + n + "/" + total);
            }));
        }
        for (Future<?> f : futs) f.get();
        pool.shutdown();
        sink.close();
        try (PrintWriter w = new PrintWriter(new FileWriter(out.resolve("conversion.csv").toFile(), true))) {
            for (var e : DifffoldASTDiffProvider.STATS.entrySet()) w.println(e.getKey() + "," + e.getValue());
        }
        summarize(out, tools);
        System.out.println("scored (see summary-*.csv); oracle files=" + oracleFiles);
    }

    /** Append-only outputs so a killed run loses at most the bugs in flight. */
    static class Sink {
        final Path out;
        final List<ASTDiffToolEnum> tools;
        final FileWriter[] native_ = new FileWriter[2];
        final FileWriter[] records = new FileWriter[2];
        final FileWriter doneW, failW, timeW;

        Sink(Path out, List<ASTDiffToolEnum> tools) throws Exception {
            this.out = out;
            this.tools = tools;
            String[] names = {"NO_FILTER", "INTRA_FILE_ONLY"};
            for (int i = 0; i < 2; i++) {
                File nf = out.resolve("d4j-" + names[i] + ".csv").toFile();
                File rf = out.resolve("records-" + names[i] + ".csv").toFile();
                boolean newN = !nf.exists() || nf.length() == 0, newR = !rf.exists() || rf.length() == 0;
                native_[i] = new FileWriter(nf, true);
                records[i] = new FileWriter(rf, true);
                if (newR) records[i].write("bug,file,tool,mapping_TP_raw,mapping_ignored,mapping_FP,mapping_FN,element_TP_raw,element_ignored,element_FP,element_FN,perfect_stats,perfect_bytes\n");
                headerPending[i] = newN;
            }
            doneW = new FileWriter(out.resolve("done.txt").toFile(), true);
            failW = new FileWriter(out.resolve("failures.csv").toFile(), true);
            File tf = out.resolve("timings.csv").toFile();
            boolean newT = !tf.exists() || tf.length() == 0;
            timeW = new FileWriter(tf, true);
            if (newT) timeW.write("bug,file,tool,millis,status\n");
        }
        final boolean[] headerPending = new boolean[2];

        Set<String> loadDone() throws Exception {
            Path p = out.resolve("done.txt");
            return Files.exists(p) ? new HashSet<>(Files.readAllLines(p)) : new HashSet<>();
        }
        synchronized void markDone(String k) throws Exception { doneW.write(k + "\n"); doneW.flush(); }
        synchronized void failure(String l) { try { failW.write(l + "\n"); failW.flush(); } catch (Exception e) { throw new RuntimeException(e); } }
        synchronized void timing(String l) { try { timeW.write(l + "\n"); timeW.flush(); } catch (Exception e) { throw new RuntimeException(e); } }
        synchronized void result(int fi, FileDiffComparisonResult r, String bug, String flat, boolean[] perfectBytes) throws Exception {
            if (headerPending[fi]) { r.writeHeader(native_[fi]); headerPending[fi] = false; }
            r.writeData(native_[fi]);
            native_[fi].flush();
            int igM = r.getIgnore().getIntraFileMappings().getMappings().size();
            int igE = r.getIgnore().getIntraFileMappings().getMatchedElements().size();
            int ti = 0;
            for (ASTDiffToolEnum tool : tools) {
                DiffStats ds = r.getDiffStatsList().get(tool.name());
                boolean p = ds.getAbstractMappingStats().getFP() == 0 && ds.getAbstractMappingStats().getFN() == 0
                        && ds.getProgramElementStats().getFP() == 0 && ds.getProgramElementStats().getFN() == 0;
                records[fi].write(bug + "," + flat + "," + tool.name() + ","
                        + ds.getAbstractMappingStats().getTP() + "," + igM + "," + ds.getAbstractMappingStats().getFP() + "," + ds.getAbstractMappingStats().getFN() + ","
                        + ds.getProgramElementStats().getTP() + "," + igE + "," + ds.getProgramElementStats().getFP() + "," + ds.getProgramElementStats().getFN() + ","
                        + (p ? 1 : 0) + "," + (perfectBytes[ti++] ? 1 : 0) + "\n");
            }
            records[fi].flush();
        }
        void close() throws Exception {
            for (FileWriter w : native_) w.close();
            for (FileWriter w : records) w.close();
            doneW.close(); failW.close(); timeW.close();
        }
    }

    static void runBug(String bugKey, List<String> flats, Map<String, Fixture> fx, Path oracle, Path out,
                       List<ASTDiffToolEnum> tools, Sink sink) throws Exception {
        String[] pb = bugKey.split("/");
        Path tmp = Files.createTempDirectory("d4jcase");
        Path bdir = tmp.resolve("before");
        Path adir = tmp.resolve("after");
        Files.createDirectories(bdir);
        Files.createDirectories(adir);
        List<String> usable = new ArrayList<>();
        for (String flat : flats) {
            Fixture f = fx.get(bugKey + "/" + flat);
            if (f == null) {
                sink.failure(bugKey + "," + flat + ",nofixture,");
                continue;
            }
            Files.copy(f.dir().resolve("before.java.test"), bdir.resolve(flat + ".java"), StandardCopyOption.REPLACE_EXISTING);
            Files.copy(f.dir().resolve("after.java.test"), adir.resolve(flat + ".java"), StandardCopyOption.REPLACE_EXISTING);
            usable.add(flat);
        }
        if (usable.isEmpty()) return;
        Case c = new Case(pb[0], pb[1], bdir, adir);
        ProjectASTDiff project = c.getProjectASTDiff();
        Set<String> have = new HashSet<>();
        for (ASTDiff d : project.getDiffSet()) have.add(d.getSrcPath());
        for (String flat : usable) {
            if (!have.contains(flat + ".java")) {
                sink.failure(bugKey + "," + flat + ",noASTDiff,RefactoringMiner produced no diff for the file");
                continue;
            }
            Path fileOut = out.resolve("hrd").resolve(pb[0]).resolve(pb[1]).resolve(flat);
            Files.createDirectories(fileOut);
            for (String g : new String[]{"GOD", "TRV"}) {
                Path link = fileOut.resolve(g + ".json");
                Files.deleteIfExists(link);
                Files.createSymbolicLink(link, oracle.resolve(pb[0]).resolve(pb[1]).resolve(flat).resolve(g + ".json").toAbsolutePath());
            }
            for (ASTDiffToolEnum tool : tools) {
                long t0 = System.nanoTime();
                HumanReadableDiff hrd;
                String status = "ok";
                try {
                    ASTDiff diff = tool.apply(c, new QueryBySrcPath(flat + ".java")).getASTDiff();
                    hrd = GenerationStrategy.NO_COMMENTS_AND_JAVADOCS.apply(c, diff);
                } catch (Throwable t) {
                    status = t.getClass().getSimpleName();
                    sink.failure(bugKey + "," + flat + "," + tool.name() + "," + t.toString().replace(',', ';').replace('\n', ' '));
                    hrd = HumanReadableDiff.makeEmpty();
                }
                sink.timing(bugKey + "," + flat + "," + tool.name() + "," + (System.nanoTime() - t0) / 1_000_000 + "," + status);
                HumanReadableDiff.write(fileOut.resolve(tool.name() + ".json").toFile(), hrd);
            }
            for (int fi = 0; fi < 2; fi++) {
                HumanReadableDiffFilter filter = fi == 0 ? FilterDuringGeneration.NO_FILTER.getFilter() : FilterDuringGeneration.INTRA_FILE_ONLY.getFilter();
                BenchmarkComparisonInput in = BenchmarkComparisonInput.readDir(fileOut, new LinkedHashSet<>(tools));
                FileDiffComparisonResult r = new FileDiffComparisonResult(c, flat);
                new HRDBenchmarkComputer(filter, FilterDuringMetricsCalculation.NO_FILTER, in).compute(r, Set.of());
                boolean perfect[] = new boolean[tools.size()];
                int ti = 0;
                for (ASTDiffToolEnum tool : tools) {
                    byte[] god = Files.readAllBytes(fileOut.resolve("GOD.json"));
                    perfect[ti++] = Arrays.equals(god, Files.readAllBytes(fileOut.resolve(tool.name() + ".json")));
                }
                sink.result(fi, r, bugKey, flat, perfect);
            }
            if (!KEEP_HRD) deleteRec(fileOut.toFile());
        }
        deleteRec(tmp.toFile());
    }

    static void deleteRec(File f) {
        File[] kids = f.listFiles();
        if (kids != null) for (File k : kids) deleteRec(k);
        f.delete();
    }

    /** Aggregates records-*.csv into summary-*.csv, in the benchmark's TP_raw / TP / FP / FN terms. */
    static void summarize(Path out, List<ASTDiffToolEnum> tools) throws Exception {
        for (String filterName : new String[]{"NO_FILTER", "INTRA_FILE_ONLY"}) {
            Map<String, long[]> agg = new LinkedHashMap<>();
            Set<String> files = new HashSet<>();
            List<String> lines = Files.readAllLines(out.resolve("records-" + filterName + ".csv"));
            for (String line : lines.subList(1, lines.size())) {
                String[] c = line.split(",");
                files.add(c[0] + "/" + c[1]);
                long[] v = agg.computeIfAbsent(c[2], k -> new long[13]);
                for (int i = 3; i < 13; i++) v[i - 3] += Long.parseLong(c[i]);
            }
            try (PrintWriter w = new PrintWriter(out.resolve("summary-" + filterName + ".csv").toFile())) {
                w.println("tool,files,kind,TP_raw,TP,FP,FN,precision,recall,f1,precision_raw,recall_raw,perfect_files_stats,perfect_files_bytes");
                for (ASTDiffToolEnum tool : tools) {
                    long[] v = agg.get(tool.name());
                    if (v == null) continue;
                    // v: 0 mTPraw, 1 mIgnoredSum, 2 mFP, 3 mFN, 4 eTPraw, 5 eIgnoredSum, 6 eFP, 7 eFN, 8 perfStats, 9 perfBytes
                    for (String kind : new String[]{"abstractMapping", "programElement", "all"}) {
                        long tpRaw = 0, tp = 0, fp = 0, fn = 0;
                        if (!kind.equals("programElement")) { tpRaw += v[0]; tp += v[0] - v[1]; fp += v[2]; fn += v[3]; }
                        if (!kind.equals("abstractMapping")) { tpRaw += v[4]; tp += v[4] - v[5]; fp += v[6]; fn += v[7]; }
                        double pr = tp / (double) (tp + fp), rc = tp / (double) (tp + fn);
                        double prr = tpRaw / (double) (tpRaw + fp), rcr = tpRaw / (double) (tpRaw + fn);
                        w.printf(Locale.ROOT, "%s,%d,%s,%d,%d,%d,%d,%.4f,%.4f,%.4f,%.4f,%.4f,%s,%s%n", tool.name(), files.size(), kind, tpRaw, tp, fp, fn,
                                pr, rc, 2 * pr * rc / (pr + rc), prr, rcr,
                                kind.equals("all") ? v[8] : "", kind.equals("all") ? v[9] : "");
                    }
                }
            }
        }
    }

    static List<String> sorted(List<String> l) {
        List<String> c = new ArrayList<>(l);
        Collections.sort(c);
        return c;
    }
}
