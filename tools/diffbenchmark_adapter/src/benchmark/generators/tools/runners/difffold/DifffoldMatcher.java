package benchmark.generators.tools.runners.difffold;

import com.github.gumtreediff.matchers.MappingStore;
import com.github.gumtreediff.matchers.Matcher;
import com.github.gumtreediff.tree.Tree;
import com.github.gumtreediff.matchers.Configurable;
import com.github.gumtreediff.matchers.GumtreeProperties;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A GumTree {@link Matcher} whose mappings come from difffold's tree-sitter based mapping.
 *
 * <p>Conversion rule. difffold emits matched node pairs as UTF-8 byte ranges plus tree-sitter kinds.
 * Byte ranges are converted to char offsets and looked up in the JDT tree DiffBenchmark builds, as
 * the chain of JDT nodes (outermost first) whose [pos, endPos) equals the range. If no JDT node has
 * exactly that range, nodes whose range differs only by a leading Javadoc or comment are accepted,
 * because tree-sitter keeps comments outside a declaration while JDT includes the Javadoc in it.
 * For a pair, every JDT node type present in both chains is mapped (k-th occurrence of a type on the
 * before side to the k-th on the after side), so a same-range wrapper such as SimpleType over
 * SimpleName is mapped on both levels. Only same-type JDT pairs are produced, matching GumTree's type
 * rule and the oracle (it contains no cross-type mapping). Pairs are classified in
 * {@link ConversionStats} as converted, noJdtNode, crossType or conflict. The tree-sitter kinds are
 * not consulted: the range and the JDT type decide.
 */
public class DifffoldMatcher implements Matcher {
    private final String algo;
    private final String srcContent;
    private final String dstContent;
    private final ConversionStats stats;
    private GumtreeProperties properties = new GumtreeProperties();

    public DifffoldMatcher(String algo, String srcContent, String dstContent, ConversionStats stats) {
        this.algo = algo;
        this.srcContent = srcContent;
        this.dstContent = dstContent;
        this.stats = stats;
    }

    @Override
    public void configure(GumtreeProperties properties) {
        this.properties = properties;
    }

    @Override
    public MappingStore match(Tree src, Tree dst, MappingStore mappings) {
        List<DifffoldBinary.Pair> pairs;
        try {
            pairs = DifffoldBinary.run(algo, srcContent.getBytes(StandardCharsets.UTF_8), dstContent.getBytes(StandardCharsets.UTF_8));
        } catch (IOException | InterruptedException e) {
            throw new DifffoldBinary.ToolFailure(e.toString());
        }
        int[] b2c = DifffoldBinary.byteToChar(srcContent);
        int[] a2c = DifffoldBinary.byteToChar(dstContent);
        Index si = new Index(src, srcContent);
        Index di = new Index(dst, dstContent);
        for (DifffoldBinary.Pair p : pairs) {
            stats.pairs.incrementAndGet();
            boolean[] viaComment = new boolean[1];
            List<Tree> cb = si.lookup(b2c[p.bs()], b2c[p.be()], viaComment);
            List<Tree> ca = di.lookup(a2c[p.as()], a2c[p.ae()], viaComment);
            if (cb.isEmpty() || ca.isEmpty()) {
                stats.noJdtNode.incrementAndGet();
                continue;
            }
            boolean shared = false;
            boolean added = false;
            Map<String, Integer> seen = new HashMap<>();
            for (Tree u : cb) {
                String type = u.getType().name;
                int k = seen.merge(type, 1, Integer::sum);
                Tree v = nth(ca, type, k);
                if (v == null) continue;
                shared = true;
                if (mappings.isSrcMapped(u) || mappings.isDstMapped(v)) continue;
                mappings.addMapping(u, v);
                stats.jdtMappings.incrementAndGet();
                added = true;
            }
            if (added) {
                stats.converted.incrementAndGet();
                if (viaComment[0]) stats.convertedViaComment.incrementAndGet();
            } else if (shared) stats.conflict.incrementAndGet();
            else stats.crossType.incrementAndGet();
        }
        int n = 0;
        int m = 0;
        for (Tree t : src.preOrder()) {
            if (insideComment(t)) continue;
            n++;
            if (mappings.isSrcMapped(t)) m++;
        }
        stats.jdtSrcNodes.addAndGet(n);
        stats.jdtSrcMapped.addAndGet(m);
        return mappings;
    }

    private static boolean insideComment(Tree t) {
        for (Tree x = t; x != null; x = x.getParent()) {
            String n = x.getType().name;
            if (n.equals("Javadoc") || n.equals("LineComment") || n.equals("BlockComment")) return true;
        }
        return false;
    }

    private static Tree nth(List<Tree> chain, String type, int k) {
        int c = 0;
        for (Tree t : chain) if (t.getType().name.equals(type) && ++c == k) return t;
        return null;
    }

    /** Index of a JDT tree by exact range and by range with leading comments skipped. */
    static class Index {
        final Map<Long, List<Tree>> exact = new HashMap<>();
        final Map<Long, List<Tree>> core = new HashMap<>();

        Index(Tree root, String content) {
            for (Tree t : root.preOrder()) {
                int s = t.getPos();
                int e = t.getEndPos();
                exact.computeIfAbsent(key(s, e), x -> new ArrayList<>()).add(t);
                int q = skipComments(content, s, e);
                if (q > s) core.computeIfAbsent(key(q, e), x -> new ArrayList<>()).add(t);
            }
        }

        List<Tree> lookup(int s, int e, boolean[] viaComment) {
            List<Tree> l = exact.get(key(s, e));
            if (l != null) return l;
            l = core.get(key(s, e));
            if (l != null) {
                viaComment[0] = true;
                return l;
            }
            return List.of();
        }

        static long key(int s, int e) {
            return ((long) s << 32) | (e & 0xffffffffL);
        }

        static int skipComments(String c, int s, int e) {
            int q = s;
            while (q < e) {
                char ch = c.charAt(q);
                if (Character.isWhitespace(ch)) q++;
                else if (c.startsWith("/*", q)) {
                    int end = c.indexOf("*/", q + 2);
                    if (end < 0) return s;
                    q = end + 2;
                } else if (c.startsWith("//", q)) {
                    int end = c.indexOf('\n', q);
                    if (end < 0) return s;
                    q = end + 1;
                } else break;
            }
            return q;
        }
    }
}
