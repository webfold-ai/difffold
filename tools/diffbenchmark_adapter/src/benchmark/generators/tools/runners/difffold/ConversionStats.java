package benchmark.generators.tools.runners.difffold;

import java.util.concurrent.atomic.AtomicLong;

/**
 * Process-wide counters for the byte-range to JDT-node conversion. Every difffold pair lands in
 * exactly one of the categories below, so the sum of the categories equals {@code pairs}.
 */
public class ConversionStats {
    /** Pairs emitted by the difffold binary. */
    public final AtomicLong pairs = new AtomicLong();
    /** Pairs that produced at least one JDT mapping. */
    public final AtomicLong converted = new AtomicLong();
    /** Of the converted pairs, those that needed the leading-comment tolerance on a side. */
    public final AtomicLong convertedViaComment = new AtomicLong();
    /** No JDT node has the range of the before side or of the after side (punctuation, tree-sitter only nodes). */
    public final AtomicLong noJdtNode = new AtomicLong();
    /** JDT nodes exist at both ranges but share no node type (cross-type relabel). */
    public final AtomicLong crossType = new AtomicLong();
    /** Every candidate JDT node was already mapped to another node. */
    public final AtomicLong conflict = new AtomicLong();
    /** Emitted JDT mappings (one converted pair can yield several, one per shared type in a same-range chain). */
    public final AtomicLong jdtMappings = new AtomicLong();
    /** JDT nodes without any tree-sitter counterpart range that were mapped by the parent-follows rule. */
    public final AtomicLong completed = new AtomicLong();
    /** JDT nodes (src side, excluding comment subtrees) and how many of them ended up mapped. */
    public final AtomicLong jdtSrcNodes = new AtomicLong();
    public final AtomicLong jdtSrcMapped = new AtomicLong();

    public void add(ConversionStats o) {
        pairs.addAndGet(o.pairs.get());
        converted.addAndGet(o.converted.get());
        convertedViaComment.addAndGet(o.convertedViaComment.get());
        noJdtNode.addAndGet(o.noJdtNode.get());
        crossType.addAndGet(o.crossType.get());
        conflict.addAndGet(o.conflict.get());
        jdtMappings.addAndGet(o.jdtMappings.get());
        completed.addAndGet(o.completed.get());
        jdtSrcNodes.addAndGet(o.jdtSrcNodes.get());
        jdtSrcMapped.addAndGet(o.jdtSrcMapped.get());
    }

    @Override
    public String toString() {
        return "pairs=" + pairs + ",converted=" + converted + ",convertedViaComment=" + convertedViaComment
                + ",noJdtNode=" + noJdtNode + ",crossType=" + crossType + ",conflict=" + conflict
                + ",jdtMappings=" + jdtMappings + ",completed=" + completed + ",jdtSrcNodes=" + jdtSrcNodes + ",jdtSrcMapped=" + jdtSrcMapped;
    }
}
