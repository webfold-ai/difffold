package benchmark.generators.tools;

import benchmark.data.diffcase.IBenchmarkCase;
import benchmark.generators.tools.models.ASTDiffProvider;
import benchmark.generators.tools.models.ASTDiffProviderForBenchmark;
import benchmark.generators.tools.models.IASTDiffTool;
import benchmark.generators.tools.runners.difffold.DifffoldASTDiffProvider;
import benchmark.generators.tools.runners.gt.GreedyGumTreeASTDiffProvider;
import benchmark.generators.tools.runners.gt.SimpleGumTreeASTDiffProvider;
import benchmark.models.selector.DiffSelector;
import org.refactoringminer.astDiff.models.ASTDiff;

/**
 * Reduced tool registry used to build DiffBenchmark in this environment. The upstream enum also
 * lists IJM, MTDiff, GumTree 2.0, IASTMapper, RM 2.0 and Spoon, whose jars (libs/*.jar in the
 * upstream repository) are not available here. Constants and short names of the tools kept here are
 * identical to upstream, and DFT_TD and DFT_TED are the difffold additions (see the .patch file).
 */
public enum ASTDiffToolEnum implements IASTDiffTool {
    GOD("Ground Truth", null),
    RMD("RefactoringMiner", (benchmarkCase, query) -> () -> query.apply(benchmarkCase.getProjectASTDiff())),
    GTG("GumTree Greedy 3.0", (benchmarkCase, query) -> new GreedyGumTreeASTDiffProvider(query.apply(benchmarkCase.getProjectASTDiff()))),
    GTS("GumTree Simple 3.0", (benchmarkCase, query) -> new SimpleGumTreeASTDiffProvider(query.apply(benchmarkCase.getProjectASTDiff()))),
    TRV("TrivialDiff", null),
    DFT_TD("difffold top-down", (benchmarkCase, query) -> new DifffoldASTDiffProvider("topdown", benchmarkCase, query)),
    DFT_TED("difffold tree edit distance", (benchmarkCase, query) -> new DifffoldASTDiffProvider("ted", benchmarkCase, query)),
    ;

    private final ASTDiffProviderForBenchmark factory;
    private final String toolName;

    ASTDiffToolEnum(String toolName, ASTDiffProviderForBenchmark factory) {
        this.factory = factory;
        this.toolName = toolName;
    }

    public String getToolName() {
        return toolName;
    }

    public String getShortName() {
        return this.name();
    }

    @Override
    public ASTDiffProvider apply(IBenchmarkCase benchmarkCase, DiffSelector query) {
        return factory.apply(benchmarkCase, query);
    }

    public ASTDiff diff(IBenchmarkCase benchmarkCase, DiffSelector querySelector) throws Exception {
        return factory.apply(benchmarkCase, querySelector).getASTDiff();
    }
}
