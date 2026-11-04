package benchmark.generators.tools.runners.difffold;

import benchmark.data.diffcase.IBenchmarkCase;
import benchmark.generators.tools.runners.gt.BaseGumTreeASTDiffProvider;
import benchmark.models.selector.DiffSelector;
import org.refactoringminer.astDiff.models.ASTDiff;
import org.refactoringminer.astDiff.models.ProjectASTDiff;

/**
 * Adapts difffold to DiffBenchmark: the mapping is computed on the file contents by the
 * {@code ted_map} binary and converted to the JDT trees of the selected {@link ASTDiff}, then
 * wrapped like GumTree's mappings (MappingStore into ExtendedMultiMappingStore with edit script).
 */
public class DifffoldASTDiffProvider extends BaseGumTreeASTDiffProvider {
    /** Conversion counters per algorithm, aggregated over all cases and threads of this JVM. */
    public static final java.util.Map<String, ConversionStats> STATS = new java.util.concurrent.ConcurrentHashMap<>();

    public DifffoldASTDiffProvider(String algo, IBenchmarkCase benchmarkCase, DiffSelector query) {
        this(algo, benchmarkCase.getProjectASTDiff(), query);
    }

    private DifffoldASTDiffProvider(String algo, ProjectASTDiff project, DiffSelector query) {
        this(algo, project, query.apply(project));
    }

    private DifffoldASTDiffProvider(String algo, ProjectASTDiff project, ASTDiff input) {
        super(new DifffoldMatcher(algo,
                project.getFileContentsBefore().get(input.getSrcPath()),
                project.getFileContentsAfter().get(input.getDstPath()),
                STATS.computeIfAbsent(algo, k -> new ConversionStats())), input);
    }
}
