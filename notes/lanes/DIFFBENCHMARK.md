# difffold on DiffBenchmark

difffold is scored on DiffBenchmark's own oracle and metric code, next to GumTree and RefactoringMiner.
Everything below was run in full: 996 oracle files, 800 Defects4J bugs, no tool failures and no timeouts.

## What ran

DiffBenchmark (pouryafard75/DiffBenchmark) scores a tool by rendering its mapping as a Human Readable Diff (HRDGen3,
`NO_COMMENTS_AND_JAVADOCS`) over RefactoringMiner's JDT trees and comparing it to the oracle `GOD.json` with
`HRDBenchmarkComputer`. The only oracle in the checkout is `hrd-oracle/adb-paper/d4j-exp` (the Defects4J oracle,
996 files, 597k oracle mappings). The RefOracle (the paper's main oracle, 285 files) needs the RefactoringMiner repo
test resources and GitHub downloads, which are not available here, so it was not rerun.

The before/after sources are the OmniDiff Defects4J fixtures (`omnidiff-apeiron/.../diffs/defects4j`). Their READMEs state
they are the exact texts the oracle offsets index into. Sanity check: RefactoringMiner, run fresh, reproduces `GOD.json`
byte for byte on 881 of 996 files, so offsets and sources line up.

Tools scored (DiffBenchmark short names):

| name | what |
| --- | --- |
| `RMD` | RefactoringMiner 3.0.10 (the oracle was built from RM output plus manual fixes, so it favours RM) |
| `GTG` | GumTree 3.0 greedy (classic) |
| `GTS` | GumTree 3.0 simple |
| `DFT_TD` | difffold, ordered top-down mapping from `diff_checked` + `correspondence` |
| `DFT_TED` | difffold, optimal general tree edit mapping (`ted_mapping`) |

Pipeline per Defects4J bug (as `D4JCase` does): all changed files of the bug go in one before and one after directory,
RefactoringMiner builds the `ProjectASTDiff`, each tool maps each file pair on the JDT trees, HRDGen3 renders it, and
DiffBenchmark's `HRDBenchmarkComputer` compares it with `GOD.json`. `TRV.json` (the trivial mappings every tool gets) is
read from the oracle directory and used for the benchmark's `TP - ignored` correction, computed over this five-tool set.

## Numbers (DiffBenchmark metrics, NO_FILTER, 996 files)

`all` = abstract mappings + program elements. `P`, `R`, `F1` use the benchmark's adjusted TP (raw TP minus trivial mappings
all tools share). `P raw`, `R raw` use raw TP and do not depend on the tool set. `perfect` = files with FP = FN = 0 for both
categories (identical to byte-equal HRD against `GOD.json`).

| tool | TP raw | TP adj | FP | FN | P | R | F1 | P raw | R raw | perfect files |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| RMD | 596954 | 49531 | 140 | 315 | 0.9972 | 0.9937 | 0.9954 | 0.9998 | 0.9995 | 881 |
| GTS | 596209 | 48786 | 761 | 1060 | 0.9846 | 0.9787 | 0.9817 | 0.9987 | 0.9982 | 649 |
| DFT_TED | 596286 | 48863 | 1627 | 983 | 0.9678 | 0.9803 | 0.9740 | 0.9973 | 0.9984 | 604 |
| DFT_TD | 595302 | 47879 | 1686 | 1967 | 0.9660 | 0.9605 | 0.9633 | 0.9972 | 0.9967 | 449 |
| GTG | 593909 | 46486 | 1137 | 3360 | 0.9761 | 0.9326 | 0.9539 | 0.9981 | 0.9944 | 209 |

Split by category (adjusted):

| tool | abstract mappings P / R | program elements P / R |
| --- | --- | --- |
| RMD | 0.9970 / 0.9933 | 1.0000 / 1.0000 |
| GTS | 0.9841 / 0.9784 | 0.9944 / 0.9856 |
| DFT_TED | 0.9663 / 0.9798 | 0.9956 / 0.9892 |
| DFT_TD | 0.9647 / 0.9592 | 0.9908 / 0.9856 |
| GTG | 0.9751 / 0.9306 | 0.9943 / 0.9704 |

Reading: difffold-ted is third behind RM and GumTree simple on F1 and perfect files (604 vs 649), ahead of GumTree greedy
(209 perfect files) and tied with GumTree simple on recall. difffold-topdown is between GumTree greedy and simple on
F1. difffold is behind GumTree simple on precision (0.966 vs 0.985). `INTRA_FILE_ONLY` filter results are in
`summary-INTRA_FILE_ONLY.csv` and differ by at most a few mappings (4 oracle files have inter-file mappings).

Mean wall time per file (includes spawning the Rust binary, the JDT conversion and HRD rendering; 3 parallel workers on 4
cores, so indicative only): RMD 9 ms, GTS 21 ms, DFT_TD 59 ms, GTG 497 ms, DFT_TED 817 ms (max 26 s on one file).

Context only, not comparable: the paper's published RefOracle aggregate with the same formulas is in
`results/diffbenchmark/published-reforacle-aggregate.csv` (for example GTG P 0.833 / R 0.687, GTS 0.857 / 0.709,
IAM_T 0.935 / 0.791 over 285 files). The Defects4J oracle is much easier (small bug fixes) and closer to RM's output.

## Byte range to JDT conversion

difffold works on tree-sitter trees; DiffBenchmark scores mappings between the JDT trees RefactoringMiner builds. The
binary `src/bin/ted_map.rs` prints matched pairs as UTF-8 byte ranges and tree-sitter kinds, plus the range of every node of
both trees. The adapter (`DifffoldMatcher`, a GumTree `Matcher` so it plugs into `BaseGumTreeASTDiffProvider`) converts:

1. Byte offsets become char offsets (JDT positions are char indices).
2. Each range is looked up in the JDT tree as the chain of nodes with exactly that `[pos, endPos)`. If none exists, nodes
   differing only by a leading Javadoc or comment are accepted (tree-sitter keeps comments outside declarations, JDT puts
   the Javadoc inside the declaration range).
3. Every JDT node type present in both chains is mapped, k-th occurrence to k-th, so a same-range wrapper like
   `SimpleType` over `SimpleName` is mapped on both levels. Only same-type pairs are produced: GumTree requires equal
   types, and the oracle contains no cross-type mapping (checked over all 597k oracle mappings). A pair whose chains share
   no type is dropped and counted as `crossType`. tree-sitter kinds are not consulted; range and JDT type decide.
4. Completion: RefactoringMiner's trees contain wrapper nodes no tree-sitter node can address (for example
   `METHOD_INVOCATION_ARGUMENTS`, `TYPE_DECLARATION_KIND`). Under each mapped pair, unmapped children with no tree-sitter
   node of the same range are paired by type and order, top-down. This mirrors the parent rules in DiffBenchmark's own
   translators (`ParentWithSameOffset`, `FirstChildOfType*`). Addressable nodes are never touched by this step.

Without step 4 the HRD marks every child of an unmapped wrapper as moved, which is scored as a false positive. Ablation
(`-Ddifffold.nocomplete=true`, `results/diffbenchmark/ablation-no-completion/`): DFT_TD FP rises from 1686 to 117319 and
adjusted precision drops from 0.966 to 0.286; DFT_TED from 1627 to 117668 (0.968 to 0.289). Recall barely moves. So the
reported difffold numbers depend on this step; it is the adapter's analogue of what the benchmark does for foreign tools.

Loss (`conversion-total.csv`, 4.75M pairs for topdown, 4.76M for ted):

| outcome | topdown | ted |
| --- | --- | --- |
| converted to at least one JDT mapping | 2394848 (50.4%) | 2400573 (50.4%) |
| no JDT node at one of the ranges (punctuation, `argument_list`, other tree-sitter only nodes) | 2356755 (49.6%) | 2360252 (49.6%) |
| both ranges have JDT nodes but no shared type | 2042 (0.04%) | 641 (0.01%) |
| conflict with an earlier mapping | 0 | 0 |
| JDT nodes mapped by completion | 52307 | 52453 |

The `noJdtNode` pairs are not an accuracy loss in themselves: JDT has no node for `;`, `(`, `.` and similar tokens. The
real loss measure is the ceiling run (`conversion-ceiling.csv`): each fixture's before file against itself plus a trailing
comment maps 2,619,494 of 2,619,560 JDT nodes (99.9975%). All 66 misses are `EnumConstantDeclaration`. In the real diffs,
99.5% (topdown) and 99.7% (ted) of before-side JDT nodes end up mapped, the rest being genuine deletions or disagreements.
The 2042 / 641 cross-type drops are tree-sitter relabels (ted) or top-down updates across kinds that JDT types would not
allow; they can cost recall.

## Caveats

- The task said DiffBenchmark was built. It was not: `libs/*.jar` (IJM, MTDiff, RM 2.2, iAST, Spoon) are absent from the
  checkout and the gradle build cannot run. RefactoringMiner 3.1.6 (in `rmlibs`) has an incompatible `Constants` API, so
  RefactoringMiner 3.0.10 from Maven Central (closest release to the 3.0.10-SNAPSHOT the code targets) is used, compiled with
  plain `javac` against DiffBenchmark's unmodified benchmark/metrics sources. The registry is reduced (`lite/ASTDiffToolEnum.java`);
  tools needing the missing jars (IJM, MTD, GT2, IAM, Spoon, RM 2.0) were not run. Their only available numbers are the
  published RefOracle ones, a different oracle.
- RM 3.0.10 vs the paper's RM: oracle agreement of RMD is 881/996 perfect files, not 996.
- `ignored` (trivial mappings) is recomputed over this five-tool set, so adjusted P, R, F1 shift if the set changes; raw
  columns do not.
- The oracle derives from RM output, so RM-like decisions score better by construction.
- Defects4J only. RefOracle (the paper's headline experiment) was not rerun, so there is no like-for-like comparison with
  IJM, GT2, IAM, Spoon.
- Each bug is one RM case with all of its changed files; difffold maps each file pair independently (it has no inter-file
  mode), which is why 4 inter-file oracle mappings count as misses.
- difffold labels are tree-sitter kinds and token text, so renames inside identifiers are label mismatches. No tuning for
  this benchmark was done.
- The patch file targets upstream `ASTDiffToolEnum` (adds `DFT_TD`, `DFT_TED`); it applies cleanly to the pristine tree but
  was not compiled against the full upstream dependency set (missing jars). The compiled variant is the `lite` enum.

## Reproduce

```
export CARGO_TARGET_DIR=/tmp/dfb-tgt
DFB=/path/to/DiffBenchmark \
FIXTURES=/path/to/omnidiff-apeiron/src/test/data/diffs/defects4j \
WORK=/tmp/dfb-work THREADS=3 \
  tools/diffbenchmark_adapter/run.sh
```

`run.sh` builds `ted_map` (`cargo build --release --features ts --bin ted_map`), fetches RM 3.0.10 with maven
(`rm-deps/pom.xml`), compiles the patched sources with `javac`, runs `rq.difffold.D4JAccuracyDriver` and then
`rq.difffold.ConversionCeiling`. For the 996-file run the driver was invoked in four sequential shards
(`--shard i/4`, `-Xmx4g`, 3 threads) because a single 8 GB JVM was OOM-killed at bug 760 of 800; outputs are append-only and
resumable (`done.txt`). Ablation: add `-Ddifffold.nocomplete=true --tools DFT_TD,DFT_TED`. The upstream patch is regenerated
with `DFB=... tools/diffbenchmark_adapter/make_patch.sh`.

## Files

- `tools/diffbenchmark_adapter/`: `src/` (adapter and drivers), `lite/ASTDiffToolEnum.java`, `diffbenchmark-difffold.patch`,
  `run.sh`, `make_patch.sh`, `rm-deps/pom.xml`.
- `src/bin/ted_map.rs` and its `[[bin]]` entry in `Cargo.toml`.
- `results/diffbenchmark/`: `summary-*.csv` (aggregates above), `d4j-*.csv` (DiffBenchmark-native per-file rows),
  `records-*.csv` (per file and tool counts), `timings.csv`, `failures.csv` (empty), `conversion-total.csv`,
  `conversion-ceiling.csv`, `published-reforacle-aggregate.csv`, `ablation-no-completion/`.
