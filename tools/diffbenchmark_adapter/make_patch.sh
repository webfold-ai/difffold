#!/usr/bin/env bash
# Regenerates diffbenchmark-difffold.patch against a pristine DiffBenchmark checkout ($DFB).
# The patch registers DFT_TD and DFT_TED in ASTDiffToolEnum and adds the adapter and drivers.
# Apply with: cd $DFB && patch -p1 < diffbenchmark-difffold.patch
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${DFB:?}"
T="$(mktemp -d)"
mkdir -p "$T/a/src/main/java/benchmark/generators/tools" "$T/b/src/main/java"
cp "$DFB/src/main/java/benchmark/generators/tools/ASTDiffToolEnum.java" "$T/a/src/main/java/benchmark/generators/tools/"
cp -r "$HERE"/src/* "$T/b/src/main/java/"
cp "$T/a/src/main/java/benchmark/generators/tools/ASTDiffToolEnum.java" "$T/b/src/main/java/benchmark/generators/tools/"
python3 - "$T/b/src/main/java/benchmark/generators/tools/ASTDiffToolEnum.java" <<'PY'
import sys
p = sys.argv[1]
s = open(p).read()
s = s.replace("import benchmark.generators.tools.runners.extensions.combined.ModifierInterConservativeMulti;",
  "import benchmark.generators.tools.runners.difffold.DifffoldASTDiffProvider;\nimport benchmark.generators.tools.runners.extensions.combined.ModifierInterConservativeMulti;", 1)
s = s.replace('    SPN_I("Original Spoon (Incompatible)", Spoon::new),',
  '    DFT_TD("difffold top-down", (benchmarkCase, query) -> new DifffoldASTDiffProvider("topdown", benchmarkCase, query)),\n\n'
  '    DFT_TED("difffold tree edit distance", (benchmarkCase, query) -> new DifffoldASTDiffProvider("ted", benchmarkCase, query)),\n\n'
  '    DFT_RF("difffold top-down + cross-level refinement", (benchmarkCase, query) -> new DifffoldASTDiffProvider("refine", benchmarkCase, query)),\n\n'
  '    SPN_I("Original Spoon (Incompatible)", Spoon::new),', 1)
open(p, "w").write(s)
PY
(cd "$T" && diff -ruN a b > "$HERE/diffbenchmark-difffold.patch") || true
rm -rf "$T"
