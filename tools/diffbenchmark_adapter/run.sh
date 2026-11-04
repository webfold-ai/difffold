#!/usr/bin/env bash
# Builds difffold's ted_map, builds a reduced DiffBenchmark with the difffold adapter, and scores
# difffold, GumTree and RefactoringMiner on DiffBenchmark's Defects4J oracle.
#
# Required environment:
#   DFB        DiffBenchmark checkout (provides hrd-oracle/adb-paper/d4j-exp and the benchmark sources)
#   FIXTURES   OmniDiff Defects4J fixtures (omnidiff-apeiron/src/test/data/diffs/defects4j)
#   WORK       scratch directory for build products and outputs
# Optional: TOOLS (default RMD,GTG,GTS,DFT_TD,DFT_TED), THREADS (3), LIMIT (0 = all bugs),
#           TIMEOUT (seconds per difffold call, 120), CARGO_TARGET_DIR.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
: "${DFB:?}" "${FIXTURES:?}" "${WORK:?}"
TOOLS="${TOOLS:-RMD,GTG,GTS,DFT_TD,DFT_TED}"
THREADS="${THREADS:-3}"
LIMIT="${LIMIT:-0}"
TIMEOUT="${TIMEOUT:-120}"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$WORK/cargo-target}"
mkdir -p "$WORK"

# 1. difffold mapping binary.
(cd "$REPO" && cargo build --release --features ts --bin ted_map)
TED_MAP="$CARGO_TARGET_DIR/release/ted_map"

# 2. RefactoringMiner 3.0.10 and its dependencies (the release closest to the 3.0.10-SNAPSHOT the
#    benchmark was written against; 3.1.x changed the Constants API).
if [ ! -d "$WORK/rmlibs" ]; then
  mvn -q -B -f "$HERE/rm-deps/pom.xml" -Dmaven.repo.local="$WORK/m2" dependency:copy-dependencies -DoutputDirectory="$WORK/rmlibs"
  rm -f "$WORK"/rmlibs/slf4j-simple-*.jar
  rm -rf "$WORK/m2"
fi
CP="$(ls "$WORK"/rmlibs/*.jar | tr '\n' ':')"

# 3. Patched sources: upstream sources, the adapter, and the reduced tool registry (lite/), which
#    drops tools whose jars (IJM, MTDiff, GumTree 2.0, IASTMapper, RM 2.0, Spoon) are not shipped.
rm -rf "$WORK/src" "$WORK/classes"
mkdir -p "$WORK/classes"
cp -r "$DFB/src/main/java" "$WORK/src"
cp -r "$HERE"/src/* "$WORK/src/"
cp "$HERE/lite/ASTDiffToolEnum.java" "$WORK/src/benchmark/generators/tools/ASTDiffToolEnum.java"
javac -nowarn -proc:none -d "$WORK/classes" -cp "$CP" -sourcepath "$WORK/src" \
  "$WORK/src/rq/difffold/D4JAccuracyDriver.java" "$WORK/src/rq/difffold/ConversionCeiling.java"

# 4. Accuracy experiment on the Defects4J oracle.
java -Xmx8g -cp "$WORK/classes:$CP" -Ddifffold.bin="$TED_MAP" -Ddifffold.timeout="$TIMEOUT" \
  rq.difffold.D4JAccuracyDriver --oracle "$DFB/hrd-oracle/adb-paper/d4j-exp" --fixtures "$FIXTURES" \
  --out "$WORK/out" --tools "$TOOLS" --threads "$THREADS" --limit "$LIMIT"

# 5. Conversion ceiling (before file against itself).
java -Xmx4g -cp "$WORK/classes:$CP" -Ddifffold.bin="$TED_MAP" rq.difffold.ConversionCeiling "$FIXTURES" "$WORK/out/conversion-ceiling.csv"
