#!/usr/bin/env bash
# Regenerates every file under results/accuracy/ (except previous-fork-run/ and gumtree/) from the OmniDiff corpus.
# usage: accuracy.sh DIFFS OMNI_DUMP_DIR SCORE_ACCURACY_BIN [OMNIDIFF_CHECKOUT]
#   DIFFS            OmniDiff's src/test/data/diffs
#   OMNI_DUMP_DIR    output of tools/omni_dump on DIFFS (OmniDiff's own mappings)
#   SCORE_ACCURACY   cargo build --release --features ts --bin score_accuracy
# The scorer is deterministic; nothing here is timing-sensitive.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
D=$1; DUMP=$2; B=$3; OMNI=${4:-}
R=$here/results/accuracy
mkdir -p "$R"/{topdown,split-dev,split-test,ablation,sweeps}
cp_tables() { cp "$1"/*.csv "$1"/summary_tables.md "$2"/; }
tmp=$(mktemp -d)
mkdir -p "$tmp"/{topdown,full,dev,test}
nice -n 10 "$B" "$D" "$DUMP" "$tmp/topdown" >/dev/null 2>&1
DFOLD_REFINE=full nice -n 10 "$B" "$D" "$DUMP" "$tmp/full" >/dev/null 2>&1
DFOLD_SPLIT=dev DFOLD_REFINE=full nice -n 10 "$B" "$D" "$DUMP" "$tmp/dev" >/dev/null 2>&1
DFOLD_SPLIT=test DFOLD_REFINE=full nice -n 10 "$B" "$D" "$DUMP" "$tmp/test" >/dev/null 2>&1
cp_tables "$tmp/full" "$R"; cp_tables "$tmp/topdown" "$R/topdown"; cp_tables "$tmp/dev" "$R/split-dev"; cp_tables "$tmp/test" "$R/split-test"
for spec in seed exact exact,validate exact,validate,containers exact,validate,containers,recover \
            exact,validate,containers,recover,descend exact,validate,containers,recover,descend,retarget; do
  name=$(echo "$spec" | tr ',' '+'); mkdir -p "$tmp/abl" "$R/ablation/$name"
  DFOLD_REFINE=$spec nice -n 10 "$B" "$D" - "$tmp/abl" >/dev/null 2>&1
  cp "$tmp/abl/SUMMARY-difffold-only.md" "$tmp/abl/accuracy-difffold-only.csv" "$R/ablation/$name/"
done
python3 -I "$here/harness/bootstrap_ci.py" "$R/fixtures.csv" --baseline "$R/topdown/fixtures.csv" --n 10000 --seed 1 --out "$R/ci.md" >/dev/null
"$here/harness/record_machine.sh" "$R/machine.txt" "$OMNI" 
rm -rf "$tmp"
echo "results/accuracy regenerated; run harness/dev_sweep.sh separately for sweeps/dev-sweep.tsv"
