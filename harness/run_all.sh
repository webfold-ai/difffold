#!/usr/bin/env bash
# Standalone driver for the difffold comparison harness. Works without spbench.
#
#   ./run_all.sh [--sample N] [--slowest N] [--seed S] [--all] [--all-langs] [--max-reps R]
#                [--timeout S] [--tools a,b,c] [--tag NAME] [--no-build]
#
# Defaults select the Java/Go/C fixtures: --slowest 50 plus --sample 300 (seed 1).
# Environment overrides (all have defaults for this machine):
#   DIFFS BASELINE OMNI OMNI_SRC APTED_WORKER GUMTREE WORK TOOLS_DIR
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
SCR=${SCR:-/tmp/claude-0/-home-user/4463fc2d-0ca5-5c92-8549-159b74884cf3/scratchpad/harness}
DIFFS=${DIFFS:-/home/user/omnidiff-apeiron/src/test/data/diffs}
BASELINE=${BASELINE:-$SCR/../baseline.csv}
OMNI=${OMNI:-/home/user/target-omni/ci/omnidiff}
OMNI_SRC=${OMNI_SRC:-/home/user/omnidiff-apeiron}
APTED_WORKER=${APTED_WORKER:-$SCR/apted-target/ci/apted_only_worker}
GUMTREE_VER=${GUMTREE_VER:-4.0.0-beta4}
GUMTREE=${GUMTREE:-$SCR/gt-x/gumtree-$GUMTREE_VER/bin/gumtree}
DFT_VER=${DFT_VER:-0.64.0}
DIFFSITTER=${DIFFSITTER:-}
TOOLS_DIR=${TOOLS_DIR:-$SCR}
DFT=${DFT:-$TOOLS_DIR/dft/bin/difft}
WORK=${WORK:-$SCR/work}
RES=$here/results

SAMPLE=300 SLOWEST=50 SEED=1 ALL=0 ALLLANGS=0 REPS=5 TMO=60 ONLY="" TAG="" BUILD=1
while [[ $# -gt 0 ]]; do
  case $1 in
    --sample) SAMPLE=$2; shift 2;; --slowest) SLOWEST=$2; shift 2;; --seed) SEED=$2; shift 2;;
    --all) ALL=1; shift;; --all-langs) ALLLANGS=1; shift;; --max-reps) REPS=$2; shift 2;;
    --timeout) TMO=$2; shift 2;; --tools) ONLY=$2; shift 2;; --tag) TAG=$2; shift 2;;
    --no-build) BUILD=0; shift;; *) echo "unknown arg $1" >&2; exit 2;;
  esac
done
mkdir -p "$RES" "$WORK"
TAG=${TAG:-run}
CLI=$here/rust/target/release/dfold-cli
BENCH=$here/rust/target/release/cli_bench

if [[ $BUILD == 1 ]]; then
  cargo build --release -j2 --manifest-path "$here/rust/Cargo.toml"
  if [[ ! -x $DFT ]]; then
    cargo install difftastic --locked --version "$DFT_VER" --root "$(dirname "$(dirname "$DFT")")" -j2
  fi
fi

# Machine and tool pins.
{
  echo "date: $(date -u +%FT%TZ)"
  echo "nproc: $(nproc)"
  echo "cpu: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ //')"
  echo "mem_total_kb: $(awk '/MemTotal/{print $2}' /proc/meminfo)"
  echo "kernel: $(uname -srv)"
  echo "loadavg_at_start: $(cat /proc/loadavg)"
  echo "rustc: $(rustc -V)"
  echo "cargo_profile: release (opt-level 3, debug=1, no LTO), -j2 builds"
  echo "git: $(git --version)"
  echo "java: $(java -version 2>&1 | grep -v JAVA_TOOL | head -1)"
  echo "difftastic: $($DFT --version | head -1) (cargo install --locked --version $DFT_VER)"
  echo "omnidiff: $($OMNI --version) src_head=$(git -C "$OMNI_SRC" rev-parse --short HEAD 2>/dev/null || echo unknown) profile=ci (release, no LTO, 16 CGUs)"
  echo "gumtree: $GUMTREE_VER (GitHub release zip, matcher gumtree-simple default, generators by extension: java-jdt, go-treesitter-ng, c-treesitter-ng)"
  echo "difffold_src_head: $(git -C "$here/.." rev-parse --short HEAD 2>/dev/null || echo unknown)"
  echo "tree-sitter crates: $(grep -A1 -E '^name = "tree-sitter(-java|-go|-c)?"$' "$here/rust/Cargo.lock" | grep -E 'name|version' | paste -sd' ' | sed 's/name = //g;s/version = //g')"
  echo "apeiron: $(grep -A2 'name = "apeiron"' "$here/rust/Cargo.lock" | grep source)"
  echo "threads: all tools single-threaded except the JVM (GC and JIT threads) and difft (rayon, default); no taskset"
  echo "limits: 60 s wall per run (SIGKILL); apted worker under prlimit --as=8GiB; zs gated at n*m>25e6 nodes; dfold-cli internal 55 s deadline"
  echo "cost_model: git/difft/gumtree/omnidiff own models; difffold and selkow unit cost per node (top-down); zs unit ins/del/relabel (general TED); apted: omnidiff's rename-cost model"
  echo "input_representation: tree-sitter CST incl. anonymous tokens, leaf label = (kind, text), inner label = kind (difffold, selkow, zs); omnidiff/apted use omnidiff's own Code trees; difft its own syntax tree; gumtree its own generators"
} > "$RES/machine.txt"

# Fixture manifest.
SEL=(--diffs "$DIFFS" --baseline "$BASELINE" --work "$WORK" --out "$RES/manifest-$TAG.tsv" --seed "$SEED")
[[ $ALL == 0 ]] && SEL+=(--sample "$SAMPLE" --slowest "$SLOWEST")
[[ $ALLLANGS == 1 ]] && SEL+=(--all-langs)
python3 -I "$here/select_fixtures.py" "${SEL[@]}"

# Tool table. Columns: name, objective, langs, ok exit codes, fallback marker, keep stdout line,
# env (; separated, ROUNDS=n caps repetitions), command with {B} {A}.
T=$RES/tools-$TAG.tsv
tab() { local IFS=$'\t'; echo "$*"; }
{
  for alg in myers patience histogram minimal; do
    tab "git-$alg" "line-based (text)" "*" "0,1" "" 0 "GIT_CONFIG_GLOBAL=/dev/null;GIT_CONFIG_SYSTEM=/dev/null" "git --no-pager diff --no-index --no-color --diff-algorithm=$alg {B} {A}"
  done
  tab difftastic "syntax graph shortest-path (own)" "*" "0" '"language":"Text' 0 "DFT_UNSTABLE=yes" "$DFT --display json --color never --byte-limit 1000000 --graph-limit 3000000 {B} {A}"
  if [[ -n $DIFFSITTER && -x $DIFFSITTER ]]; then
    tab diffsitter "AST node diff (tree-sitter and own)" "java,go,c" "0,1" "" 0 "" "$DIFFSITTER {B} {A}"
  fi
  tab omnidiff "heuristic matching + APTED on residual (own)" "*" "0" '"large_residual": true' 0 "" "$OMNI --mode json {B} {A}"
  tab difffold "top-down Selkow (exact)" "java,go,c" "0" "" 1 "" "$CLI --algo difffold {B} {A}"
  tab difffold-distance "top-down Selkow (exact)" "java,go,c" "0" "" 1 "" "$CLI --algo difffold-distance {B} {A}"
  tab difffold-refine "top-down + cross-level refinement" "java,go,c" "0" "" 1 "" "$CLI --algo difffold-refine {B} {A}"
  tab difffold-hot "top-down Selkow (exact)" "java,go,c" "0" "" 1 "ROUNDS=2" "$CLI --algo difffold --reps 7 {B} {A}"
  tab difffold-refine-hot "top-down + cross-level refinement" "java,go,c" "0" "" 1 "ROUNDS=2" "$CLI --algo difffold-refine --reps 7 {B} {A}"
  tab selkow-ref "top-down Selkow (plain DP)" "java,go,c" "0" "" 1 "ROUNDS=3" "$CLI --algo selkow --timeout-s 55 {B} {A}"
  tab zhang-shasha "general TED (promotes children)" "java,go,c" "0" "" 1 "ROUNDS=3" "$CLI --algo zs --timeout-s 55 --max-cells 25000000 {B} {A}"
  if [[ -x $APTED_WORKER ]]; then
    tab apted-omnidiff "general TED (APTED, omnidiff cost model)" "*" "0" "" 1 "ROUNDS=3" "prlimit --as=8589934592 -- $APTED_WORKER --before {B} --after {A} --lang-path {B}"
  fi
  if [[ -x $GUMTREE ]]; then
    tab gumtree "heuristic matching (gumtree-simple)" "java,go,c" "0" "" 0 "ROUNDS=3" "$GUMTREE textdiff {B} {A}"
  fi
} > "$T"
if [[ -n $ONLY ]]; then
  grep -E "^($(echo "$ONLY" | sed 's/,/|/g'))	" "$T" > "$T.f" && mv "$T.f" "$T"
fi

"$BENCH" --manifest "$RES/manifest-$TAG.tsv" --tools "$T" --out "$RES/cli-$TAG.csv" \
  --timeout-s "$TMO" --max-reps "$REPS" --seed "$SEED" --tmp "$SCR/bench-tmp"

python3 -I "$here/summarize.py" --cli "$RES/cli-$TAG.csv" --manifest "$RES/manifest-$TAG.tsv" \
  --machine "$RES/machine.txt" --out "$RES/SUMMARY.md" --ratios "$RES/ratios-$TAG.csv" --views "$RES/views-$TAG.csv"
