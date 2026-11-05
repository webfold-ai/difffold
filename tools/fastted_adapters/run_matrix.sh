#!/usr/bin/env bash
# Runs every tool on every tree pair and appends the raw CSV rows to OUTCSV.
#
#   run_matrix.sh TREES BIN OUTCSV
#
# TREES holds real/<pair>/{a,b}.tree and syn/<pair>/{a,b}.tree. BIN holds fastted_bench (built by cargo) and
# tsim_adapter and xted_adapter (built by build.sh). Every run is pinned with taskset to core 0.
#
# Modes:
#   unknown    the tool searches the threshold itself.
#   threshold  the tool gets tau = the exact difffold distance for the pair. That tau is a tight bound, so its
#              acquisition cost is charged in aggregate.py (the median difffold unknown-mode distance time).
#              APTED and X-TED have no threshold entry point and are not run in threshold mode.
#
# A cell that exceeds 60 s on any run stops after that run with status gt60s. The outer 75 s timeout kills a
# run that is still going past 60 s, so a single slow run cannot hold the matrix. Killed cells leave partial rows
# and aggregate.py reports them as skipped.
set -euo pipefail
TREES="$1"
BIN="$2"
OUTCSV="$3"
HDR="tool,mode,pair,phase,rep,us,distance,status"
[ -f "$OUTCSV" ] || echo "$HDR" > "$OUTCSV"
export LC_ALL=C
for bin in fastted_bench tsim_adapter xted_adapter; do
  [ -x "$BIN/$bin" ] || { echo "missing $BIN/$bin" >&2; exit 2; }
done

for kind in real syn; do
  for dir in "$TREES/$kind"/*/; do
    pair=$(basename "$dir")
    a="$dir/a.tree"
    b="$dir/b.tree"
    # Resume: a pair counts as complete once its touzet_dp threshold cell has rows, because X-TED cells may be killed
    # by the timeout and leave no rows. Partial rows for the other pairs are dropped before rerunning them.
    if grep -q "^touzet_dp,threshold,$pair," "$OUTCSV"; then
      echo "[$(date +%T)] $pair already complete" >&2
      continue
    fi
    if grep -q ",$pair," "$OUTCSV"; then
      grep -v ",$pair," "$OUTCSV" > "$OUTCSV.tmp" && mv "$OUTCSV.tmp" "$OUTCSV"
    fi
    echo "[$(date +%T)] $pair" >&2

    # difffold, unknown mode. Its distance is the reference for every other tool on this pair.
    tmp=$(mktemp)
    timeout 75 taskset -c 0 "$BIN/fastted_bench" --pair "$pair" --mode unknown --reps 7 "$a" "$b" > "$tmp" || true
    cat "$tmp" >> "$OUTCSV"
    tau=$(awk -F, '$4=="dist" && $8=="ok" {print $7; exit}' "$tmp")
    if [ -z "$tau" ]; then
      echo "  difffold produced no distance for $pair; skipping its cells" >&2
      rm -f "$tmp"
      continue
    fi
    rm -f "$tmp"

    run() {
      timeout 75 taskset -c 0 "$@" >> "$OUTCSV" || echo "$pair,killed-or-error:$?" >> "$OUTCSV.errors"
    }

    # difffold, threshold mode with tau = the reference distance (bound cost charged in aggregate.py).
    run "$BIN/fastted_bench" --pair "$pair" --mode threshold --tau "$tau" --reps 7 "$a" "$b"

    run "$BIN/tsim_adapter" --tool apted --mode unknown --reps 7 --pair "$pair" "$a" "$b"
    run "$BIN/tsim_adapter" --tool touzet_baseline --mode unknown --reps 7 --pair "$pair" "$a" "$b"
    run "$BIN/tsim_adapter" --tool touzet_baseline --mode threshold --tau "$tau" --reps 7 --pair "$pair" "$a" "$b"
    run "$BIN/tsim_adapter" --tool touzet_krset --mode unknown --reps 7 --pair "$pair" "$a" "$b"
    run "$BIN/tsim_adapter" --tool touzet_krset --mode threshold --tau "$tau" --reps 7 --pair "$pair" "$a" "$b"
    run "$BIN/tsim_adapter" --tool touzet_dp --mode unknown --reps 7 --pair "$pair" "$a" "$b"
    run "$BIN/tsim_adapter" --tool touzet_dp --mode threshold --tau "$tau" --reps 7 --pair "$pair" "$a" "$b"
    run "$BIN/xted_adapter" --mode unknown --reps 7 --pair "$pair" "$a" "$b"
  done
done
echo "[$(date +%T)] done" >&2
