#!/usr/bin/env bash
# Runs X-TED CPU with a given thread count on every tree pair and appends the rows to OUTCSV.
#
#   run_xted_threads.sh TREES BIN OUTCSV THREADS
#
# The process is pinned to cores 0 to THREADS-1, so the thread count and the core count match. Each run is
# capped at 75 s by timeout, and the adapter prints a gt60s row for any run past 60 s.
set -euo pipefail
TREES="$1"
BIN="$2"
OUTCSV="$3"
THREADS="$4"
CORES="0-$((THREADS - 1))"
[ -x "$BIN/xted_adapter" ] || { echo "missing $BIN/xted_adapter" >&2; exit 2; }
[ -f "$OUTCSV" ] || echo "tool,mode,pair,phase,rep,us,distance,status" > "$OUTCSV"
export LC_ALL=C

for kind in real syn; do
  for dir in "$TREES/$kind"/*/; do
    pair=$(basename "$dir")
    echo "[$(date +%T)] xted threads=$THREADS $pair" >&2
    timeout 75 taskset -c "$CORES" "$BIN/xted_adapter" --mode unknown --threads "$THREADS" --reps 7 \
      --pair "$pair" "$dir/a.tree" "$dir/b.tree" >> "$OUTCSV" || echo "$pair,killed-or-error:$?" >> "$OUTCSV.errors"
  done
done
echo "[$(date +%T)] done" >&2
