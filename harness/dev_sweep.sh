#!/usr/bin/env bash
# One-at-a-time parameter sweep of the refinement on the dev half of the OmniDiff fixtures.
# usage: dev_sweep.sh DIFFS SCORE_ACCURACY_BIN OUT.tsv
# Each row: parameter, value, then micro pair F1, changed-span P, R, F1, perfect fixtures (dev half only).
set -euo pipefail
D=$1; B=$2; OUT=$3
tmp=$(mktemp -d)
echo -e "param\tvalue\tpair_f1\tspan_p\tspan_r\tspan_f1\tperfect" > "$OUT"
run() { # param value env...
  local p=$1 v=$2; shift 2
  env "$@" DFOLD_SPLIT=dev DFOLD_REFINE=full "$B" "$D" - "$tmp" >/dev/null 2>&1
  grep -m1 '^| ALL | difffold | ' "$tmp/SUMMARY-difffold-only.md" |
    awk -F'|' -v p="$p" -v v="$v" '{gsub(/ /,"",$0); printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n", p, v, $8, $9, $10, $11, $12}' >> "$OUT"
}
run default - DFOLD_NONE=1
for v in 0.3 0.4 0.6 0.7; do run dice $v DFOLD_DICE=$v; done
for v in 0.2 0.4 0.5; do run keep $v DFOLD_KEEP=$v; done
for v in 2 3 4 5 6 8 12; do run anchor_below $v DFOLD_ANCHOR=$v; done
for v in 3 4 5; do run min_exact $v DFOLD_MINEXACT=$v; done
for v in 0 1 2 3 4 6 12; do run hops $v DFOLD_HOPS=$v; done
rm -rf "$tmp"
