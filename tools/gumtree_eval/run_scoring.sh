#!/usr/bin/env bash
# usage: run_scoring.sh <work-dir> <eval-out-dir> <generator> <matcher> <score_accuracy-bin> <gt2map-bin> <sel-dir>
# Converts GumTree/RM dumps for one (generator, matcher) to .map files and scores them with score_accuracy.
set -euo pipefail
W=$1; O=$2; G=$3; M=$4; SA=$5; G2M=$6; SEL=$7
D=$W/scored/$G/$M
rm -rf "$D"; mkdir -p "$D"
"$G2M" "$SEL" "$O/$G" "$M" "$D/raw-maps" "$D/scoped-maps"
"$SA" "$SEL" "$D/raw-maps" "$D/raw" >/dev/null 2>"$D/raw.log" || true
"$SA" "$SEL" "$D/scoped-maps" "$D/scoped" >/dev/null 2>"$D/scoped.log" || true
rm -rf "$D/raw-maps/"*.map "$D/scoped-maps/"*.map
