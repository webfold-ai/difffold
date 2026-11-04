#!/usr/bin/env bash
# Compile proof/Myers/<Name>.lean files in the order given, with plain Lean 4.31.0 (core only, no Mathlib).
# Oleans go to proof/build-myers/ only.   usage: ./run-myers.sh Lcs Script ...
set -euo pipefail
cd "$(dirname "$0")"
S=${LEAN_SCRATCH:-/tmp/claude-0/-home-user/4463fc2d-0ca5-5c92-8549-159b74884cf3/scratchpad}
export PATH=$S/lean/tc/lean-4.31.0-linux/bin:$PATH
B=$PWD/build-myers; mkdir -p "$B"
export LEAN_PATH="$B:${LEAN_PATH:-}"
for f in "$@"; do
  echo "== $f"
  timeout "${T:-600}" lean -DmaxHeartbeats=${HB:-1000000} --root=$PWD/Myers -o "$B/$f.olean" "Myers/$f.lean"
done
