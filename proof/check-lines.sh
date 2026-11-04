#!/usr/bin/env bash
# Stage 3 and the proofs for the lines/ted extraction (gen/lean-lines, gen/lean-ted).
#   LEAN_WS=/path/to/aeneas/backends/lean-with-mathlib-cache ./check-lines.sh [--gen] Common FirstNl ...
# --gen also elaborates gen/lean-ted/DifffoldTed.lean (known to fail, see README). Each named module
# Lines/<Name>.lean is compiled to build-lines/<Name>.olean in the order given.
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_WS:?set LEAN_WS}"
HERE=$PWD; B=$HERE/build-lines; mkdir -p "$B"
GEN=0; if [ "${1:-}" = "--gen" ]; then GEN=1; shift; fi
( cd "$LEAN_WS"
  lake env lean --root="$HERE/gen/lean-lines" -o "$B/DifffoldLines.olean" "$HERE/gen/lean-lines/DifffoldLines.lean"
  echo "stage 3 ok: DifffoldLines.lean sha256 $(sha256sum "$HERE/gen/lean-lines/DifffoldLines.lean" | cut -d' ' -f1)"
  if [ $GEN = 1 ]; then
    lake env lean --root="$HERE/gen/lean-ted" -o "$B/DifffoldTed.olean" "$HERE/gen/lean-ted/DifffoldTed.lean"
    echo "stage 3 ok: DifffoldTed.lean sha256 $(sha256sum "$HERE/gen/lean-ted/DifffoldTed.lean" | cut -d' ' -f1)"
  fi
  for f in "$@"; do
    echo "== $f"
    lake env bash -c "LEAN_PATH=\$LEAN_PATH:$B timeout ${LEAN_TIMEOUT:-300} lean -DmaxHeartbeats=${HEARTBEATS:-400000} --root=$HERE/Lines -o $B/$f.olean $HERE/Lines/$f.lean"
  done )
