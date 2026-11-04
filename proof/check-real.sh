#!/usr/bin/env bash
# Stage 3 for the Myers extraction: elaborate gen/lean-real/DifffoldReal.lean, then the proof files
# named (Lines/<Name>.lean style, here Myers2/<Name>.lean) into build-myers/.
#   LEAN_WS=/path/to/aeneas/backends/lean ./check-myers.sh [Name ...]
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_WS:?set LEAN_WS}"
HERE=$PWD; B=$HERE/build-myers; mkdir -p "$B"
( cd "$LEAN_WS"
  lake env lean --root="$HERE/gen/lean-real" -o "$B/DifffoldReal.olean" "$HERE/gen/lean-real/DifffoldReal.lean"
  echo "stage 3 ok: DifffoldReal.lean sha256 $(sha256sum "$HERE/gen/lean-real/DifffoldReal.lean" | cut -d' ' -f1)"
  for f in "$@"; do
    echo "== $f"
    lake env bash -c "LEAN_PATH=\$LEAN_PATH:$B timeout ${LEAN_TIMEOUT:-300} lean -DmaxHeartbeats=${HEARTBEATS:-400000} --root=$HERE/Myers2 -o $B/$f.olean $HERE/Myers2/$f.lean"
  done )
