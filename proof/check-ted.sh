#!/usr/bin/env bash
# Stage 3 and the proofs for the ted extraction (gen/lean-ted/DifffoldTed.lean, from extract/ted_core.rs).
#   LEAN_WS=/path/to/aeneas/backends/lean ./check-ted.sh Basic Lml ...
# Needs Lean 4.31.0 on PATH and a Lake workspace with the Aeneas library built (stock release, not
# apeiron's patched build). Elaborates the generated file, then compiles each Ted/<Name>.lean to
# build-ted/<Name>.olean in the order given, so later modules can import earlier ones.
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_WS:?set LEAN_WS}"
HERE=$PWD; B=$HERE/build-ted; mkdir -p "$B"
( cd "$LEAN_WS"
  lake env lean --root="$HERE/gen/lean-ted" -o "$B/DifffoldTed.olean" "$HERE/gen/lean-ted/DifffoldTed.lean"
  echo "stage 3 ok: DifffoldTed.lean sha256 $(sha256sum "$HERE/gen/lean-ted/DifffoldTed.lean" | cut -d' ' -f1)"
  for f in "$@"; do
    echo "== $f"
    lake env bash -c "LEAN_PATH=\$LEAN_PATH:$B timeout ${LEAN_TIMEOUT:-600} lean -DmaxHeartbeats=${HEARTBEATS:-400000} --root=$HERE/Ted -o $B/$f.olean $HERE/Ted/$f.lean"
  done )
