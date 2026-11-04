#!/usr/bin/env bash
# Stage 3 of the chain and the proofs over the extracted code.
#   LEAN_WS=/path/to/aeneas/backends/lean-with-mathlib-cache ./check-kernel.sh Defs Trim ...
# Needs: Lean 4.31.0 on PATH, a Lake workspace (a copy of Aeneas's backends/lean) where
# `lake exe cache get` and `lake build Aeneas` have run, and gen/lean/DifffoldKernel.lean from extract.sh.
# Each named module Kernel/<Name>.lean is compiled to build-kernel/<Name>.olean in the order given,
# so later modules can import earlier ones. The model modules (Difffold/*.lean, plain Lean) are
# compiled to build-model/ when missing.
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_WS:?set LEAN_WS}"
HERE=$PWD; B=$HERE/build-kernel; M=$HERE/build-model; mkdir -p "$B" "$M/Difffold"
( cd "$LEAN_WS"
  for m in Basic Prune Decision Link Strip; do
    [ -f "$M/Difffold/$m.olean" ] && [ "$M/Difffold/$m.olean" -nt "$HERE/Difffold/$m.lean" ] ||
      lake env bash -c "LEAN_PATH=\$LEAN_PATH:$M lean --root=$HERE -o $M/Difffold/$m.olean $HERE/Difffold/$m.lean" >/dev/null
  done
  # Stage 3: the Lean kernel elaborates the Aeneas output.
  lake env lean --root="$HERE/gen/lean" -o "$B/DifffoldKernel.olean" "$HERE/gen/lean/DifffoldKernel.lean"
  echo "stage 3 ok: DifffoldKernel.lean sha256 $(sha256sum "$HERE/gen/lean/DifffoldKernel.lean" | cut -d' ' -f1)"
  for f in "$@"; do
    echo "== $f"
    lake env bash -c "LEAN_PATH=\$LEAN_PATH:$B:$M timeout ${LEAN_TIMEOUT:-300} lean -DmaxHeartbeats=${HEARTBEATS:-400000} --root=$HERE/Kernel -o $B/$f.olean $HERE/Kernel/$f.lean"
  done )
