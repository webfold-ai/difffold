#!/usr/bin/env bash
# Build all Difffold modules with plain `lean` (no Mathlib, no lake). Usage: source env.sh; ./build.sh
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build/Difffold
export LEAN_PATH="$PWD/build:${LEAN_PATH:-}"
for m in "$@"; do
  echo "== $m"; lean -o build/Difffold/$m.olean Difffold/$m.lean
done
