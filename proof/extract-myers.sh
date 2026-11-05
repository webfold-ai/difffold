#!/usr/bin/env bash
# Charon -> Aeneas extraction of the closure-free copies of the pure pieces of the line search
# (extract/myers_core.rs), separate outputs from extract-lines.sh:
#   gen/difffold_myers.llbc, gen/lean-myers/DifffoldMyers.lean, gen/RECEIPT-myers.txt.
#   AENEAS_HOME=/path/to/unpacked/release ./extract-myers.sh
# See extract.sh for the toolchain installation. The copies are tied to src/lines.rs by tests/myers_core.rs
# (random agreement), not by a proof.
set -euo pipefail
cd "$(dirname "$0")"
: "${AENEAS_HOME:?set AENEAS_HOME}"
SCRATCH=${SCRATCH:-${TMPDIR:-/tmp}/difffold-extract-myers}
mkdir -p "$SCRATCH/sysroot" "$SCRATCH/target" gen
export PATH="$AENEAS_HOME:$PATH"
export CHARON_MIRI_SYSROOT="$SCRATCH/sysroot" CHARON_MIRI_SYSROOTS="$SCRATCH/sysroot" MIRI_SYSROOT="$SCRATCH/sysroot"
args=(); for r in common_prefix common_suffix snake snake_back line_start suffix_on_line_start count_block count_byte count_lines; do args+=(--start-from "crate::mcore::$r"); done
( cd extract-myers && "$AENEAS_HOME/charon" cargo --preset aeneas --dest-file ../gen/difffold_myers.llbc "${args[@]}" -- --offline --lib --target-dir "$SCRATCH/target" )
rm -rf gen/lean-myers && mkdir -p gen/lean-myers
"$AENEAS_HOME/aeneas" -backend lean -dest gen/lean-myers -no-progress-bar gen/difffold_myers.llbc
{
  echo "charon:   $("$AENEAS_HOME/charon" version | sed "s/ (.*//")"
  echo "aeneas:   $("$AENEAS_HOME/aeneas" -version | sed "s/-[0-9a-f]\{7\}$//")"
  echo "rust:     $("$AENEAS_HOME/charon" toolchain-version)"
  echo "lines.rs sha256:        $(sha256sum ../src/lines.rs | cut -d' ' -f1)"
  echo "lines_core.rs sha256:   $(sha256sum extract/lines_core.rs | cut -d' ' -f1)"
  echo "myers_core.rs sha256:   $(sha256sum extract/myers_core.rs | cut -d' ' -f1)"
  echo "myers llbc sha256:      $(sha256sum gen/difffold_myers.llbc | cut -d' ' -f1)"
  echo "DifffoldMyers.lean:     $(sha256sum gen/lean-myers/DifffoldMyers.lean | cut -d' ' -f1)"
} | tee gen/RECEIPT-myers.txt
