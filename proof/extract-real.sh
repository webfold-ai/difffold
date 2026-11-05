#!/usr/bin/env bash
# Charon -> Aeneas extraction of the REAL src/lines.rs search (included by #[path] in extract-myers/lib.rs).
#   AENEAS_HOME=... ./extract-real.sh   -> gen/difffold_real.llbc, gen/lean-real/DifffoldReal.lean, gen/RECEIPT-real.txt
set -euo pipefail
cd "$(dirname "$0")"
: "${AENEAS_HOME:?set AENEAS_HOME}"
SCRATCH=${SCRATCH:-${TMPDIR:-/tmp}/difffold-extract-real}
mkdir -p "$SCRATCH/sysroot" "$SCRATCH/target" gen
export PATH="$AENEAS_HOME:$PATH"
export CHARON_MIRI_SYSROOT="$SCRATCH/sysroot" CHARON_MIRI_SYSROOTS="$SCRATCH/sysroot" MIRI_SYSROOT="$SCRATCH/sysroot"
roots=${ROOTS:-"diff_text_core diff_ids solve middle sweep forward forward_one forward_seq backward backward_one backward_seq snake snake_back common_prefix common_suffix split_lines count_lines line_start suffix_on_line_start first_nl last_nl"}
args=(); for r in $roots; do args+=(--start-from "crate::lines::$r"); done
( cd extract-myers && charon cargo --preset aeneas --dest-file ../gen/difffold_real.llbc "${args[@]}" -- --offline --lib --target-dir "$SCRATCH/target" )
rm -rf gen/lean-real && mkdir -p gen/lean-real
aeneas -backend lean -dest gen/lean-real -no-progress-bar gen/difffold_real.llbc
mv gen/lean-real/*.lean gen/lean-real/DifffoldReal.lean 2>/dev/null || true
{
  echo "charon:   $(charon version | sed "s/ (.*//")"; echo "aeneas:   $(aeneas -version | sed "s/-[0-9a-f]\{7\}$//")"
  echo "lines.rs sha256:   $(sha256sum ../src/lines.rs | cut -d' ' -f1)"
  echo "llbc sha256:       $(sha256sum gen/difffold_real.llbc | cut -d' ' -f1)"
  echo "DifffoldReal.lean: $(sha256sum gen/lean-real/DifffoldReal.lean | cut -d' ' -f1)"
} | tee gen/RECEIPT-real.txt
