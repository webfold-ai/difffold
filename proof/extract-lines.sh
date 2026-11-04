#!/usr/bin/env bash
# Charon -> Aeneas extraction of the pure cores of src/lines.rs and src/ted.rs.
#   AENEAS_HOME=/path/to/unpacked/release ./extract-lines.sh
# Outputs gen/difffold_lines.llbc, gen/lean-lines/DifffoldLines.lean, gen/difffold_ted.llbc,
# gen/lean-ted/DifffoldTed.lean and the digest chain gen/RECEIPT-lines.txt. See extract.sh for the
# toolchain installation. What is extracted:
#   extract-lines/lib.rs  includes the real src/lines.rs by #[path];
#   extract/lines_core.rs is the one copy (first_nl and last_nl without closures, see its header);
#   src/ted.rs is included unchanged by #[path]; the roots are from_kids (via root_from_kids), label_lower_bound,
#   fill_window and within_td. The functions reachable from them are written in the subset stock Aeneas handles.
set -euo pipefail
cd "$(dirname "$0")"
: "${AENEAS_HOME:?set AENEAS_HOME}"
SCRATCH=${SCRATCH:-${TMPDIR:-/tmp}/difffold-extract}
mkdir -p "$SCRATCH/sysroot" "$SCRATCH/target"
export PATH="$AENEAS_HOME:$PATH"
export CHARON_MIRI_SYSROOT="$SCRATCH/sysroot" CHARON_MIRI_SYSROOTS="$SCRATCH/sysroot" MIRI_SYSROOT="$SCRATCH/sysroot"
args=(); for r in nl_mask word common_prefix common_suffix first_in_block last_in_block count_block count_byte count_true each; do args+=(--start-from "crate::lines::$r"); done
for r in first_nl last_nl; do args+=(--start-from "crate::lines_core::$r"); done
( cd extract-lines && "$AENEAS_HOME/charon" cargo --preset aeneas --dest-file ../gen/difffold_lines.llbc "${args[@]}" -- --offline --lib --target-dir "$SCRATCH/target" )
rm -rf gen/lean-lines && mkdir -p gen/lean-lines
"$AENEAS_HOME/aeneas" -backend lean -dest gen/lean-lines -no-progress-bar gen/difffold_lines.llbc
( cd extract-lines && "$AENEAS_HOME/charon" cargo --preset aeneas --dest-file ../gen/difffold_ted.llbc --start-from crate::root_from_kids --start-from crate::ted::label_lower_bound --start-from crate::ted::fill_window --start-from crate::ted::within_td -- --offline --lib --target-dir "$SCRATCH/target" )
rm -rf gen/lean-ted && mkdir -p gen/lean-ted
"$AENEAS_HOME/aeneas" -backend lean -dest gen/lean-ted -no-progress-bar gen/difffold_ted.llbc || true
{
  echo "charon:   $("$AENEAS_HOME/charon" version)"
  echo "aeneas:   $("$AENEAS_HOME/aeneas" -version)"
  echo "rust:     $("$AENEAS_HOME/charon" toolchain-version)"
  echo "lines.rs sha256:        $(sha256sum ../src/lines.rs | cut -d' ' -f1)"
  echo "lines_core.rs sha256:   $(sha256sum extract/lines_core.rs | cut -d' ' -f1)"
  echo "ted.rs sha256:          $(sha256sum ../src/ted.rs | cut -d' ' -f1)"
  echo "lines llbc sha256:      $(sha256sum gen/difffold_lines.llbc | cut -d' ' -f1)"
  echo "DifffoldLines.lean:     $(sha256sum gen/lean-lines/DifffoldLines.lean | cut -d' ' -f1)"
  echo "ted llbc sha256:        $(sha256sum gen/difffold_ted.llbc | cut -d' ' -f1)"
  echo "DifffoldTed.lean:       $(sha256sum gen/lean-ted/DifffoldTed.lean | cut -d' ' -f1)"
} | tee gen/RECEIPT-lines.txt
