#!/usr/bin/env bash
# Charon -> Aeneas extraction of the real src/kernel.rs, with the digest chain caretaker's proof
# verifier requires (docs/agents/proof-verifier.md): the Aeneas input digest is the LLBC digest,
# and the Lean stage input digest is the generated Lean digest.
#
#   AENEAS_HOME=/path/to/unpacked/release ./extract.sh
#
# AENEAS_HOME holds the verified release `nightly-2026.09.09-505b6ca` (archive sha256
# d5ba53b1370d30866bcd86de5e34abfbadf09e76b3689a7f70f458cd0c133591): aeneas, charon, charon-driver,
# backends/lean. Move its `rust-toolchain` file aside so rustup does not install every listed
# target, and install the toolchain once with only the host target:
#   rustup toolchain install nightly-2026-08-18 --profile minimal -c rustc-dev -c llvm-tools -c rust-src -c miri
set -euo pipefail
cd "$(dirname "$0")"
: "${AENEAS_HOME:?set AENEAS_HOME}"
SCRATCH=${SCRATCH:-${TMPDIR:-/tmp}/difffold-extract}
mkdir -p "$SCRATCH/sysroot" "$SCRATCH/target" gen/lean
export PATH="$AENEAS_HOME:$PATH"
export CHARON_MIRI_SYSROOT="$SCRATCH/sysroot" CHARON_MIRI_SYSROOTS="$SCRATCH/sysroot" MIRI_SYSROOT="$SCRATCH/sysroot"
roots=(fill first_row row_cells cell_value del_cand ins_cand lower_bound diag_stage pick count_cell trim_row suffix_sums bound adiff umin Row::at)
args=(); for r in "${roots[@]}"; do args+=(--start-from "crate::kernel::$r"); done
( cd extract && "$AENEAS_HOME/charon" cargo --preset aeneas --dest-file ../gen/difffold_kernel.llbc "${args[@]}" -- --offline --lib --target-dir "$SCRATCH/target" )
rm -rf gen/lean && mkdir -p gen/lean
"$AENEAS_HOME/aeneas" -backend lean -dest gen/lean -no-progress-bar gen/difffold_kernel.llbc
{
  echo "charon:   $("$AENEAS_HOME/charon" version)"
  echo "aeneas:   $("$AENEAS_HOME/aeneas" -version)"
  echo "rust:     $("$AENEAS_HOME/charon" toolchain-version)"
  echo "kernel.rs sha256:      $(sha256sum ../src/kernel.rs | cut -d' ' -f1)"
  echo "llbc sha256:           $(sha256sum gen/difffold_kernel.llbc | cut -d' ' -f1)"
  echo "DifffoldKernel.lean:   $(sha256sum gen/lean/DifffoldKernel.lean | cut -d' ' -f1)"
} | tee gen/RECEIPT.txt
