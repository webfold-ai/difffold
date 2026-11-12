# Reproducing the measurements

The numbers in `README.md` come from the files in `results/` and `harness/results/`. Re-running them
needs an OmniDiff checkout and the tree-sitter parsers. The README section "Provenance of the recorded
results" says which files record their machine and toolchain; for the others, a re-run gives new numbers,
not a confirmation of the recorded ones.

- `harness/run_all.sh` takes its paths from environment variables. Set `DIFFS`, `OMNI` and `OMNI_SRC`
  to your own locations. The defaults are the paths on the machine where the results were recorded,
  and they will not exist elsewhere.
- `proof/run1.sh` contains a machine-specific path to a Lean toolchain and to the build directory.
  It is a development helper, not a CI step.
- `harness/results/tools-*.tsv` record the path of the `dfold-cli` binary used on the recording
  machine. Those rows are a record of that run and are not edited.
- `tools/omni_dump/` depends on an absolute path to an OmniDiff checkout and is excluded from the
  workspace.

The machine used for the cost measurements is recorded in `harness/results/machine.txt`.

## Tree edit distance against APTED

`results/lines/ted-*.csv` with 17 columns are written by `tedbench`:

```sh
cargo run --release --locked -p linebench --bin tedbench -- DIFFS OUT.csv MAXNODES [MAXPAIRS] [REPS] [MINNODES]
```

`DIFFS` is OmniDiff's `src/test/data/diffs`. Defaults are 300 pairs, 3 reps and a 20-node minimum. The
arguments used for the recorded files are not recorded; the three cohorts (up to 384, 1,472 and 5,958 nodes
per side) were evidently selected with different `MAXNODES` values. The program panics, and writes no
further rows, if its distance differs from APTED's, from `ted_unpruned`, from the mapping's implied script
cost, or from the replayed operation count. The 15-column, 6-column and headerless `ted-*` files have no
known producer in this repository.

## Accuracy scoring

```sh
cargo run --release --locked -p difffold --features ts --bin score_accuracy -- DIFFS OMNI_DUMP OUT            # top-down
DFOLD_REFINE=full cargo run --release --locked -p difffold --features ts --bin score_accuracy -- DIFFS OMNI_DUMP OUT   # refined
DFOLD_TED=1 cargo run --release --locked -p difffold --features ts --bin score_accuracy -- DIFFS - OUT
```

`OMNI_DUMP` is the output of `tools/omni_dump`; `-` selects the difffold-only mode that wrote
`SUMMARY-difffold-only.md` (and, in `results/accuracy/previous-fork-run/`, `SUMMARY-ted-only.md`). With `DFOLD_TED` set the scorer uses `ted_mapping`
(falling back to the top-down mapping above 20,000 nodes); `DFOLD_KINDS` and `DFOLD_MOVES` change that
configuration and are not recorded in the committed `ted-only` files.
