# Reproducing the measurements

The numbers in `README.md` come from the files in `results/` and `harness/results/`. Re-running them
needs an OmniDiff checkout and the tree-sitter parsers.

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
