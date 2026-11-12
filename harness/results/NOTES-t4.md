# Run t4: protocol and deviations

Governing protocol: `harness/run_all.sh` (cold-process `cli_bench` per tool and fixture, tool order shuffled per round, wall,
CPU and RSS from `wait4`), `harness/select_fixtures.py` (manifest), `harness/summarize.py` (summary), and the layout of `t1` to `t3`
(`manifest-*`, `tools-*`, `cli-*`, `ratios-*`, `machine-*`). Revision at base: `d4a5b0b`; recorded revisions: `machine-t4.txt`.

What was run: `cli-t4.csv` (350 Java, Go, C fixtures; difffold, difffold-refine, their in-process `--reps 10` variants, `git diff
--diff-algorithm=myers`; up to 10 rounds per fixture, 5 s slow cut-off), `omni_time-t4.csv` (OmniDiff in process, 10 passes, same 350
fixtures), `paired-t4/` (120 of the 350, interleaved fixture by fixture in shuffled order, 10 passes each).

Deviations from the protocol, all caused by what was available or by the machine:

1. **No `run_all.sh` invocation.** `run_all.sh` needs OmniDiff's `benchmark_diff_pairs` output as a baseline for the "slowest 50" selection. It was not
   produced; the manifest was selected with the same script on a size-derived baseline (`bytes_before + bytes_after` as `elapsed_ms`), so "slowest" means
   "largest input". `run_all.sh` was updated with `difffold-refine` rows so the committed protocol covers the new engine.
2. **OmniDiff is not run through its command line.** Its binary was not built (the build was cut short by disk space on the recording machine, and
   `tools/omni_dump` shares its dependencies). OmniDiff is timed in process through its library, split into tree-sitter parse, parse plus AST metadata ("load"),
   and `diff_code_with_config`, by `tools/omni_dump/src/bin/omni_time.rs`. Process start and JSON rendering are not included for OmniDiff.
3. **The machine was heavily loaded** by other jobs (one-minute load average 20 to 85 on 4 vCPUs; per-run values in `machine-t4.txt` and in
   `paired-t4/paired.csv`) and all timed processes ran at `nice` 10. Absolute times are several times those of an idle machine. The paired run
   interleaves the tools so that load is shared; unpaired ratios (`unpaired-t4/`) are secondary.
4. **GumTree** was timed on 24 of the 350 fixtures (seed 1), up to 10 rounds, in the same shuffled rounds as difffold's cold process (`cli-gtcmp-t4.csv`, `tools-gtcmp-t4.tsv`), because a cold JVM per round was too slow under this load for all 350. A first attempt on 40 fixtures was aborted when the paired run needed the machine; its partial rows are not kept.
5. **The tool table's objective strings contained commas** and shifted CSV columns in `cli-t4.csv`; the commas were replaced after the run (`sed`) and
   `tools-t4.tsv` has the fixed strings. No numbers were altered.
6. `difffold-hot` and `difffold-refine-hot` wall times include ten in-process passes; their `stdout_line` carries the per-stage medians used by `stage_summary.py`.
