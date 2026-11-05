# General tree edit distance: difffold `ted` against other exact tools  [measured]

This lane times difffold's general ordered tree edit distance (`ted`, plus `ted_within` with a supplied
threshold) against APTED, the Touzet family, and X-TED CPU. Unit costs throughout: insert, delete and
relabel each cost 1. Every completed cell was checked against difffold's distance on the same pair.

Raw rows: `results/fastted/raw.csv`. Per-cell min, median and max: `results/fastted/summary.csv`. Matrix:
`results/fastted/matrix.md` (copied below). Driver and adapters: `tools/fastted_adapters/` and the Rust
binaries `src/bin/fastted_export.rs` and `src/bin/fastted_bench.rs`.

## Headline, per regime

Figures are medians over timed reps for the full call (preprocessing plus distance). Each comparison
below is limited to pairs where both tools completed.

- **Real AST pairs (10 Java pairs, 77 to 5,958 nodes).** difffold is faster than APTED on every pair where
  both ran. Median of difffold over APTED is 0.04 (9 pairs). At 5,958 nodes: difffold 71 ms, APTED 18.0 s,
  X-TED with 4 threads 5.3 s. The Touzet baseline `ted()` path (unknown bound) is the fastest of the unknown-mode
  tools on 6 of the 10 real pairs, and difffold on 4. On the 2,763-node large-distance pair (distance 370)
  difffold takes 1.04 s, X-TED with 4 threads 1.04 s, and the Touzet baseline 1.87 s.
- **Low-distance mutations (15 pairs, shapes x sizes, distance 1 to 50).** difffold is fastest on 12 of the 15
  pairs, the Touzet baseline `ted()` on 3. At 5,000 balanced: difffold 184 ms, APTED 20.9 s, X-TED with 4 threads
  4.8 s.
- **Unrelated trees (15 pairs, distance 128 to 9,962).** This is where difffold does not win. The fastest
  unknown-mode tool is X-TED with 4 threads on 7 pairs, difffold on 5, X-TED with 1 thread on 3. Median
  difffold over X-TED with 4 threads is 2.36 (14 pairs), and median difffold over APTED is 0.71 (12 pairs).
  Examples where a competitor is faster: 1,000-node star (APTED 222 ms, difffold 264 ms), 1,000-node balanced
  (X-TED 4 threads 169 ms, difffold 446 ms), and 5,000-node rcomb (X-TED 4 threads 2.3 s, difffold `ted` 5.3 s;
  difffold's threshold run on that pair did not complete).

These medians come from a single machine, with the caveats under Limitations. They do not establish that
difffold is fastest or slowest in general.

## Setup

- Branch `bench/faster-ted` from `origin/main`. Nothing pushed to `main`, no force push.
- Hardware: Intel Xeon Processor @ 2.10 GHz, 4 logical CPUs (`lscpu`), 15 GB RAM, shared cloud VM. No GPU:
  `nvidia-smi` is not installed, so **X-TED GPU: no GPU available, not run**.
- Scratch clones and builds were under the session scratchpad. They are deleted after this commit.

## Tool versions

| Tool | Version used | Source |
|---|---|---|
| difffold | crate version `0.0.1` from `main` (not a tagged release; the repo has no release tags) | this repo, `src/ted.rs`; built with Rust 1.89.0, `--release`, debug info off (`CARGO_PROFILE_RELEASE_DEBUG=0`, which does not change generated code) |
| APTED, Touzet baseline / KR-set / depth-pruning | tree-similarity **tag 0.1.1** (commit date 2023-05-03) | https://github.com/DatabaseGroup/tree-similarity, header-only; compiled with g++ 13.3.0, `-O3 -DNDEBUG -std=c++17` |
| X-TED CPU | **no tagged release**; default-branch snapshot cloned 2026-11-05, last commit dated 2025-06-14 | https://github.com/Davis-Fan/X-TED, `X-TED_CPU/`; compiled with g++ 13.3.0, `-O3 -DNDEBUG -std=c++14 -pthread`; `TED.cpp`, `parallel_computing.cpp`, `dataset_preprocess.cpp`, not its `main.cpp` |

No semver tag exists for X-TED, so the version is recorded as a dated snapshot.

The label "TopDiff" in the brief does not name any class in tree-similarity 0.1.1. The row "Touzet baseline
`ted()` (TopDiff path)" runs the `ted()` in `src/ted/ted_algorithm_touzet.h` on `TouzetBaselineTreeIndex`. That
`ted()` doubles a threshold with no supplied bound. The Touzet KR-set and depth-pruning indices inherit the same
`ted()`, and they are reported as separate rows.

## Inputs

- **Real AST pairs (10).** OmniDiff Defects4J Java fixtures, parsed with tree-sitter-java through difffold's
  `ts` feature by `fastted_export`. Node counts match the existing `results/lines/ted-*.csv`. Pairs:
  chart-10, protobuf update-comment-2, jacksondatabind-84, cli-2, compress-7, jacksondatabind-38, chart-17,
  chart-13, chart-3, chart-21. Labels are interned (kind, text) for leaves and kind for internal nodes,
  as in `src/bin/ted_map.rs`.
- **Synthetic pairs (30).** `tools/fastted_adapters/gen_synthetic.py`. Five shapes (chain, star or wide,
  left comb, right comb, balanced binary), sizes 100, 1,000 and 5,000 nodes, two regimes.
  - `mut` (low distance): the second tree is the first with max(1, n/100) random edits (relabel, insert leaf,
    delete leaf). Realized distances are 1 to 50.
  - `unrel` (large distance): the second tree is a uniform random recursive tree with n nodes and fresh labels.
    Realized distances are about 0.9 n. This is an unrelated-structure regime, not a same-shape rewrite.
  - Labels come from a 16-symbol alphabet. Seeds are fixed per pair.

## Phases and what is charged

- difffold: `prep` = `PostTree::from_kids` for both trees. `dist` = `ted` or `ted_within`. The distance time
  includes difffold's internal mirror choice and doubling, as `ted` does.
- tree-similarity: `build` = constructing the library's node tree from the file. The library's `add_child`
  copies subtrees, so this is O(n * depth) and is reported on its own. `index` = `index_tree` for both trees.
  `dist` = the algorithm call.
- X-TED: `build` = converting to preorder vectors. `dist` = `standard_ted`, which includes its own cost matrix
  and key-root setup. X-TED has no separate index phase.
- Summary totals are per-rep sums of the phases, so `total_med_us` is the median of per-rep totals.

## Modes

- **Unknown:** the tool searches the threshold itself (`ted`, `ted()`, `standard_ted`).
- **Threshold:** the tool gets tau = difffold's exact distance for the pair, and the cost of obtaining tau is
  charged. difffold's own unknown-mode total for the pair is that cost. Charged totals are
  `tool total + difffold unknown total` (medians). This tau is a tight bound, so the charge is required.
  Rows marked "(charged)" in the matrix are threshold-mode.
- APTED and X-TED have no threshold entry point and were not run in threshold mode.

## Method

- Every run is pinned with `taskset`: single-thread tools on core 0, X-TED with 4 threads on cores 0 to 3.
- Per cell: one untimed warm-up plus 7 timed reps. `summary.csv` holds min, median and max for prep and
  distance.
- Cell cap: the driver stops after any run that exceeds 60 s and records `gt60s`. The runner also wraps each
  process in `timeout 75`, which kills a run that is still going past 60 s. A cell with no completed row is
  reported as "n/a" or "skipped".
- Distance assertion: every completed timed distance must equal difffold's unknown-mode distance on the same
  pair. A mismatch would be marked `DISAGREE` and excluded from timing. **No DISAGREE cells occurred.**

## Distance agreement and disagreements

- Across all completed unknown-mode and threshold-mode cells, every returned distance equals difffold's.
- **Touzet KR-set `ted_k` returned "above tau" at tau = difffold's distance in 4 cells**: mutation chain 1,000
  (D=8), chain 5,000 (D=34), lcomb 5,000 (D=50), rcomb 1,000 (D=10). For unit costs, the optimal mapping's
  insertions plus deletions cannot exceed the total distance, so tau = D should be a valid `k`. These
  results contradict that expectation. Those cells are excluded from timing and reported as `above_tau`. I did
  not investigate the cause.
- X-TED CPU has undefined behavior in `key_roots` (`TED.cpp`, around line 68): `(j>0) & (key_roots_view[j-1] <
  kr_view[i])` uses bitwise `&`, so `key_roots_view[-1]` is read when `j == 0`. AddressSanitizer reports
  heap-buffer-overflow on 3-node inputs. The optimized build runs and its distances agree with difffold, so the
  adapter uses the unmodified source. A local `&&` patch was tested in a scratch copy and not used.

## Matrix

Median total per cell (preprocessing plus distance, reps summed per rep), in ms. Threshold-mode and charged
columns include the cost of obtaining tau. "n/a" means no output row, from a first run that did not finish within
the 75 s cap or a cell interrupted by a runner restart (the CSV cannot separate these). "skipped" means a run
exceeded 60 s. "above_tau" is described above. `D` is difffold's exact distance.

| regime | shape | nodes A/B | D | difffold ted | difffold ted_within (charged) | APTED (C++) | Touzet baseline ted() (TopDiff path) | Touzet baseline ted_k (charged) | Touzet KR-set ted() | Touzet KR-set ted_k (charged) | Touzet depth-pruning ted() | Touzet depth-pruning ted_k (charged) | X-TED CPU (1 thread) | X-TED CPU (4 threads) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| mutation | balanced | 100 / 100 | 1 | 0.04 ms | 0.06 ms | 1.90 ms | 0.10 ms | 0.13 ms | 0.09 ms | 0.12 ms | 0.09 ms | 0.12 ms | 0.87 ms | 2.01 ms |
| mutation | balanced | 1000 / 1002 | 10 | 5.10 ms | 7.34 ms | 430.44 ms | 7.31 ms | 10.54 ms | 5.18 ms | 8.17 ms | 6.53 ms | 9.46 ms | 128.50 ms | 115.50 ms |
| mutation | balanced | 5000 / 4996 | 50 | 183.77 ms | 264.58 ms | 20882.42 ms | 347.12 ms | 289.05 ms | 201.28 ms | 266.36 ms | 364.59 ms | 306.90 ms | 7153.18 ms | 4779.23 ms |
| mutation | chain | 100 / 100 | 1 | 0.04 ms | 0.06 ms | 0.91 ms | 0.70 ms | 0.69 ms | 0.46 ms | 0.47 ms | 0.50 ms | 0.53 ms | 0.16 ms | 0.33 ms |
| mutation | chain | 1000 / 1000 | 8 | 0.70 ms | 1.22 ms | 146.30 ms | 1158.65 ms | 876.27 ms | 67.14 ms | above_tau (tool reported distance above tau) | 85.98 ms | 77.52 ms | 18.12 ms | 29.73 ms |
| mutation | chain | 5000 / 5003 | 34 | 20.57 ms | 40.36 ms | 7009.13 ms | n/a | n/a | 4836.94 ms | above_tau (tool reported distance above tau) | n/a | 9329.54 ms | 1425.65 ms | 956.62 ms |
| mutation | lcomb | 100 / 100 | 1 | 0.04 ms | 0.05 ms | 0.60 ms | 0.27 ms | 0.36 ms | 0.22 ms | 0.22 ms | 0.20 ms | 0.26 ms | 25.27 ms | 23.14 ms |
| mutation | lcomb | 1000 / 998 | 10 | 1.82 ms | 2.96 ms | 193.84 ms | 1370.27 ms | 624.99 ms | 46.41 ms | 54.43 ms | 111.28 ms | 76.77 ms | n/a | n/a |
| mutation | lcomb | 5000 / 5011 | 50 | 199.88 ms | 273.45 ms | 4061.32 ms | n/a | n/a | 1695.09 ms | above_tau (tool reported distance above tau) | n/a | n/a | n/a | n/a |
| mutation | rcomb | 100 / 100 | 1 | 0.03 ms | 0.15 ms | 0.75 ms | 0.34 ms | 0.39 ms | 0.38 ms | 0.42 ms | 0.32 ms | 0.44 ms | 0.41 ms | 3.41 ms |
| mutation | rcomb | 1000 / 999 | 10 | 2.24 ms | 364.12 ms | 76.77 ms | 1095.81 ms | 375.10 ms | 999.38 ms | above_tau (tool reported distance above tau) | 80.67 ms | 40.96 ms | 28.45 ms | 54.51 ms |
| mutation | rcomb | 5000 / 4996 | 50 | 100.49 ms | skipped (no completed timed run (killed or error)) | 4299.99 ms | n/a | n/a | n/a | n/a | n/a | 5377.21 ms | 1925.05 ms | 2121.44 ms |
| mutation | star | 100 / 99 | 1 | 0.06 ms | 0.11 ms | 0.65 ms | 0.04 ms | 0.10 ms | 0.06 ms | 0.12 ms | 0.05 ms | 0.11 ms | 0.49 ms | 4.05 ms |
| mutation | star | 1000 / 1000 | 10 | 8.01 ms | 11.70 ms | 66.08 ms | 2.79 ms | 9.06 ms | 5.46 ms | 9.69 ms | 3.33 ms | 9.42 ms | 63.57 ms | 78.13 ms |
| mutation | star | 5000 / 4997 | 49 | 226.58 ms | 303.85 ms | 4297.89 ms | 52.76 ms | 253.32 ms | 97.18 ms | 268.81 ms | 68.26 ms | 252.16 ms | 2171.86 ms | 2226.95 ms |
| real AST | java-ast | 77 / 77 | 1 | 0.03 ms | 0.06 ms | 1.41 ms | 0.07 ms | 0.10 ms | 0.07 ms | 0.11 ms | 0.08 ms | 0.10 ms | 0.68 ms | 1.68 ms |
| real AST | java-ast | 80 / 87 | 7 | 0.15 ms | 0.32 ms | 1.56 ms | 0.15 ms | 0.30 ms | 0.21 ms | 0.34 ms | 0.17 ms | 0.31 ms | 0.65 ms | 3.18 ms |
| real AST | java-ast | 655 / 701 | 46 | 11.90 ms | 25.97 ms | 125.60 ms | 5.85 ms | 17.69 ms | 6.44 ms | 17.90 ms | 6.44 ms | 18.15 ms | 52.92 ms | 47.60 ms |
| real AST | java-ast | 952 / 1053 | 102 | 91.75 ms | 145.87 ms | 292.61 ms | 18.55 ms | 109.89 ms | 19.32 ms | 111.11 ms | 21.60 ms | 111.36 ms | 124.80 ms | 104.75 ms |
| real AST | java-ast | 1070 / 1067 | 10 | 11.76 ms | 18.42 ms | 627.39 ms | 10.79 ms | 16.91 ms | 12.47 ms | 17.31 ms | 11.82 ms | 17.00 ms | 200.85 ms | 179.24 ms |
| real AST | java-ast | 1236 / 1248 | 25 | 22.56 ms | 36.98 ms | 634.02 ms | 14.26 ms | 33.63 ms | 16.79 ms | 34.07 ms | 18.54 ms | 34.91 ms | 251.46 ms | 193.93 ms |
| real AST | java-ast | 2763 / 3131 | 370 | 1037.97 ms | 1758.87 ms | 3754.04 ms | 1866.66 ms | 1324.97 ms | 1665.54 ms | 1403.15 ms | 1862.96 ms | 1391.84 ms | 1368.88 ms | 1042.79 ms |
| real AST | java-ast | 4590 / 4609 | 36 | 155.56 ms | 261.90 ms | 10588.73 ms | 93.12 ms | 219.29 ms | 96.09 ms | 219.40 ms | 112.24 ms | 219.57 ms | 3870.34 ms | 3190.79 ms |
| real AST | java-ast | 4613 / 4622 | 9 | 28.39 ms | 64.40 ms | n/a | 29.74 ms | 56.96 ms | 31.61 ms | 58.63 ms | 29.38 ms | 57.52 ms | 9317.60 ms | 3440.10 ms |
| real AST | java-ast | 5958 / 5982 | 24 | 70.98 ms | 165.46 ms | 17984.86 ms | 31.31 ms | 100.41 ms | 40.92 ms | 108.17 ms | 55.60 ms | 106.24 ms | 7498.26 ms | 5314.61 ms |
| unrelated | balanced | 100 / 100 | 123 | 1.07 ms | 1.63 ms | 1.63 ms | 6.23 ms | 4.30 ms | 3.02 ms | 2.48 ms | 7.04 ms | 4.79 ms | 0.99 ms | 48.15 ms |
| unrelated | balanced | 1000 / 1000 | 1202 | 446.49 ms | 597.50 ms | 497.93 ms | 2632.30 ms | 1222.23 ms | 1011.09 ms | 771.98 ms | 3213.73 ms | 1418.07 ms | 224.11 ms | 169.33 ms |
| unrelated | balanced | 5000 / 5000 | 6002 | 33119.37 ms | 52188.49 ms | skipped (a run exceeded 60 s) | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 8043.05 ms |
| unrelated | chain | 100 / 100 | 186 | 0.30 ms | 0.58 ms | 1.48 ms | 154.17 ms | 171.43 ms | 11.23 ms | 1.86 ms | 163.27 ms | 102.76 ms | 0.31 ms | 0.83 ms |
| unrelated | chain | 1000 / 1000 | 1970 | 190.04 ms | 385.20 ms | 558.83 ms | n/a | n/a | 844.69 ms | 617.50 ms | n/a | n/a | 197.49 ms | 61.90 ms |
| unrelated | chain | 5000 / 5000 | 9962 | 7538.13 ms | 14314.86 ms | n/a | n/a | n/a | n/a | 11831.98 ms | n/a | n/a | 5716.87 ms | 1781.80 ms |
| unrelated | lcomb | 100 / 100 | 130 | 0.57 ms | 0.93 ms | 0.93 ms | 104.38 ms | 54.88 ms | 12.92 ms | 2.03 ms | 104.90 ms | 37.98 ms | 11.37 ms | 9.79 ms |
| unrelated | lcomb | 1000 / 1000 | 1377 | 192.84 ms | 342.12 ms | 241.29 ms | n/a | n/a | 422.35 ms | 350.75 ms | n/a | n/a | 6687.88 ms | 4153.10 ms |
| unrelated | lcomb | 5000 / 5000 | 6900 | 3581.53 ms | 6067.44 ms | 5028.71 ms | n/a | n/a | n/a | 8639.11 ms | n/a | n/a | n/a | n/a |
| unrelated | rcomb | 100 / 100 | 138 | 0.59 ms | 5.33 ms | 1.03 ms | 26.72 ms | 8.66 ms | 20.84 ms | 7.55 ms | 29.81 ms | 9.99 ms | 0.47 ms | 1.47 ms |
| unrelated | rcomb | 1000 / 1000 | 1391 | 109.73 ms | 7681.00 ms | 136.26 ms | n/a | n/a | n/a | 8139.88 ms | n/a | n/a | 60.47 ms | 61.36 ms |
| unrelated | rcomb | 5000 / 5000 | 6908 | 5309.85 ms | skipped (no completed timed run (killed or error)) | 7019.37 ms | n/a | n/a | n/a | n/a | n/a | n/a | 7147.88 ms | 2250.23 ms |
| unrelated | star | 100 / 100 | 128 | 0.63 ms | 1.05 ms | 1.02 ms | 7.41 ms | 2.51 ms | 11.49 ms | 1.67 ms | 10.48 ms | 2.00 ms | 0.67 ms | 1.20 ms |
| unrelated | star | 1000 / 1000 | 1237 | 264.29 ms | 407.35 ms | 221.67 ms | 1439.53 ms | 597.07 ms | 1256.53 ms | 635.41 ms | 1843.96 ms | 710.06 ms | 157.45 ms | 66.45 ms |
| unrelated | star | 5000 / 5000 | 6146 | 10022.43 ms | 16682.03 ms | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 8707.28 ms | 3330.01 ms |

## Limitations

- **One machine, one run per cell.** Timings are medians of 7 reps but come from a single VM session. Load was
  not controlled: other `run_matrix.sh` jobs from a different scratch directory were running on the same VM for
  part of the run, which I did not start and did not stop. Load average was about 2 during the run. Treat
  individual cells as noisy, especially under 1 ms.
- **Interrupted and resumed runs.** The matrix was stopped and resumed several times, with a fix to the resume
  logic partway through. A resume dropped partial rows for pairs that had not finished and reran them. Duplicate
  rows were removed by keeping the first row for each (tool, mode, pair, phase, rep). Some cells marked "n/a" may be
  cells that were interrupted by these restarts, and the CSV cannot distinguish them from cells that exceeded the
  cap.
- **Cells not run.** Many 5,000-node unrelated and some mutation cells exceeded the cap for at least one tool
  (see the matrix). Those results are missing, not wins for any tool.
- **Threshold mode.** tau is an exact distance, so tight-bound threshold timings favour the threshold tools.
  The charge is applied, but it is a single difffold run per pair. difffold's `ted_within` was slower than its
  own `ted` on some pairs, for example mutation rcomb 1,000 (364 ms against 2.2 ms). I did not investigate that
  difference.
- **Synthetic regimes.** The `unrel` regime uses random recursive trees, which give large distances but not
  same-shape rewrites. The `mut` regime covers only leaf-level edits. Neither represents real code diffs
  beyond the 10 real pairs.
- **X-TED.** Unpatched source with a known out-of-bounds read (see above). Its distance agreement held on every
  completed cell. The 4-thread run uses the same source with `standard_ted(..., threads, ...)`.
- **Not established.** Asymptotic complexity, peak memory, mapping recovery cost, and behavior on other
  languages.

## Reproduce

Clone the two external repos (tree-similarity at tag 0.1.1, X-TED default branch), then:

    TREE_SIMILARITY_DIR=... XTED_DIR=... OUT=... tools/fastted_adapters/build.sh
    cargo build --release --features ts --bin fastted_export --bin fastted_bench
    python3 tools/fastted_adapters/gen_synthetic.py TREES
    # export the 10 real pairs with fastted_export from the OmniDiff fixtures (names above)
    tools/fastted_adapters/run_matrix.sh TREES OUT RAW.csv
    tools/fastted_adapters/run_xted_threads.sh TREES OUT RAW4.csv 4
    python3 tools/fastted_adapters/aggregate.py RAW.csv TREES summary.csv matrix.md

The results committed here were produced by the sequence above, with the restarts described under Limitations.
