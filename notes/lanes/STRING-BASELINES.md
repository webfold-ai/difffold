# String baselines: unit-cost Levenshtein against Edlib, RapidFuzz, WFA2-lib and difffold

Scope: exact unit-cost Levenshtein (insert, delete and substitute each cost 1) on integer token
sequences. The indel (LCS) and gap-affine objectives are not measured here.

Harness: `tools/strbench/` (standalone Cargo project with its own `Cargo.lock`, not a member of the
main workspace). Raw data: `tools/strbench/results/matrix.tsv`, one row per matrix cell and tool.
The winner tables below are generated from that file by `tools/strbench/summarize.py`.

Labels: MEASURED means the number came from the harness on the machine described under Hardware.
Nothing here is claimed for other hardware or builds.

## Status

- Externals (Edlib, RapidFuzz, WFA2-lib): built, verified against independent oracles, and run over the
  full matrix. MEASURED.
- difffold: the kernel in `src/levenshtein.rs` from the difffold kernel branch was merged into this lane
  and is included by path in the harness, so the timed code is the repository code. Exact job uses
  `levenshtein`, bounded job uses `levenshtein_within_u32`. MEASURED in the same matrix run as the
  other tools. difffold does not win the classical cells (see Results).

## Tools and versions

| tool | version used | how it is built or called | notes |
|---|---|---|---|
| Edlib | tag `v1.2.7` (latest release tag) | C++ `edlib.cpp`, `c++ -O3 -DNDEBUG`, called through `csrc/shim.cpp` | global NW mode, `EDLIB_TASK_DISTANCE`, bound `k` |
| WFA2-lib | tag `v2.3.6` (latest release tag) | C sources of `alignment/ system/ utils/ wavefront/`, `cc -O3 -DNDEBUG`, called through the shim | `distance_metric = edit`, `compute_score`, `heuristic = wf_heuristic_none`, `max_alignment_steps` |
| RapidFuzz | crate `rapidfuzz` `0.5.0` from crates.io | direct Rust call | uniform weights (1, 1, 1), `score_cutoff` for bounded queries |
| RapidFuzz (C++) | not built | tag `v3.3.4` exists but was not used | the Rust crate is the RapidFuzz entry, which the task allows |
| difffold | kernel `src/levenshtein.rs` from the difffold kernel branch, merged into this lane | Rust, included with `#[path]` | exact `levenshtein` (threshold doubling), bounded `levenshtein_within_u32` |

No commit hashes or branch names are recorded in any committed file. Edlib and WFA2-lib were fetched
at the tags above into the scratchpad, outside the repository. The build reads them through the
`STRBENCH_EXT` environment variable.

## Objective mapping

- Edlib: `edlibNewAlignConfig(k, EDLIB_MODE_NW, EDLIB_TASK_DISTANCE, NULL, 0)`. `k = -1` means
  unbounded. A distance above `k` returns `-1`.
- WFA2: `distance_metric = edit` (Levenshtein), `alignment_scope = compute_score`,
  `heuristic.strategy = wf_heuristic_none`, `system.max_alignment_steps`. WFA2 aborts when
  `score >= max_alignment_steps`, so the bound `k` is passed as `k + 1`.
- RapidFuzz: `levenshtein::distance` with the default weight table (1, 1, 1). The default was
  checked against the oracle, not assumed. Bounded queries use `Args::score_cutoff(k)`, which returns
  `None` when the distance exceeds `k`.
- difffold: `levenshtein(a, b)` for the exact job and `levenshtein_within_u32(a, b, k)` for the
  bounded job. Both are the kernel's public entry points.

## Symbol representation

- Dense alphabets with 2, 4 and 256 symbols use ids `0..sigma`.
- Sparse alphabets use 4,096 random `u32` ids, all at least 256.
- RapidFuzz and difffold receive the `u32` ids directly. difffold is generic over `Eq`.
- Edlib receives the ids as bytes (identity map), so it runs only for `sigma <= 256`.
- WFA2 receives the ids through an injective map onto 253 byte values that excludes `'!'` (33) and
  `'?'` (63). Those bytes are WFA2's end sentinels (see Findings). WFA2 is therefore recorded as
  `unsupported` at 256 symbols, because every byte is needed.
- No id is ever concatenated or encoded into several bytes.

## Oracles and verification

- Full two-row Wagner-Fischer DP for pairs up to about 4 million cells.
- Banded DP that is exact for every distance at most `k`. It also serves the exact job, with bound
  doubling, within a budget of 4e8 cells per pair.
- Above that budget, the exact job uses RapidFuzz as the reference, labelled `consensus-rapidfuzz` in
  the TSV. This applies only to the 100,000-symbol unrelated pairs. The band would be quadratic there.
- Verification, MEASURED: `verify` checked every adapter (including difffold) against the full DP on
  40,000 random pairs (two seeds of 20,000, lengths 1 to 40) for the exact answer and for bounds 0, 1,
  2, 4, 8, 32 and 128. That is 1,090,696 checks with 0 failures. `cargo test` in the harness also
  passes, including the band oracle over lengths up to 60.
- Benchmark matrix, MEASURED: 3,120 cells, 4 tools, 0 disagreements between any tool and its oracle or
  reference. Every pair that a tool timed was checked first.

## Hardware, load and build

- Intel Xeon at 2.10 GHz, 4 vCPU with one thread per core, about 15 GiB RAM, Linux 6.18. Every run is
  pinned with `taskset -c 0`.
- The VM is shared with other benchmark agents. The 1-minute load average at the start of each cell
  was between 2.11 and 3.12 during the matrix run (column `load1_at_start` in the TSV). Load reached
  about 6.5 at other times in the session. Expect noise of the same order as differences in close
  cells, and note that cells near the 60 second limit flip between runs under load.
- Rust 1.89.0 release build (`opt-level 3`, `debug = 0`). C and C++ built with GCC 13.3, `-O3 -DNDEBUG
  -w`, with no `-march` flag. Edlib and WFA2 therefore compile without AVX2 and use their scalar paths.

## Method

- Job (a), exact distance: each tool is called with no bound. Edlib and WFA2 allocate per call, and that
  cost is part of the measured time. Input conversion happens before timing, for every tool.
- Job (b), bounded query: each tool uses its native bound (Edlib `k`, WFA2 `max_alignment_steps`,
  RapidFuzz `score_cutoff`, difffold `levenshtein_within_u32`). Bounds are 1, 2, 4, 8, 32 and 128.
- Timing: one warm-up pass, then 7 timed passes over the cell's pairs. Each pass is divided by the
  number of pairs (5 pairs, or 3 for lengths of 10,000 and above). The tables show the median of the 7
  per-pair means. The TSV also has min and max.
- Each cell runs in its own process with a 60 second wall-clock limit for the whole cell (oracle,
  warm-up and timed passes) and a 6 GiB address-space limit. A cell over the limit is `timeout`.
- Regimes are defined by the designed edit count `d` relative to the bound `k`. `d<k` uses `k/2`,
  `d==k` uses `k`, `d==k+1` uses `k+1`, `d>>k` uses `min(8k, n/2)` and is skipped when that is below
  `2k`. `tiny-prefix-suffix` makes 2 edits in the middle third, which keeps a long identical prefix and
  suffix. `unrelated` uses two independent random sequences. The exact job uses `tiny-prefix-suffix`
  (2 edits), `d=16` (16 edits anywhere) and `unrelated`. The TSV's `realized_d_median` column gives the
  realized distance, because random edits can cancel.

## Findings from harness development and the run (MEASURED)

1. WFA2-lib character interface: its ASCII kernels use `'!'` as the pattern end sentinel and `'?'` as
   the text end sentinel. A symbol equal to the other side's sentinel can extend past the end. Random
   pairs over bytes 1 to 127 gave wrong distances on 6 of 300 pairs (for example 41 for an answer of
   40), and the run slowed to about 0.2 s per call. Excluding those two bytes gave 0 mismatches in
   40,000 checks. The harness uses that remap. This is an interface limitation, not a library change.
2. WFA2 `max_alignment_steps` aborts when `score >= limit`, so an answer of exactly `k` was reported as
   exceeding the bound. The harness passes `k + 1`.
3. Edlib with one empty input ignores the bound and returns the exact distance even when it exceeds `k`
   (for example `n = 34, m = 0, k = 4` returns 34). The benchmark uses lengths of 16 and up, so this
   path is not timed.
4. difffold, observed in the matrix: its exact path is much slower than the other tools on unrelated
   pairs. At length 1,000 with alphabet 2 the median is 2.07 ms per pair, against 56 us for RapidFuzz.
   At length 10,000 it is 92 ms, against 11 to 16 ms for RapidFuzz and Edlib. Its bounded path is 2 to
   5 times slower than RapidFuzz at length 1,000 (median ratio 3.6, 4.3, 5.0 and 2.2 for alphabets 2,
   4, 256 and sparse). These are measured ratios. The cause was not profiled here.

## Results: winners per regime (MEASURED)

Times are medians in microseconds per pair (`us`), or milliseconds (`ms`) where stated. The winner is
the fastest tool whose answers agreed with the oracle. Tables follow below. Cells marked `unsupported`
are explained under Symbol representation. Cells marked `timeout` hit the 60 second cell limit.

Win counts over all cells that have at least one timed result: bounded job, RapidFuzz 419, WFA2
144, difffold 76, Edlib 1 (640 cells). Exact job, RapidFuzz 34, WFA2 12, difffold 10, Edlib 3 (59
cells). These counts are a summary of the tables, not a ranking.

Exact distance (job a):

- Lengths 16 and 100: RapidFuzz is fastest in every regime, at 0.07 to 4.3 us. The other tools are
  between 0.6 and 33 us in these cells.
- Length 1,000: WFA2 is fastest for `tiny` and `d=16` on alphabets 2 and 4 (1.0 to 2.9 us, against 18
  to 58 us for Edlib and RapidFuzz). RapidFuzz is fastest for unrelated pairs on alphabets 2, 4 and
  256 (51 to 85 us). difffold is fastest for sparse `d=16` (66 us, against 158 us for RapidFuzz).
  difffold is slowest on unrelated pairs at this length (2.0 to 3.3 ms on alphabets 2, 4 and 256).
- Length 10,000: WFA2 is fastest for `tiny` and `d=16` on alphabets 2 and 4 (2.6 to 5.5 us, against
  99 to 11,400 us for RapidFuzz and 178 to 326 us for Edlib). difffold is fastest for `d=16` on
  alphabet 256 (3.4 ms, against 8.5 ms for Edlib and 12 ms for RapidFuzz), and for sparse `d=16`
  (3.4 ms, against 48 ms for RapidFuzz) and sparse `tiny` (53 us, against 320 us). Edlib is fastest
  for unrelated pairs on alphabet 2 (11.4 ms, against 15.9 ms for RapidFuzz). RapidFuzz is fastest for
  unrelated pairs on the other alphabets.
- Length 100,000: WFA2 is fastest for `tiny` and `d=16` on alphabets 2 and 4 (23 to 30 us, against 4.6
  to 8.1 ms for Edlib and 12 to 20 ms for RapidFuzz). difffold is fastest for `tiny` and `d=16` on
  alphabet 256 (0.21 ms and 40 ms, against 75 and 96 ms for Edlib and 7.7 ms and 1.3 s for RapidFuzz),
  and for sparse `tiny` and `d=16` (0.18 ms and 16 ms). Edlib is fastest for unrelated pairs on alphabets
  2 and 4 (0.66 s and 1.35 s). RapidFuzz is fastest for unrelated pairs on alphabet 256 (1.46 s). WFA2
  and difffold timed out on unrelated pairs, and RapidFuzz timed out on unrelated pairs at alphabets 2
  and 4, and Edlib timed out at alphabet 256. These unrelated cells sit near the 60 second limit, and in the earlier run at load about 2
  RapidFuzz and Edlib completed them (for example Edlib at alphabet 256 took 1.2 s).

Bounded threshold query (job b):

- Lengths 16 and 100: RapidFuzz is fastest in most cells, often at 20 to 200 ns for short inputs.
  difffold wins several `k=1` cells on this length, for example 0.03 us at length 16 on alphabet 2.
- Length 1,000: WFA2 is fastest for `k` of 4 and above on alphabets 2 and 4 (about 1 to 19 us). RapidFuzz
  is fastest for `k` of 1 and 2 on alphabet 2, and for most cells on alphabet 256. difffold is 2 to 5
  times slower than RapidFuzz on median at this length.
- Lengths 10,000 and 100,000, alphabets 2 and 4: WFA2 is fastest in most cells (about 2.8 to 33 us at
  length 10,000, and 22 to 77 us at 100,000). RapidFuzz and Edlib win a few cells, mostly unrelated
  pairs at small `k` and some `d>>k` cells.
- Alphabet 256: RapidFuzz is fastest in most cells from length 100. Edlib takes 55 to 91 ms per pair at
  length 100,000 in this run, which is 100 to 1,000 times slower. difffold wins several `k=1` cells
  (for example 45 us at length 100,000, against 127 us for RapidFuzz). WFA2 is unsupported.
- Sparse `u32` alphabet: RapidFuzz and difffold are the only tools that run. difffold wins 41 of the
  160 sparse cells, mostly at small `k` and at lengths of 10,000 and above, and RapidFuzz wins most of the
  rest.
- difffold wins by bound: 26 of 120 cells at `k=1`, then 14 of 120 at `k=2`, 16 of 120 at `k=4`, 7 of
  116 at `k=8`, 9 of 92 at `k=32` and 4 of 72 at `k=128`. Its advantage is therefore concentrated at
  small bounds, and at large bounds it trails WFA2 and RapidFuzz.

Edlib's bounded cost at length 100,000 ranges from 0.3 to 12 ms per pair on alphabets 2 and 4, and
from 55 to 91 ms on alphabet 256. This is measured, not profiled.

RapidFuzz's bounded path on unrelated pairs returns in tens of nanoseconds at length 100,000 (for
example 47 ns on alphabet 2 with `k=1`). The answers matched the oracle on every timed pair, but the
mechanism was not profiled. Those cells favour an early exit on unrelated input and are not a
throughput comparison.

## Full matrix, winners per cell

Generated from `tools/strbench/results/matrix.tsv` by `tools/strbench/summarize.py`. Exact-job cells
are not split by `k`. Bounded tables are split by regime, with one column per bound. Each cell shows the
fastest tool, its median microseconds per pair, and the runner-up ratio. A cell with no timed result shows
its status instead. `k >= n` means the bound is vacuous, and the cell was skipped.

## Exact distance (job a)

| regime | len | alphabet | winner (median us/pair, runner-up ratio) | Edlib | WFA2 | RapidFuzz | difffold |
|---|---|---|---|---|---|---|---|
| d=16 | 16 | 2 | **RapidFuzz** 0.126 (8.12x) | 1.215 | 2.025 | 0.126 | 1.023 |
| d=16 | 16 | 256 | **RapidFuzz** 0.098 (13.6x) | 1.375 | unsupported | 0.098 | 1.336 |
| d=16 | 16 | 4 | **RapidFuzz** 0.092 (6.85x) | 0.63 | 1.474 | 0.092 | 0.714 |
| d=16 | 16 | sparse-u32 | **RapidFuzz** 0.207 (6x) | unsupported | unsupported | 0.207 | 1.242 |
| d=16 | 100 | 2 | **RapidFuzz** 2.29 (1.15x) | 3.822 | 2.636 | 2.292 | 6.766 |
| d=16 | 100 | 256 | **RapidFuzz** 2.31 (6.85x) | 16.47 | unsupported | 2.31 | 15.81 |
| d=16 | 100 | 4 | **RapidFuzz** 1.37 (1.21x) | 2.316 | 1.653 | 1.371 | 4.256 |
| d=16 | 100 | sparse-u32 | **RapidFuzz** 1.9 (8.3x) | unsupported | unsupported | 1.899 | 15.75 |
| d=16 | 1000 | 2 | **WFA2** 2.93 (8.78x) | 25.73 | 2.93 | 57.34 | 162.3 |
| d=16 | 1000 | 256 | **RapidFuzz** 40.6 (2.03x) | 207 | unsupported | 40.55 | 82.5 |
| d=16 | 1000 | 4 | **WFA2** 1.83 (11.5x) | 20.96 | 1.827 | 57.48 | 183.2 |
| d=16 | 1000 | sparse-u32 | **difffold** 65.9 (2.4x) | unsupported | unsupported | 158.3 | 65.91 |
| d=16 | 10000 | 2 | **WFA2** 5.52 (59x) | 326 | 5.522 | 1.14e+04 | 4336 |
| d=16 | 10000 | 256 | **difffold** 3.45e+03 (2.46x) | 8496 | unsupported | 1.207e+04 | 3449 |
| d=16 | 10000 | 4 | **WFA2** 3.81 (56x) | 213.5 | 3.81 | 9749 | 4069 |
| d=16 | 10000 | sparse-u32 | **difffold** 3.37e+03 (14.4x) | unsupported | unsupported | 4.846e+04 | 3372 |
| d=16 | 100000 | 2 | **WFA2** 24 (191x) | 4584 | 23.95 | 1.282e+06 | 5.565e+04 |
| d=16 | 100000 | 256 | **difffold** 4e+04 (2.39x) | 9.563e+04 | unsupported | 1.32e+06 | 3.995e+04 |
| d=16 | 100000 | 4 | **WFA2** 22.9 (211x) | 4820 | 22.9 | 1.423e+06 | 7.172e+04 |
| d=16 | 100000 | sparse-u32 | **difffold** 1.6e+04 | unsupported | unsupported | timeout | 1.598e+04 |
| tiny-prefix-suffix | 16 | 2 | **RapidFuzz** 0.067 (1.94x) | 1.033 | 1.433 | 0.067 | 0.13 |
| tiny-prefix-suffix | 16 | 256 | **RapidFuzz** 0.062 (3.05x) | 1.09 | 0.874 | 0.062 | 0.189 |
| tiny-prefix-suffix | 16 | 4 | **RapidFuzz** 0.039 (2.31x) | 0.641 | 0.898 | 0.039 | 0.09 |
| tiny-prefix-suffix | 16 | sparse-u32 | **RapidFuzz** 0.111 (4.5x) | unsupported | unsupported | 0.111 | 0.499 |
| tiny-prefix-suffix | 100 | 2 | **RapidFuzz** 0.184 (4.08x) | 3.479 | 1.822 | 0.184 | 0.751 |
| tiny-prefix-suffix | 100 | 256 | **RapidFuzz** 0.132 (5.63x) | 10.1 | unsupported | 0.132 | 0.743 |
| tiny-prefix-suffix | 100 | 4 | **RapidFuzz** 0.127 (2.83x) | 2.033 | 1.023 | 0.127 | 0.36 |
| tiny-prefix-suffix | 100 | sparse-u32 | **RapidFuzz** 0.155 (2.91x) | unsupported | unsupported | 0.155 | 0.451 |
| tiny-prefix-suffix | 1000 | 2 | **WFA2** 1.73 (1.29x) | 18.1 | 1.729 | 2.236 | 2.497 |
| tiny-prefix-suffix | 1000 | 256 | **RapidFuzz** 4.81 (1.06x) | 221.3 | unsupported | 4.812 | 5.078 |
| tiny-prefix-suffix | 1000 | 4 | **WFA2** 1.02 (3.53x) | 35.76 | 1.02 | 3.601 | 6.054 |
| tiny-prefix-suffix | 1000 | sparse-u32 | **difffold** 3.29 (1.12x) | unsupported | unsupported | 3.699 | 3.289 |
| tiny-prefix-suffix | 10000 | 2 | **WFA2** 2.62 (14.9x) | 178.8 | 2.621 | 101.6 | 39.12 |
| tiny-prefix-suffix | 10000 | 256 | **difffold** 29 (2.99x) | 7356 | unsupported | 86.92 | 29.04 |
| tiny-prefix-suffix | 10000 | 4 | **WFA2** 2.85 (12x) | 198.4 | 2.854 | 99.44 | 34.33 |
| tiny-prefix-suffix | 10000 | sparse-u32 | **difffold** 53 (6.04x) | unsupported | unsupported | 320.1 | 52.96 |
| tiny-prefix-suffix | 100000 | 2 | **WFA2** 24.6 (9.91x) | 5791 | 24.64 | 1.188e+04 | 244.1 |
| tiny-prefix-suffix | 100000 | 256 | **difffold** 205 (37.5x) | 7.503e+04 | unsupported | 7686 | 205.2 |
| tiny-prefix-suffix | 100000 | 4 | **WFA2** 30 (10.6x) | 8130 | 29.98 | 2.034e+04 | 318.4 |
| tiny-prefix-suffix | 100000 | sparse-u32 | **difffold** 180 (106x) | unsupported | unsupported | 1.904e+04 | 179.8 |
| unrelated | 16 | 2 | **RapidFuzz** 0.137 (4.7x) | 0.987 | 2.129 | 0.137 | 0.644 |
| unrelated | 16 | 256 | **RapidFuzz** 0.094 (18.8x) | 1.77 | unsupported | 0.094 | 2.703 |
| unrelated | 16 | 4 | **RapidFuzz** 0.092 (10.1x) | 1.12 | 1.413 | 0.092 | 0.926 |
| unrelated | 16 | sparse-u32 | **RapidFuzz** 0.225 (13.5x) | unsupported | unsupported | 0.225 | 3.047 |
| unrelated | 100 | 2 | **RapidFuzz** 3.11 (1.19x) | 3.709 | 6.318 | 3.108 | 8.217 |
| unrelated | 100 | 256 | **RapidFuzz** 1.53 (16.4x) | 32.92 | unsupported | 1.526 | 25.09 |
| unrelated | 100 | 4 | **RapidFuzz** 1.46 (1.48x) | 2.169 | 8.331 | 1.462 | 6.609 |
| unrelated | 100 | sparse-u32 | **RapidFuzz** 4.32 (9.79x) | unsupported | unsupported | 4.317 | 42.26 |
| unrelated | 1000 | 2 | **RapidFuzz** 56.1 (1.73x) | 96.83 | 173.3 | 56.11 | 2068 |
| unrelated | 1000 | 256 | **RapidFuzz** 50.9 (5.16x) | 262.5 | unsupported | 50.88 | 3292 |
| unrelated | 1000 | 4 | **RapidFuzz** 85.1 (1.23x) | 104.3 | 2080 | 85.1 | 2118 |
| unrelated | 1000 | sparse-u32 | **RapidFuzz** 183 (27.8x) | unsupported | unsupported | 182.6 | 5073 |
| unrelated | 10000 | 2 | **Edlib** 1.14e+04 (1.39x) | 1.142e+04 | 3.661e+04 | 1.588e+04 | 9.239e+04 |
| unrelated | 10000 | 256 | **RapidFuzz** 1.25e+04 (2.31x) | 2.879e+04 | unsupported | 1.246e+04 | 1.086e+05 |
| unrelated | 10000 | 4 | **RapidFuzz** 1.61e+04 (1.18x) | 1.902e+04 | 1.192e+05 | 1.613e+04 | 9.268e+04 |
| unrelated | 10000 | sparse-u32 | **RapidFuzz** 4.82e+04 (8.48x) | unsupported | unsupported | 4.822e+04 | 4.089e+05 |
| unrelated | 100000 | 2 | **Edlib** 6.59e+05 | 6.587e+05 | timeout | timeout | timeout |
| unrelated | 100000 | 256 | **RapidFuzz** 1.46e+06 | timeout | unsupported | 1.458e+06 | timeout |
| unrelated | 100000 | 4 | **Edlib** 1.35e+06 | 1.348e+06 | timeout | timeout | timeout |
| unrelated | 100000 | sparse-u32 | timeout/unsupported | unsupported | unsupported | timeout | timeout |

## Bounded threshold query (job b)

### d<k

| len | alphabet | k=1 | k=2 | k=4 | k=8 | k=32 | k=128 |
|---|---|---|---|---|---|---|---|
| 16 | 2 | **difffold** 0.039 (1.44x) | **difffold** 0.065 (1.08x) | **difffold** 0.045 (1.38x) | **RapidFuzz** 0.115 (3.68x) | k >= n | k >= n |
| 16 | 4 | **RapidFuzz** 0.035 (1.2x) | **difffold** 0.039 (1.54x) | **RapidFuzz** 0.066 (4.79x) | **RapidFuzz** 0.071 (2.49x) | k >= n | k >= n |
| 16 | 256 | **difffold** 0.019 (1.37x) | **difffold** 0.043 (1.84x) | **RapidFuzz** 0.064 (3.75x) | **RapidFuzz** 0.131 (2.74x) | k >= n | k >= n |
| 16 | sparse-u32 | **difffold** 0.029 (1.41x) | **difffold** 0.055 (1.47x) | **RapidFuzz** 0.093 (4.08x) | **RapidFuzz** 0.098 (2.62x) | k >= n | k >= n |
| 100 | 2 | **difffold** 0.05 (1.36x) | **RapidFuzz** 0.065 (1.08x) | **RapidFuzz** 0.217 (2.48x) | **RapidFuzz** 0.396 (2.3x) | **RapidFuzz** 1.34 (1.07x) | k >= n |
| 100 | 4 | **difffold** 0.051 (1.35x) | **difffold** 0.08 (1.16x) | **RapidFuzz** 0.217 (2.36x) | **RapidFuzz** 0.37 (2.67x) | **WFA2** 1.72 (1.04x) | k >= n |
| 100 | 256 | **difffold** 0.048 (2.15x) | **difffold** 0.072 (1.39x) | **RapidFuzz** 0.222 (4.44x) | **RapidFuzz** 0.445 (4.39x) | **RapidFuzz** 1.36 (1.79x) | k >= n |
| 100 | sparse-u32 | **difffold** 0.048 (1.46x) | **difffold** 0.074 (1.24x) | **RapidFuzz** 0.24 (3.42x) | **RapidFuzz** 1.62 (1.17x) | **RapidFuzz** 1.8 (1.96x) | k >= n |
| 1000 | 2 | **difffold** 0.356 (2.29x) | **RapidFuzz** 0.694 (1.07x) | **WFA2** 1.51 (2.17x) | **WFA2** 1.13 (4.94x) | **WFA2** 1.8 (8.37x) | **WFA2** 10.1 (1.94x) |
| 1000 | 4 | **difffold** 0.324 (1.45x) | **RapidFuzz** 0.718 (1.06x) | **WFA2** 1.09 (1.63x) | **WFA2** 1.19 (2.67x) | **WFA2** 1.86 (7.9x) | **WFA2** 14.3 (1.31x) |
| 1000 | 256 | **difffold** 0.473 (1.97x) | **difffold** 0.467 (1.53x) | **RapidFuzz** 2.06 (7.57x) | **RapidFuzz** 4.27 (13.5x) | **RapidFuzz** 14.8 (5x) | **RapidFuzz** 21.1 (4.45x) |
| 1000 | sparse-u32 | **difffold** 0.365 (1.47x) | **difffold** 0.442 (1.64x) | **RapidFuzz** 3.87 (2.95x) | **RapidFuzz** 24.3 (1.89x) | **RapidFuzz** 38.7 (2.76x) | **RapidFuzz** 68.3 (1.86x) |
| 10000 | 2 | **WFA2** 2.39 (2.12x) | **difffold** 3.64 (1.09x) | **WFA2** 2.91 (18x) | **WFA2** 2.94 (9.58x) | **WFA2** 5.16 (27.7x) | **WFA2** 9.7 (22.8x) |
| 10000 | 4 | **WFA2** 2.68 (1.23x) | **WFA2** 2.76 (1.9x) | **WFA2** 3.06 (5.61x) | **WFA2** 3.03 (10.5x) | **WFA2** 3.7 (42.6x) | **WFA2** 10.2 (21.3x) |
| 10000 | 256 | **RapidFuzz** 4.46 (1.39x) | **difffold** 4.71 (1.23x) | **RapidFuzz** 25.8 (2.5x) | **RapidFuzz** 84.3 (6.46x) | **RapidFuzz** 316 (24.1x) | **RapidFuzz** 330 (36.1x) |
| 10000 | sparse-u32 | **difffold** 5.93 (1.55x) | **difffold** 4.12 (3.14x) | **difffold** 112 (2.06x) | **RapidFuzz** 373 (1.17x) | **RapidFuzz** 3.3e+03 (2.28x) | **RapidFuzz** 3.87e+03 (7.12x) |
| 100000 | 2 | **WFA2** 24.7 (2.09x) | **WFA2** 37.2 (2.29x) | **WFA2** 31.5 (13.1x) | **WFA2** 24.9 (17x) | **WFA2** 26 (176x) | **WFA2** 46.5 (132x) |
| 100000 | 4 | **WFA2** 30.6 (1.13x) | **WFA2** 26.3 (2.25x) | **WFA2** 29.8 (15x) | **WFA2** 29.7 (10.3x) | **WFA2** 23.8 (351x) | **WFA2** 32.5 (233x) |
| 100000 | 256 | **difffold** 34 (1.48x) | **difffold** 45.7 (3.07x) | **RapidFuzz** 523 (8.35x) | **RapidFuzz** 419 (19.6x) | **RapidFuzz** 7.67e+03 (4.62x) | **RapidFuzz** 8.86e+03 (8.9x) |
| 100000 | sparse-u32 | **RapidFuzz** 50.9 (1.25x) | **difffold** 76.9 (1.64x) | **difffold** 3.43e+03 (1.14x) | **RapidFuzz** 8.16e+03 (1.05x) | **RapidFuzz** 1.93e+04 (2.06x) | **RapidFuzz** 2.86e+04 (5.83x) |

### d==k

| len | alphabet | k=1 | k=2 | k=4 | k=8 | k=32 | k=128 |
|---|---|---|---|---|---|---|---|
| 16 | 2 | **difffold** 0.029 (1.34x) | **RapidFuzz** 0.096 (2.19x) | **RapidFuzz** 0.113 (3.26x) | **RapidFuzz** 0.129 (4.21x) | k >= n | k >= n |
| 16 | 4 | **RapidFuzz** 0.028 (2.14x) | **RapidFuzz** 0.054 (3.3x) | **RapidFuzz** 0.081 (2.65x) | **RapidFuzz** 0.123 (3.63x) | k >= n | k >= n |
| 16 | 256 | **difffold** 0.049 (1.06x) | **RapidFuzz** 0.097 (4.82x) | **RapidFuzz** 0.087 (7.36x) | **RapidFuzz** 0.09 (4.94x) | k >= n | k >= n |
| 16 | sparse-u32 | **RapidFuzz** 0.029 (1.14x) | **RapidFuzz** 0.091 (2.05x) | **RapidFuzz** 0.11 (3.45x) | **RapidFuzz** 0.108 (3.36x) | k >= n | k >= n |
| 100 | 2 | **difffold** 0.071 (1.11x) | **RapidFuzz** 0.109 (3.68x) | **RapidFuzz** 0.278 (3.64x) | **RapidFuzz** 0.825 (1.59x) | **RapidFuzz** 1.37 (1.13x) | k >= n |
| 100 | 4 | **RapidFuzz** 0.071 (1.42x) | **RapidFuzz** 0.127 (3.91x) | **RapidFuzz** 0.41 (2.68x) | **RapidFuzz** 0.374 (3.28x) | **RapidFuzz** 1.25 (1.62x) | k >= n |
| 100 | 256 | **difffold** 0.095 (1.42x) | **RapidFuzz** 0.152 (9.64x) | **RapidFuzz** 0.628 (2.72x) | **RapidFuzz** 0.49 (4.67x) | **RapidFuzz** 1.42 (2.17x) | k >= n |
| 100 | sparse-u32 | **difffold** 0.081 (1.05x) | **RapidFuzz** 0.163 (7.25x) | **RapidFuzz** 1.11 (2.37x) | **RapidFuzz** 2.11 (1.35x) | **RapidFuzz** 1.84 (2.82x) | k >= n |
| 1000 | 2 | **difffold** 0.465 (1.48x) | **RapidFuzz** 1.42 (1.24x) | **WFA2** 1.17 (3.37x) | **WFA2** 1.33 (4.71x) | **WFA2** 2.87 (5.37x) | **WFA2** 18.8 (1.13x) |
| 1000 | 4 | **RapidFuzz** 0.694 (1.16x) | **WFA2** 1.71 (1.28x) | **WFA2** 2.06 (3.45x) | **WFA2** 2.24 (3.23x) | **WFA2** 3.17 (4.85x) | **Edlib** 20.7 (1.06x) |
| 1000 | 256 | **difffold** 0.449 (1.41x) | **RapidFuzz** 1.38 (4.59x) | **RapidFuzz** 3.33 (7.5x) | **RapidFuzz** 4.68 (14x) | **RapidFuzz** 14.7 (5.23x) | **RapidFuzz** 17.2 (4.67x) |
| 1000 | sparse-u32 | **difffold** 0.449 (1.78x) | **RapidFuzz** 1.33 (8.18x) | **RapidFuzz** 37 (1.11x) | **RapidFuzz** 41 (2.42x) | **RapidFuzz** 38.5 (2.95x) | **RapidFuzz** 66.4 (1.9x) |
| 10000 | 2 | **WFA2** 3.72 (1.04x) | **WFA2** 2.85 (2.22x) | **WFA2** 2.81 (11.5x) | **WFA2** 2.83 (21.8x) | **WFA2** 8.77 (34.3x) | **WFA2** 25.5 (9.07x) |
| 10000 | 4 | **WFA2** 2.87 (2.28x) | **WFA2** 3.28 (3.48x) | **WFA2** 3.09 (20.4x) | **WFA2** 3.27 (14.2x) | **WFA2** 9.45 (24.7x) | **WFA2** 32.8 (6.93x) |
| 10000 | 256 | **difffold** 7.87 (1.42x) | **RapidFuzz** 11 (7.64x) | **RapidFuzz** 74.7 (3.77x) | **RapidFuzz** 67.6 (9.16x) | **RapidFuzz** 148 (26.3x) | **RapidFuzz** 204 (22x) |
| 10000 | sparse-u32 | **difffold** 8.14 (1.39x) | **RapidFuzz** 28.3 (1.63x) | **difffold** 144 (3.1x) | **difffold** 281 (1.4x) | **RapidFuzz** 583 (12.4x) | **RapidFuzz** 3.46e+03 (8.13x) |
| 100000 | 2 | **WFA2** 24.9 (2.09x) | **WFA2** 23.6 (3.7x) | **WFA2** 32.9 (12.8x) | **WFA2** 23.5 (137x) | **WFA2** 22.7 (187x) | **WFA2** 52.7 (138x) |
| 100000 | 4 | **WFA2** 24.4 (2.55x) | **WFA2** 21.9 (4.5x) | **WFA2** 32 (109x) | **WFA2** 30.9 (16x) | **WFA2** 34.5 (131x) | **WFA2** 76.6 (94.2x) |
| 100000 | 256 | **difffold** 44.8 (1.6x) | **RapidFuzz** 127 (4.45x) | **RapidFuzz** 363 (11.4x) | **RapidFuzz** 621 (17.9x) | **RapidFuzz** 7.82e+03 (5.17x) | **RapidFuzz** 8.21e+03 (8.79x) |
| 100000 | sparse-u32 | **difffold** 44 (1.64x) | **RapidFuzz** 102 (3.31x) | **difffold** 4.06e+03 (1.88x) | **difffold** 8.33e+03 (1.07x) | **RapidFuzz** 2.38e+04 (1.51x) | **RapidFuzz** 2.8e+04 (6.17x) |

### d==k+1

| len | alphabet | k=1 | k=2 | k=4 | k=8 | k=32 | k=128 |
|---|---|---|---|---|---|---|---|
| 16 | 2 | **RapidFuzz** 0.039 (2.36x) | **RapidFuzz** 0.046 (2.74x) | **RapidFuzz** 0.068 (2.28x) | **RapidFuzz** 0.125 (3.26x) | k >= n | k >= n |
| 16 | 4 | **RapidFuzz** 0.026 (5.73x) | **RapidFuzz** 0.054 (3.39x) | **RapidFuzz** 0.073 (2.53x) | **RapidFuzz** 0.09 (3.09x) | k >= n | k >= n |
| 16 | 256 | **RapidFuzz** 0.028 (3.43x) | **RapidFuzz** 0.048 (6.25x) | **RapidFuzz** 0.08 (5.99x) | **RapidFuzz** 0.083 (5.35x) | k >= n | k >= n |
| 16 | sparse-u32 | **RapidFuzz** 0.044 (10x) | **RapidFuzz** 0.103 (4.51x) | **RapidFuzz** 0.198 (2.96x) | **RapidFuzz** 0.115 (2.96x) | k >= n | k >= n |
| 100 | 2 | **RapidFuzz** 0.046 (6.04x) | **RapidFuzz** 0.124 (7.56x) | **RapidFuzz** 0.54 (3.39x) | **RapidFuzz** 0.662 (3.13x) | **difffold** 2.58 (1.03x) | k >= n |
| 100 | 4 | **RapidFuzz** 0.134 (5.66x) | **RapidFuzz** 0.14 (9.4x) | **RapidFuzz** 0.441 (3.68x) | **RapidFuzz** 1.33 (1.14x) | **RapidFuzz** 1.39 (1.13x) | k >= n |
| 100 | 256 | **RapidFuzz** 0.101 (17.9x) | **RapidFuzz** 0.191 (4.84x) | **RapidFuzz** 0.482 (4.25x) | **RapidFuzz** 0.894 (4.8x) | **RapidFuzz** 3.04 (1.64x) | k >= n |
| 100 | sparse-u32 | **RapidFuzz** 0.099 (16.3x) | **RapidFuzz** 0.118 (19.3x) | **RapidFuzz** 0.787 (4.09x) | **RapidFuzz** 2.57 (1.25x) | **RapidFuzz** 1.99 (2.14x) | k >= n |
| 1000 | 2 | **RapidFuzz** 0.387 (1.37x) | **RapidFuzz** 0.95 (1.19x) | **WFA2** 1.19 (2.57x) | **WFA2** 1.32 (2.77x) | **WFA2** 4.72 (3.28x) | **WFA2** 19.3 (1.1x) |
| 1000 | 4 | **RapidFuzz** 0.452 (2.18x) | **RapidFuzz** 1.75 (1.14x) | **WFA2** 1.99 (2.38x) | **WFA2** 2.68 (2.86x) | **WFA2** 5.35 (5.88x) | **RapidFuzz** 21.1 (1.28x) |
| 1000 | 256 | **RapidFuzz** 0.426 (8.25x) | **RapidFuzz** 1.15 (10.2x) | **RapidFuzz** 2.9 (8.63x) | **RapidFuzz** 4.31 (15.7x) | **RapidFuzz** 15.1 (5.37x) | **RapidFuzz** 18.9 (5.34x) |
| 1000 | sparse-u32 | **RapidFuzz** 0.387 (6.81x) | **RapidFuzz** 0.807 (9.94x) | **difffold** 43 (1.33x) | **RapidFuzz** 62.4 (1.91x) | **RapidFuzz** 40 (3.13x) | **RapidFuzz** 65.8 (2.01x) |
| 10000 | 2 | **WFA2** 3.58 (1.16x) | **WFA2** 2.7 (3.08x) | **WFA2** 3.08 (11.8x) | **WFA2** 3.12 (13.4x) | **WFA2** 4.94 (30.4x) | **WFA2** 39.2 (5.26x) |
| 10000 | 4 | **WFA2** 2.38 (1.88x) | **RapidFuzz** 0.973 (2.83x) | **WFA2** 2.84 (13x) | **WFA2** 2.76 (10.4x) | **WFA2** 5.62 (31.3x) | **WFA2** 31 (7.36x) |
| 10000 | 256 | **RapidFuzz** 2.42 (10.4x) | **RapidFuzz** 7.74 (6.22x) | **RapidFuzz** 36.8 (4.16x) | **RapidFuzz** 75.1 (4.14x) | **RapidFuzz** 157 (26.3x) | **RapidFuzz** 186 (63.8x) |
| 10000 | sparse-u32 | **RapidFuzz** 3.47 (23.3x) | **RapidFuzz** 11.4 (4.34x) | **difffold** 149 (3.36x) | **RapidFuzz** 532 (1.06x) | **RapidFuzz** 533 (7.21x) | **RapidFuzz** 3.5e+03 (8.23x) |
| 100000 | 2 | **WFA2** 22.6 (4.85x) | **WFA2** 24.4 (4.91x) | **WFA2** 36.4 (85.4x) | **WFA2** 23.3 (139x) | **WFA2** 38.1 (117x) | **WFA2** 48.8 (130x) |
| 100000 | 4 | **WFA2** 28 (1.58x) | **WFA2** 23.3 (7.16x) | **WFA2** 20.9 (14.1x) | **WFA2** 23.2 (19.6x) | **WFA2** 42.8 (101x) | **WFA2** 56.2 (157x) |
| 100000 | 256 | **RapidFuzz** 24.7 (11.4x) | **RapidFuzz** 85 (9.97x) | **RapidFuzz** 376 (18.7x) | **RapidFuzz** 666 (14.1x) | **RapidFuzz** 7.81e+03 (5.7x) | **RapidFuzz** 8.23e+03 (8.26x) |
| 100000 | sparse-u32 | **RapidFuzz** 36 (1.76x) | **RapidFuzz** 108 (5.19x) | **difffold** 3.41e+03 (1.11x) | **RapidFuzz** 7.44e+03 (1.47x) | **RapidFuzz** 2.77e+04 (1.44x) | **RapidFuzz** 2.36e+04 (8.51x) |

### d>>k

| len | alphabet | k=1 | k=2 | k=4 | k=8 | k=32 | k=128 |
|---|---|---|---|---|---|---|---|
| 16 | 2 | **RapidFuzz** 0.026 (3.69x) | **RapidFuzz** 0.034 (3.5x) | **RapidFuzz** 0.049 (2.8x) | designed distance not applicable at this length and k | k >= n | k >= n |
| 16 | 4 | **RapidFuzz** 0.04 (9.03x) | **RapidFuzz** 0.043 (4.65x) | **RapidFuzz** 0.085 (2.78x) | designed distance not applicable at this length and k | k >= n | k >= n |
| 16 | 256 | **RapidFuzz** 0.025 (16.1x) | **RapidFuzz** 0.032 (7.72x) | **RapidFuzz** 0.08 (4.56x) | designed distance not applicable at this length and k | k >= n | k >= n |
| 16 | sparse-u32 | **RapidFuzz** 0.02 (7.2x) | **RapidFuzz** 0.033 (6.15x) | **RapidFuzz** 0.114 (2.77x) | designed distance not applicable at this length and k | k >= n | k >= n |
| 100 | 2 | **RapidFuzz** 0.028 (19.8x) | **RapidFuzz** 0.093 (17.8x) | **RapidFuzz** 0.079 (6.52x) | **RapidFuzz** 0.523 (4.2x) | designed distance not applicable at this length and k | k >= n |
| 100 | 4 | **RapidFuzz** 0.022 (12.5x) | **RapidFuzz** 0.041 (20.7x) | **RapidFuzz** 0.03 (8.87x) | **RapidFuzz** 0.251 (5.3x) | designed distance not applicable at this length and k | k >= n |
| 100 | 256 | **RapidFuzz** 0.041 (2.78x) | **RapidFuzz** 0.048 (34.8x) | **RapidFuzz** 0.277 (12.8x) | **RapidFuzz** 0.141 (15.5x) | designed distance not applicable at this length and k | k >= n |
| 100 | sparse-u32 | **RapidFuzz** 0.017 (2x) | **RapidFuzz** 0.061 (12.7x) | **RapidFuzz** 0.252 (5.68x) | **RapidFuzz** 0.351 (5.32x) | designed distance not applicable at this length and k | k >= n |
| 1000 | 2 | **RapidFuzz** 0.048 (10.2x) | **RapidFuzz** 0.217 (4.77x) | **RapidFuzz** 1.28 (1.45x) | **RapidFuzz** 0.65 (2.85x) | **WFA2** 3.83 (1.85x) | **RapidFuzz** 11.8 (1.06x) |
| 1000 | 4 | **RapidFuzz** 0.282 (6.07x) | **RapidFuzz** 0.152 (6.95x) | **RapidFuzz** 0.145 (7.4x) | **RapidFuzz** 0.11 (12.2x) | **RapidFuzz** 3.3 (1.25x) | **RapidFuzz** 8.94 (1.6x) |
| 1000 | 256 | **RapidFuzz** 0.042 (5.4x) | **RapidFuzz** 0.116 (4.9x) | **RapidFuzz** 0.635 (4.49x) | **RapidFuzz** 0.367 (26.3x) | **RapidFuzz** 4.79 (11.8x) | **RapidFuzz** 12.9 (5.8x) |
| 1000 | sparse-u32 | **RapidFuzz** 0.038 (11.8x) | **RapidFuzz** 0.135 (9.41x) | **RapidFuzz** 0.432 (2.94x) | **RapidFuzz** 2.18 (5.82x) | **RapidFuzz** 8.01 (5.43x) | **RapidFuzz** 21.1 (2.91x) |
| 10000 | 2 | **RapidFuzz** 0.841 (2.41x) | **RapidFuzz** 1.04 (2.01x) | **WFA2** 1.76 (3.01x) | **WFA2** 1.86 (1.38x) | **WFA2** 4.63 (9.11x) | **WFA2** 41.4 (1.45x) |
| 10000 | 4 | **RapidFuzz** 0.021 (72x) | **WFA2** 1.92 (1.45x) | **RapidFuzz** 0.405 (7.18x) | **RapidFuzz** 0.757 (2.79x) | **WFA2** 5.1 (8.48x) | **RapidFuzz** 42 (1.5x) |
| 10000 | 256 | **RapidFuzz** 0.882 (10.9x) | **RapidFuzz** 2.98 (6.16x) | **RapidFuzz** 3.47 (3.81x) | **RapidFuzz** 2.4 (8.15x) | **RapidFuzz** 32.4 (5.82x) | **RapidFuzz** 44.2 (160x) |
| 10000 | sparse-u32 | **RapidFuzz** 1.08 (5.59x) | **RapidFuzz** 1.35 (4.21x) | **difffold** 18.1 (1.22x) | **difffold** 37.9 (1.56x) | **difffold** 173 (1.35x) | **RapidFuzz** 231 (33.5x) |
| 100000 | 2 | **RapidFuzz** 7.68 (2.09x) | **WFA2** 15.6 (1.63x) | **WFA2** 14.7 (5.49x) | **WFA2** 14.2 (4.72x) | **WFA2** 16.4 (30.7x) | **WFA2** 45.9 (12.6x) |
| 100000 | 4 | **RapidFuzz** 2.15 (6.64x) | **WFA2** 19.2 (1.64x) | **WFA2** 14.4 (5.39x) | **WFA2** 17.9 (1.41x) | **WFA2** 16.8 (32.9x) | **WFA2** 79.2 (8.45x) |
| 100000 | 256 | **RapidFuzz** 8.17 (2.15x) | **RapidFuzz** 38.7 (3.91x) | **RapidFuzz** 23.9 (5.81x) | **RapidFuzz** 52.8 (4.98x) | **RapidFuzz** 3.52e+03 (2.27x) | **RapidFuzz** 3.51e+03 (7.99x) |
| 100000 | sparse-u32 | **RapidFuzz** 8.75 (6.29x) | **RapidFuzz** 13.8 (4.91x) | **difffold** 205 (1.42x) | **difffold** 386 (1.14x) | **difffold** 7.5e+03 (1.09x) | **RapidFuzz** 8.85e+03 (3.58x) |

### tiny-prefix-suffix

| len | alphabet | k=1 | k=2 | k=4 | k=8 | k=32 | k=128 |
|---|---|---|---|---|---|---|---|
| 16 | 2 | **RapidFuzz** 0.028 (1.43x) | **RapidFuzz** 0.059 (1.41x) | **difffold** 0.021 (1.29x) | **RapidFuzz** 0.041 (2.17x) | k >= n | k >= n |
| 16 | 4 | **RapidFuzz** 0.03 (1.47x) | **RapidFuzz** 0.039 (2.64x) | **RapidFuzz** 0.042 (1.6x) | **RapidFuzz** 0.058 (4.16x) | k >= n | k >= n |
| 16 | 256 | **RapidFuzz** 0.054 (3.5x) | **RapidFuzz** 0.08 (4.39x) | **RapidFuzz** 0.073 (3.66x) | **RapidFuzz** 0.059 (3.14x) | k >= n | k >= n |
| 16 | sparse-u32 | **RapidFuzz** 0.028 (8.86x) | **RapidFuzz** 0.046 (4.65x) | **RapidFuzz** 0.073 (2.41x) | **RapidFuzz** 0.054 (2.22x) | k >= n | k >= n |
| 100 | 2 | **RapidFuzz** 0.094 (2.65x) | **RapidFuzz** 0.096 (2.35x) | **RapidFuzz** 0.145 (2.31x) | **RapidFuzz** 0.151 (1.6x) | **RapidFuzz** 0.198 (1.17x) | k >= n |
| 100 | 4 | **RapidFuzz** 0.069 (2.8x) | **RapidFuzz** 0.108 (1.33x) | **RapidFuzz** 0.127 (1.72x) | **RapidFuzz** 0.153 (1.87x) | **RapidFuzz** 0.147 (1.5x) | k >= n |
| 100 | 256 | **RapidFuzz** 0.074 (10.8x) | **RapidFuzz** 0.125 (3.8x) | **RapidFuzz** 0.258 (2.06x) | **RapidFuzz** 0.136 (5.71x) | **RapidFuzz** 0.124 (6.24x) | k >= n |
| 100 | sparse-u32 | **RapidFuzz** 0.075 (4.27x) | **RapidFuzz** 0.118 (2.18x) | **RapidFuzz** 0.189 (2.56x) | **RapidFuzz** 0.179 (2.53x) | **RapidFuzz** 0.264 (2.42x) | k >= n |
| 1000 | 2 | **difffold** 0.518 (1.07x) | **RapidFuzz** 0.811 (1.34x) | **RapidFuzz** 1.03 (1.07x) | **RapidFuzz** 0.93 (1.15x) | **WFA2** 0.942 (1.18x) | **difffold** 0.883 (1.22x) |
| 1000 | 4 | **RapidFuzz** 0.606 (1.73x) | **RapidFuzz** 0.831 (1.3x) | **WFA2** 0.966 (1.11x) | **WFA2** 1.08 (1.01x) | **WFA2** 0.998 (2.18x) | **WFA2** 1.23 (1.8x) |
| 1000 | 256 | **RapidFuzz** 0.339 (4.31x) | **RapidFuzz** 1.57 (8.15x) | **RapidFuzz** 1.72 (2.06x) | **RapidFuzz** 1.2 (4.27x) | **RapidFuzz** 2.86 (1.74x) | **RapidFuzz** 2.48 (1.67x) |
| 1000 | sparse-u32 | **RapidFuzz** 0.377 (6.36x) | **RapidFuzz** 0.78 (4.38x) | **RapidFuzz** 3.45 (1.98x) | **RapidFuzz** 3.03 (1.72x) | **RapidFuzz** 6.43 (1.74x) | **RapidFuzz** 4.15 (1.56x) |
| 10000 | 2 | **WFA2** 2.21 (1.69x) | **WFA2** 2.73 (2.44x) | **WFA2** 2.92 (2.45x) | **WFA2** 4.27 (2.28x) | **WFA2** 2.88 (7.76x) | **WFA2** 2.88 (8.88x) |
| 10000 | 4 | **WFA2** 2.21 (1.67x) | **WFA2** 2.88 (2.34x) | **WFA2** 2.81 (3.02x) | **WFA2** 2.55 (5.15x) | **WFA2** 2.81 (10.5x) | **WFA2** 2.87 (7.14x) |
| 10000 | 256 | **RapidFuzz** 5.81 (2.19x) | **RapidFuzz** 14.7 (2.61x) | **RapidFuzz** 18.5 (3.16x) | **RapidFuzz** 11.5 (5.5x) | **RapidFuzz** 26.7 (5.71x) | **RapidFuzz** 55.3 (8.49x) |
| 10000 | sparse-u32 | **RapidFuzz** 5.78 (2.11x) | **RapidFuzz** 10.1 (1.98x) | **difffold** 68.2 (1.71x) | **RapidFuzz** 61.6 (1.32x) | **RapidFuzz** 34.7 (3.17x) | **RapidFuzz** 172 (2.85x) |
| 100000 | 2 | **WFA2** 20.7 (3.06x) | **WFA2** 24 (2.82x) | **WFA2** 23.2 (6.06x) | **WFA2** 24.1 (4.35x) | **WFA2** 24 (11x) | **WFA2** 24.1 (139x) |
| 100000 | 4 | **RapidFuzz** 17.8 (1.18x) | **WFA2** 32.6 (2.39x) | **WFA2** 24.4 (4.59x) | **WFA2** 23.6 (5.99x) | **WFA2** 20.3 (9.72x) | **WFA2** 24.1 (16.6x) |
| 100000 | 256 | **RapidFuzz** 20.3 (2.62x) | **RapidFuzz** 124 (2.83x) | **RapidFuzz** 100 (1.91x) | **RapidFuzz** 125 (3.42x) | **RapidFuzz** 363 (20.3x) | **RapidFuzz** 512 (141x) |
| 100000 | sparse-u32 | **RapidFuzz** 67.2 (1.52x) | **RapidFuzz** 159 (1.65x) | **difffold** 295 (2.46x) | **difffold** 276 (1.67x) | **RapidFuzz** 3.4e+03 (1.27x) | **RapidFuzz** 3.33e+03 (4.74x) |

### unrelated

| len | alphabet | k=1 | k=2 | k=4 | k=8 | k=32 | k=128 |
|---|---|---|---|---|---|---|---|
| 16 | 2 | **RapidFuzz** 0.025 (9.48x) | **RapidFuzz** 0.056 (3.95x) | **RapidFuzz** 0.102 (2.57x) | **RapidFuzz** 0.118 (2.3x) | k >= n | k >= n |
| 16 | 4 | **RapidFuzz** 0.038 (11.2x) | **RapidFuzz** 0.047 (5.26x) | **RapidFuzz** 0.099 (2.72x) | **RapidFuzz** 0.101 (5.94x) | k >= n | k >= n |
| 16 | 256 | **RapidFuzz** 0.023 (15.6x) | **RapidFuzz** 0.069 (8.17x) | **RapidFuzz** 0.093 (4.16x) | **RapidFuzz** 0.099 (8.29x) | k >= n | k >= n |
| 16 | sparse-u32 | **RapidFuzz** 0.023 (21x) | **RapidFuzz** 0.045 (6.02x) | **RapidFuzz** 0.135 (2.42x) | **RapidFuzz** 0.131 (2.75x) | k >= n | k >= n |
| 100 | 2 | **RapidFuzz** 0.031 (3x) | **RapidFuzz** 0.129 (1.37x) | **RapidFuzz** 0.323 (4x) | **RapidFuzz** 0.333 (3.8x) | **RapidFuzz** 1.45 (1.13x) | k >= n |
| 100 | 4 | **RapidFuzz** 0.024 (2.92x) | **RapidFuzz** 0.085 (2.21x) | **RapidFuzz** 0.217 (8x) | **RapidFuzz** 0.183 (6.22x) | **RapidFuzz** 1.29 (1.34x) | k >= n |
| 100 | 256 | **RapidFuzz** 0.024 (5.25x) | **RapidFuzz** 0.048 (1.69x) | **RapidFuzz** 0.153 (3.26x) | **RapidFuzz** 0.129 (14.2x) | **RapidFuzz** 1.36 (1.54x) | k >= n |
| 100 | sparse-u32 | **RapidFuzz** 0.038 (3.34x) | **RapidFuzz** 0.084 (2.05x) | **difffold** 0.136 (2.35x) | **RapidFuzz** 0.328 (9.13x) | **RapidFuzz** 1.35 (2.99x) | k >= n |
| 1000 | 2 | **RapidFuzz** 0.025 (3.32x) | **RapidFuzz** 0.12 (1.13x) | **RapidFuzz** 0.198 (3.6x) | **RapidFuzz** 0.298 (2.92x) | **RapidFuzz** 3.33 (1.12x) | **RapidFuzz** 8.73 (1.42x) |
| 1000 | 4 | **RapidFuzz** 0.036 (3.89x) | **RapidFuzz** 0.078 (2.62x) | **RapidFuzz** 0.121 (1.62x) | **RapidFuzz** 0.212 (4.68x) | **RapidFuzz** 2.55 (1.39x) | **RapidFuzz** 6.1 (1.99x) |
| 1000 | 256 | **RapidFuzz** 0.025 (2.44x) | **RapidFuzz** 0.045 (1.93x) | **RapidFuzz** 0.11 (1.25x) | **RapidFuzz** 0.117 (2.91x) | **RapidFuzz** 2.16 (1.52x) | **RapidFuzz** 3.55 (9.95x) |
| 1000 | sparse-u32 | **RapidFuzz** 0.024 (3x) | **RapidFuzz** 0.047 (1.68x) | **difffold** 0.131 (1.54x) | **difffold** 0.308 (1.04x) | **difffold** 3.06 (2.58x) | **RapidFuzz** 13.7 (3.17x) |
| 10000 | 2 | **RapidFuzz** 0.029 (3.55x) | **RapidFuzz** 0.066 (2.48x) | **RapidFuzz** 0.215 (1.34x) | **RapidFuzz** 0.293 (3.05x) | **WFA2** 4.53 (4.81x) | **RapidFuzz** 27.2 (1.27x) |
| 10000 | 4 | **RapidFuzz** 0.029 (2.34x) | **RapidFuzz** 0.094 (1.93x) | **RapidFuzz** 0.186 (2.22x) | **RapidFuzz** 0.366 (2.8x) | **WFA2** 4.34 (3.11x) | **RapidFuzz** 23.8 (1.44x) |
| 10000 | 256 | **RapidFuzz** 0.029 (2.28x) | **RapidFuzz** 0.052 (1.81x) | **RapidFuzz** 0.104 (1.22x) | **RapidFuzz** 0.139 (2.34x) | **difffold** 3.92 (6.85x) | **RapidFuzz** 33 (3.32x) |
| 10000 | sparse-u32 | **RapidFuzz** 0.031 (2.06x) | **RapidFuzz** 0.051 (2.1x) | **difffold** 0.143 (1.35x) | **RapidFuzz** 0.351 (1.41x) | **difffold** 3.42 (54.9x) | **difffold** 51.7 (3.37x) |
| 100000 | 2 | **RapidFuzz** 0.047 (2x) | **RapidFuzz** 0.066 (2.21x) | **RapidFuzz** 0.147 (1.91x) | **RapidFuzz** 0.572 (1.8x) | **WFA2** 14.6 (1.75x) | **WFA2** 47.5 (5.74x) |
| 100000 | 4 | **RapidFuzz** 0.029 (2.45x) | **RapidFuzz** 0.059 (1.97x) | **RapidFuzz** 0.134 (1.43x) | **RapidFuzz** 0.217 (2.66x) | **difffold** 8.04 (1.98x) | **WFA2** 39.8 (3.41x) |
| 100000 | 256 | **RapidFuzz** 0.029 (4.1x) | **RapidFuzz** 0.052 (3.38x) | **RapidFuzz** 0.171 (1.57x) | **RapidFuzz** 0.193 (2.81x) | **difffold** 7.82 (416x) | **difffold** 58 (7.16x) |
| 100000 | sparse-u32 | **RapidFuzz** 0.026 (4.65x) | **RapidFuzz** 0.05 (1.5x) | **RapidFuzz** 0.199 (1.47x) | **difffold** 0.287 (1.22x) | **difffold** 3.34 (1.94e+03x) | **difffold** 91.6 (82.4x) |


## Limitations

- One shared VM, pinned to one core, with one process per cell and 7 timed passes. Load varied between
  about 2 and 3 during the matrix. Treat ratios below about 1.3 as ties. Cells near the 60 second limit
  can change status between runs.
- Edlib and WFA2-lib are compiled without `-march`, so WFA2 uses its scalar kernels and Edlib uses its
  default code path. difffold and RapidFuzz are Rust release builds with the default target. Other flags
  or AVX2 builds may change the ordering.
- Only unit-cost Levenshtein is measured. The indel and gap-affine objectives are not.
- Edlib and WFA2 cannot take sparse symbols, so the sparse column is RapidFuzz and difffold only. WFA2
  also cannot take 256 dense symbols, because it needs its sentinel bytes.
- Timeouts (60 s for the whole cell) in the final run: WFA2 exact on 100,000 unrelated symbols at
  alphabets 2 and 4; RapidFuzz exact on 100,000 unrelated symbols at alphabets 2 and 4 and on sparse
  symbols for `d=16` and unrelated pairs; difffold exact on 100,000 unrelated symbols at alphabets 2, 4
  and sparse; Edlib exact on 100,000 unrelated symbols at alphabet 256. Edlib at alphabet 256 completed
  in the earlier run, so these are load-sensitive. They have no timing.
- Exact unrelated pairs at length 100,000 use RapidFuzz as the reference, because the band oracle would
  exceed its work budget. Those cells are consistent with each other, but they are not checked against an
  independent oracle. Their `oracle` column says `consensus-rapidfuzz`.
- The exact job and bounded job generate different pairs, so their pairs are not identical.
- The regime labels describe the designed edit count, not the realized distance. The TSV gives the
  realized median.
- Empty inputs are excluded from timing. Edlib's bounded path does not honour its bound for empty input
  (see Findings).
- difffold was measured at the branch tip that existed when this run started. The branch may still move.

## Reproduce

```
STRBENCH_EXT=<dir with edlib/ and WFA2-lib/ source trees at the tags above>
cd tools/strbench
cargo +1.89.0 test --release
cargo +1.89.0 build --release --bins
./run_matrix.sh target/release/bench /tmp/matrix.tsv all
python3 summarize.py /tmp/matrix.tsv
```
