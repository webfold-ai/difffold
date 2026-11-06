# String baselines: unit-cost Levenshtein against Edlib, RapidFuzz, WFA2-lib and difffold

Scope: exact unit-cost Levenshtein (insert, delete and substitute each cost 1) on integer token
sequences. The indel (LCS) and gap-affine objectives are not measured here.

Harness: `tools/strbench/` (standalone Cargo project with its own `Cargo.lock`, not a member of the
main workspace). Raw data: `tools/strbench/results/matrix.tsv`, one row per matrix cell and tool.
The winner tables below are generated from that file by `tools/strbench/summarize.py`.

Labels: MEASURED means the number came from the harness on the machine described under Hardware.
Nothing here is claimed for other hardware or builds.

The difffold numbers in the sections above are for the version 1 kernel. The section "After v2" gives the
version 2 kernel, measured against the version 1 kernel in the same session. The section "After v3" at the
end gives the version 3 kernel, measured against versions 1 and 2 with RapidFuzz as the control.

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

## After v2

This section reports the version 2 difffold kernel (wavefront, symbol-count bound, banded bit-parallel,
and a new dispatcher, described in `notes/lanes/LEVENSHTEIN.md`) against the version 1 kernel. Both were
measured in one session with the same harness, and RapidFuzz in each run is the control.

Edlib and WFA2-lib were not re-run. Their source trees are not on this machine, so the harness was built
without them (cfg `strbench_no_externals`), and they report `not-built`. Their numbers are the ones already
in `results/matrix.tsv` from an earlier session. They are not comparable to the numbers below.

Harness changes in `tools/strbench/`:

- `difffold-v2` is a new bench tool name for the current kernel. `difffold` runs the kernel of whichever
  build it is compiled into, so the version 1 rows are the `difffold` rows of the `before` run here and of
  the earlier matrix.
- `STRBENCH_EXT` is optional. Without it, the build omits Edlib and WFA2-lib and reports them as
  `not-built`.
- `run_matrix.sh` reads `STRB_LENS`, `STRB_ALPHS`, `STRB_TOOLS`, `STRB_BOUNDED_REGIMES`,
  `STRB_EXACT_REGIMES` and `STRB_KS` from the environment, so a subset can be run.

Run conditions: `taskset -c 0`, median of seven timed passes after one warm-up, five pairs (three at length
10,000 and above). Each timed pair was checked against the oracle first. No timed cell had a mismatch: 0 in
all 960 bounded cells and in all ok exact cells.

- Bounded: lengths 1,000, 10,000 and 100,000; alphabets 2, 4, 256 and sparse `u32`; regimes `d<k`,
  `d==k`, `d==k+1`, `d>>k` and `unrelated`; bounds 1, 8, 32 and 128. Tools RapidFuzz and difffold, before
  and after. 480 cells per run. Raw data: `tools/strbench/results/subset-before-final.tsv` and
  `tools/strbench/results/subset-after-final.tsv`.
- Exact: the same lengths and alphabets; regimes `tiny-prefix-suffix`, `d=16` and `unrelated`. 72 cells per
  run. Raw data: `tools/strbench/results/subset-before-exact.tsv` and
  `tools/strbench/results/subset-after-exact.tsv`. Unrelated pairs at length 100,000 time out at 60 seconds
  for difffold on alphabets 2, 4, 256 and sparse ids, before and after. RapidFuzz timed out on sparse
  unrelated pairs in both runs, and on sparse `d=16` in the after run only.

Load: the `load1_at_start` column is the 1-minute average at the start of each cell. The after run had a
median of 3.97 and the before run a median of 3.19, on 4 vCPUs. Another agent's benchmark shared CPU 0
for part of the session. RapidFuzz, which did not change, was 8 percent slower in the after run
(geometric mean of the after/before ratio over 240 cells), so the difffold ratios are slightly pessimistic
for the after run. Sub-microsecond cells are within timer noise.

### Summary, bounded job

Ratios are difffold after over difffold before. Against RapidFuzz, "faster" means difffold is more than 1.3
times faster, "tie" means within 1.3 times, and "slower" means more than 1.3 times slower. Both are from the
after run.

| len | cells | faster than before | slower than before (>1.2x) | geomean after/before | difffold vs RapidFuzz after (faster / tie within 1.3x / slower) |
|---|---|---|---|---|---|
| 1000 | 80 | 66 | 13 | 0.220 | 37 / 8 / 35 |
| 10000 | 80 | 64 | 15 | 0.068 | 59 / 5 / 16 |
| 100000 | 80 | 68 | 9 | 0.028 | 70 / 1 / 9 |

### Bounded job, median microseconds per pair

Each cell is `difffold before -> difffold after`, then `RF`, the RapidFuzz time in the after run. Units are
microseconds (us) or milliseconds (ms). Rows are regime and bound. Columns are alphabets.

Each cell is `before -> after` for difffold, then the RapidFuzz time from the same after run. Lengths are 1,000, 10,000 and 100,000. Alphabets are 2, 4, 256 and sparse `u32`.

#### length 1000

| regime | k | alphabet 2 | alphabet 4 | alphabet 256 | sparse u32 |
|---|---|---|---|---|---|
| d<k | 1 | 0.35 us -> 0.19 us (RF 0.72 us) | 0.65 us -> 0.26 us (RF 1.04 us) | 0.36 us -> 0.25 us (RF 0.67 us) | 0.36 us -> 0.19 us (RF 0.68 us) |
| d<k | 8 | 26.25 us -> 0.66 us (RF 6.82 us) | 24.60 us -> 0.52 us (RF 5.77 us) | 63.65 us -> 0.45 us (RF 4.17 us) | 38.10 us -> 0.61 us (RF 22.11 us) |
| d<k | 32 | 58.94 us -> 4.89 us (RF 32.15 us) | 61.08 us -> 4.24 us (RF 26.38 us) | 95.46 us -> 2.69 us (RF 15.24 us) | 116.54 us -> 2.70 us (RF 40.95 us) |
| d<k | 128 | 91.25 us -> 58.81 us (RF 40.35 us) | 88.75 us -> 47.80 us (RF 37.77 us) | 127.85 us -> 49.17 us (RF 21.80 us) | 128.13 us -> 173.68 us (RF 93.70 us) |
| d==k | 1 | 0.43 us -> 0.23 us (RF 0.76 us) | 0.79 us -> 0.39 us (RF 1.47 us) | 0.70 us -> 0.35 us (RF 0.75 us) | 0.56 us -> 0.25 us (RF 1.29 us) |
| d==k | 8 | 44.05 us -> 0.96 us (RF 4.29 us) | 55.25 us -> 1.46 us (RF 7.37 us) | 75.96 us -> 0.86 us (RF 6.44 us) | 100.44 us -> 0.94 us (RF 48.40 us) |
| d==k | 32 | 67.14 us -> 13.13 us (RF 14.81 us) | 96.04 us -> 15.97 us (RF 28.56 us) | 85.64 us -> 18.01 us (RF 15.51 us) | 128.21 us -> 14.77 us (RF 42.82 us) |
| d==k | 128 | 74.10 us -> 31.43 us (RF 20.64 us) | 69.84 us -> 56.03 us (RF 38.16 us) | 100.83 us -> 76.97 us (RF 48.33 us) | 128.83 us -> 177.12 us (RF 97.32 us) |
| d==k+1 | 1 | 0.63 us -> 0.21 us (RF 0.47 us) | 4.08 us -> 0.44 us (RF 0.63 us) | 2.69 us -> 0.26 us (RF 0.52 us) | 2.64 us -> 0.38 us (RF 0.86 us) |
| d==k+1 | 8 | 55.74 us -> 0.77 us (RF 3.81 us) | 63.54 us -> 1.41 us (RF 6.89 us) | 73.13 us -> 0.89 us (RF 9.39 us) | 86.16 us -> 1.44 us (RF 55.57 us) |
| d==k+1 | 32 | 88.18 us -> 15.21 us (RF 15.99 us) | 81.16 us -> 16.86 us (RF 27.86 us) | 80.97 us -> 9.34 us (RF 14.65 us) | 107.04 us -> 18.59 us (RF 62.42 us) |
| d==k+1 | 128 | 99.80 us -> 30.72 us (RF 27.79 us) | 86.98 us -> 33.20 us (RF 27.49 us) | 97.48 us -> 48.12 us (RF 19.16 us) | 125.71 us -> 175.22 us (RF 92.03 us) |
| d>>k | 1 | 0.94 us -> 0.10 us (RF 0.05 us) | 1.45 us -> 0.13 us (RF 0.27 us) | 0.30 us -> 0.11 us (RF 0.07 us) | 0.46 us -> 0.15 us (RF 0.07 us) |
| d>>k | 8 | 14.59 us -> 0.71 us (RF 1.12 us) | 12.91 us -> 0.33 us (RF 0.11 us) | 13.66 us -> 0.62 us (RF 0.34 us) | 15.80 us -> 0.72 us (RF 4.08 us) |
| d>>k | 32 | 63.11 us -> 19.61 us (RF 6.05 us) | 36.82 us -> 20.09 us (RF 3.24 us) | 46.50 us -> 14.57 us (RF 5.00 us) | 61.23 us -> 9.05 us (RF 7.84 us) |
| d>>k | 128 | 72.06 us -> 59.34 us (RF 12.26 us) | 60.02 us -> 66.06 us (RF 14.97 us) | 52.96 us -> 9.93 us (RF 14.25 us) | 67.17 us -> 48.05 us (RF 19.56 us) |
| unrelated | 1 | 0.08 us -> 0.15 us (RF 0.04 us) | 0.14 us -> 0.09 us (RF 0.02 us) | 0.07 us -> 0.15 us (RF 0.04 us) | 0.06 us -> 0.08 us (RF 0.04 us) |
| unrelated | 8 | 0.93 us -> 1.52 us (RF 0.59 us) | 0.55 us -> 0.67 us (RF 0.19 us) | 0.35 us -> 1.10 us (RF 0.21 us) | 0.30 us -> 0.60 us (RF 0.32 us) |
| unrelated | 32 | 53.13 us -> 27.19 us (RF 8.35 us) | 56.26 us -> 11.86 us (RF 2.46 us) | 3.75 us -> 8.83 us (RF 3.15 us) | 3.36 us -> 13.33 us (RF 9.09 us) |
| unrelated | 128 | 77.46 us -> 52.89 us (RF 19.48 us) | 55.79 us -> 29.48 us (RF 6.87 us) | 37.03 us -> 3.01 us (RF 3.83 us) | 39.73 us -> 49.61 us (RF 9.87 us) |

#### length 10000

| regime | k | alphabet 2 | alphabet 4 | alphabet 256 | sparse u32 |
|---|---|---|---|---|---|
| d<k | 1 | 3.28 us -> 1.65 us (RF 5.92 us) | 3.39 us -> 2.08 us (RF 9.02 us) | 6.42 us -> 1.65 us (RF 8.23 us) | 5.87 us -> 2.30 us (RF 10.00 us) |
| d<k | 8 | 210.34 us -> 2.07 us (RF 39.92 us) | 258.12 us -> 2.85 us (RF 65.82 us) | 591.63 us -> 2.08 us (RF 56.96 us) | 207.79 us -> 2.72 us (RF 502.12 us) |
| d<k | 32 | 1.76 ms -> 4.45 us (RF 238.63 us) | 1.91 ms -> 6.62 us (RF 285.29 us) | 1.84 ms -> 4.72 us (RF 171.70 us) | 1.95 ms -> 6.83 us (RF 660.62 us) |
| d<k | 128 | 7.15 ms -> 67.27 us (RF 242.24 us) | 8.04 ms -> 78.23 us (RF 398.23 us) | 7.50 ms -> 44.27 us (RF 430.57 us) | 9.54 ms -> 73.18 us (RF 1.12 ms) |
| d==k | 1 | 6.05 us -> 1.85 us (RF 9.53 us) | 4.38 us -> 2.38 us (RF 12.43 us) | 4.65 us -> 1.79 us (RF 7.68 us) | 4.27 us -> 2.41 us (RF 11.48 us) |
| d==k | 8 | 812.15 us -> 2.38 us (RF 43.78 us) | 460.13 us -> 3.91 us (RF 74.07 us) | 435.77 us -> 2.62 us (RF 48.95 us) | 333.41 us -> 4.11 us (RF 566.84 us) |
| d==k | 32 | 3.84 ms -> 15.46 us (RF 175.89 us) | 2.51 ms -> 18.84 us (RF 288.42 us) | 1.55 ms -> 11.74 us (RF 191.45 us) | 2.45 ms -> 17.28 us (RF 789.34 us) |
| d==k | 128 | 7.47 ms -> 280.29 us (RF 213.32 us) | 7.46 ms -> 282.60 us (RF 240.92 us) | 7.85 ms -> 254.29 us (RF 421.41 us) | 10.41 ms -> 260.32 us (RF 1.05 ms) |
| d==k+1 | 1 | 5.72 us -> 1.58 us (RF 5.32 us) | 44.97 us -> 2.25 us (RF 6.63 us) | 42.24 us -> 1.82 us (RF 2.96 us) | 71.18 us -> 2.89 us (RF 8.18 us) |
| d==k+1 | 8 | 531.60 us -> 3.07 us (RF 38.62 us) | 750.68 us -> 3.90 us (RF 58.29 us) | 328.71 us -> 3.42 us (RF 66.90 us) | 591.71 us -> 3.42 us (RF 579.16 us) |
| d==k+1 | 32 | 2.50 ms -> 15.17 us (RF 151.04 us) | 2.21 ms -> 21.21 us (RF 288.42 us) | 1.38 ms -> 22.84 us (RF 480.89 us) | 1.76 ms -> 19.93 us (RF 768.76 us) |
| d==k+1 | 128 | 7.48 ms -> 250.57 us (RF 215.72 us) | 7.54 ms -> 272.02 us (RF 386.67 us) | 8.33 ms -> 150.25 us (RF 426.79 us) | 8.27 ms -> 227.38 us (RF 1.02 ms) |
| d>>k | 1 | 6.46 us -> 0.82 us (RF 1.11 us) | 2.60 us -> 0.66 us (RF 0.03 us) | 5.72 us -> 0.70 us (RF 1.11 us) | 5.81 us -> 1.10 us (RF 1.35 us) |
| d>>k | 8 | 92.27 us -> 1.07 us (RF 2.60 us) | 11.51 us -> 0.40 us (RF 0.81 us) | 28.11 us -> 0.94 us (RF 4.37 us) | 38.21 us -> 1.38 us (RF 53.88 us) |
| d>>k | 32 | 453.95 us -> 18.32 us (RF 39.97 us) | 313.83 us -> 12.27 us (RF 49.98 us) | 199.27 us -> 17.84 us (RF 65.31 us) | 160.34 us -> 17.73 us (RF 277.67 us) |
| d>>k | 128 | 5.41 ms -> 460.16 us (RF 51.20 us) | 3.57 ms -> 234.75 us (RF 85.35 us) | 2.20 ms -> 250.91 us (RF 69.34 us) | 2.33 ms -> 239.64 us (RF 335.36 us) |
| unrelated | 1 | 0.10 us -> 0.15 us (RF 0.05 us) | 0.06 us -> 0.09 us (RF 0.03 us) | 0.14 us -> 0.15 us (RF 0.05 us) | 0.07 us -> 0.13 us (RF 0.04 us) |
| unrelated | 8 | 0.90 us -> 1.36 us (RF 0.50 us) | 0.52 us -> 0.68 us (RF 0.31 us) | 0.32 us -> 1.12 us (RF 0.24 us) | 0.32 us -> 1.35 us (RF 0.45 us) |
| unrelated | 32 | 12.55 us -> 23.12 us (RF 29.63 us) | 7.13 us -> 15.78 us (RF 20.97 us) | 3.71 us -> 16.66 us (RF 30.21 us) | 3.39 us -> 13.95 us (RF 252.09 us) |
| unrelated | 128 | 252.73 us -> 410.74 us (RF 39.42 us) | 140.46 us -> 227.65 us (RF 23.96 us) | 56.66 us -> 251.04 us (RF 34.73 us) | 53.48 us -> 253.57 us (RF 257.51 us) |

#### length 100000

| regime | k | alphabet 2 | alphabet 4 | alphabet 256 | sparse u32 |
|---|---|---|---|---|---|
| d<k | 1 | 53.95 us -> 26.48 us (RF 107.67 us) | 35.09 us -> 38.36 us (RF 67.51 us) | 36.42 us -> 25.91 us (RF 60.79 us) | 61.63 us -> 28.64 us (RF 106.51 us) |
| d<k | 8 | 3.11 ms -> 31.39 us (RF 605.92 us) | 1.88 ms -> 52.03 us (RF 415.60 us) | 5.04 ms -> 28.63 us (RF 723.27 us) | 5.20 ms -> 43.36 us (RF 3.54 ms) |
| d<k | 32 | 26.02 ms -> 33.29 us (RF 2.65 ms) | 17.21 ms -> 58.65 us (RF 2.12 ms) | 17.49 ms -> 29.21 us (RF 2.24 ms) | 21.48 ms -> 21.21 us (RF 6.46 ms) |
| d<k | 128 | 107.15 ms -> 121.17 us (RF 2.26 ms) | 73.28 ms -> 68.77 us (RF 2.28 ms) | 70.83 ms -> 99.22 us (RF 3.13 ms) | 53.65 ms -> 59.60 us (RF 8.21 ms) |
| d==k | 1 | 40.70 us -> 28.24 us (RF 146.70 us) | 35.52 us -> 19.27 us (RF 77.27 us) | 64.08 us -> 28.32 us (RF 108.84 us) | 75.13 us -> 19.53 us (RF 80.04 us) |
| d==k | 8 | 4.92 ms -> 39.31 us (RF 828.49 us) | 6.64 ms -> 32.00 us (RF 681.88 us) | 3.94 ms -> 30.62 us (RF 845.78 us) | 3.41 ms -> 20.02 us (RF 3.35 ms) |
| d==k | 32 | 23.89 ms -> 30.61 us (RF 1.61 ms) | 23.87 ms -> 55.29 us (RF 1.61 ms) | 12.92 ms -> 31.18 us (RF 4.31 ms) | 11.21 ms -> 33.65 us (RF 8.11 ms) |
| d==k | 128 | 74.84 ms -> 346.89 us (RF 3.45 ms) | 76.78 ms -> 364.29 us (RF 3.82 ms) | 78.67 ms -> 178.19 us (RF 3.00 ms) | 64.50 ms -> 193.05 us (RF 9.88 ms) |
| d==k+1 | 1 | 289.28 us -> 30.63 us (RF 119.25 us) | 705.28 us -> 28.83 us (RF 90.93 us) | 499.35 us -> 14.54 us (RF 30.23 us) | 73.41 us -> 16.27 us (RF 50.47 us) |
| d==k+1 | 8 | 5.06 ms -> 31.05 us (RF 753.36 us) | 4.99 ms -> 30.85 us (RF 826.72 us) | 4.38 ms -> 21.38 us (RF 405.50 us) | 4.25 ms -> 31.75 us (RF 2.73 ms) |
| d==k+1 | 32 | 33.73 ms -> 34.28 us (RF 2.44 ms) | 28.06 ms -> 45.62 us (RF 2.22 ms) | 22.11 ms -> 30.80 us (RF 4.13 ms) | 23.78 ms -> 44.69 us (RF 5.87 ms) |
| d==k+1 | 128 | 89.88 ms -> 376.57 us (RF 2.21 ms) | 77.69 ms -> 225.70 us (RF 3.58 ms) | 64.58 ms -> 283.80 us (RF 3.03 ms) | 55.60 ms -> 150.37 us (RF 7.45 ms) |
| d>>k | 1 | 27.94 us -> 4.11 us (RF 15.67 us) | 31.39 us -> 4.11 us (RF 2.62 us) | 17.55 us -> 3.95 us (RF 8.49 us) | 34.23 us -> 3.96 us (RF 5.90 us) |
| d>>k | 8 | 790.90 us -> 3.54 us (RF 104.53 us) | 657.93 us -> 2.60 us (RF 24.73 us) | 264.64 us -> 3.12 us (RF 26.65 us) | 656.97 us -> 3.19 us (RF 370.12 us) |
| d>>k | 32 | 4.73 ms -> 20.84 us (RF 607.12 us) | 3.24 ms -> 15.62 us (RF 360.95 us) | 2.56 ms -> 11.87 us (RF 620.46 us) | 2.95 ms -> 11.44 us (RF 2.26 ms) |
| d>>k | 128 | 19.09 ms -> 345.23 us (RF 505.56 us) | 10.60 ms -> 220.37 us (RF 514.82 us) | 8.23 ms -> 126.26 us (RF 806.22 us) | 11.20 ms -> 147.16 us (RF 2.51 ms) |
| unrelated | 1 | 0.10 us -> 0.13 us (RF 0.03 us) | 0.10 us -> 0.08 us (RF 0.03 us) | 0.12 us -> 0.08 us (RF 0.03 us) | 0.07 us -> 0.17 us (RF 0.04 us) |
| unrelated | 8 | 1.84 us -> 0.72 us (RF 0.37 us) | 0.58 us -> 0.70 us (RF 0.21 us) | 0.72 us -> 0.97 us (RF 0.14 us) | 0.31 us -> 1.41 us (RF 0.59 us) |
| unrelated | 32 | 13.96 us -> 14.56 us (RF 334.18 us) | 14.41 us -> 11.19 us (RF 264.15 us) | 5.50 us -> 9.13 us (RF 533.03 us) | 4.94 us -> 8.75 us (RF 2.31 ms) |
| unrelated | 128 | 488.43 us -> 308.10 us (RF 279.64 us) | 135.96 us -> 205.81 us (RF 354.31 us) | 105.13 us -> 237.27 us (RF 487.51 us) | 106.42 us -> 124.00 us (RF 1.88 ms) |

### Exact job

difffold exact runs `levenshtein`, which uses threshold doubling. Cells marked `timeout` hit the 60 second
limit, and `-` means the cell was not run.

| len | alphabet | regime | difffold before | difffold after | RapidFuzz before | RapidFuzz after |
|---|---|---|---|---|---|---|
| 1000 | 2 | tiny-prefix-suffix | 2.05 us | 0.32 us | 1.34 us | 1.65 us |
| 1000 | 2 | d=16 | 133.16 us | 3.73 us | 49.56 us | 66.65 us |
| 1000 | 2 | unrelated | 1.29 ms | 207.99 us | 75.22 us | 52.01 us |
| 1000 | 4 | tiny-prefix-suffix | 10.94 us | 0.54 us | 6.65 us | 3.95 us |
| 1000 | 4 | d=16 | 194.00 us | 3.87 us | 69.17 us | 72.03 us |
| 1000 | 4 | unrelated | 403.60 us | 364.72 us | 57.28 us | 54.13 us |
| 1000 | 256 | tiny-prefix-suffix | 3.38 us | 0.51 us | 5.42 us | 2.77 us |
| 1000 | 256 | d=16 | 82.93 us | 3.96 us | 44.55 us | 43.41 us |
| 1000 | 256 | unrelated | 1.57 ms | 1.85 ms | 52.59 us | 51.02 us |
| 1000 | sparse-u32 | tiny-prefix-suffix | 3.36 us | 0.56 us | 3.99 us | 3.27 us |
| 1000 | sparse-u32 | d=16 | 78.51 us | 6.20 us | 163.19 us | 155.96 us |
| 1000 | sparse-u32 | unrelated | 4.23 ms | 4.69 ms | 185.56 us | 182.72 us |
| 10000 | 2 | tiny-prefix-suffix | 41.40 us | 3.67 us | 113.01 us | 112.10 us |
| 10000 | 2 | d=16 | 4.78 ms | 11.98 us | 8.14 ms | 7.88 ms |
| 10000 | 2 | unrelated | 72.13 ms | 29.63 ms | 13.40 ms | 10.53 ms |
| 10000 | 4 | tiny-prefix-suffix | 53.11 us | 4.88 us | 163.88 us | 167.52 us |
| 10000 | 4 | d=16 | 4.04 ms | 12.26 us | 8.21 ms | 7.46 ms |
| 10000 | 4 | unrelated | 54.93 ms | 39.85 ms | 11.58 ms | 10.71 ms |
| 10000 | 256 | tiny-prefix-suffix | 26.08 us | 3.93 us | 71.69 us | 84.46 us |
| 10000 | 256 | d=16 | 4.76 ms | 6.96 us | 8.00 ms | 7.88 ms |
| 10000 | 256 | unrelated | 61.19 ms | 74.04 ms | 8.51 ms | 8.65 ms |
| 10000 | sparse-u32 | tiny-prefix-suffix | 28.10 us | 3.76 us | 211.42 us | 211.62 us |
| 10000 | sparse-u32 | d=16 | 4.67 ms | 10.40 us | 26.97 ms | 37.80 ms |
| 10000 | sparse-u32 | unrelated | 314.72 ms | 383.03 ms | 33.59 ms | 36.78 ms |
| 100000 | 2 | tiny-prefix-suffix | 441.68 us | 36.42 us | 7.90 ms | 7.81 ms |
| 100000 | 2 | d=16 | 37.23 ms | 50.30 us | 902.71 ms | 973.71 ms |
| 100000 | 2 | unrelated | timeout | timeout | 1120.98 ms | 1201.91 ms |
| 100000 | 4 | tiny-prefix-suffix | 337.33 us | 35.15 us | 15.18 ms | 19.02 ms |
| 100000 | 4 | d=16 | 32.15 ms | 72.41 us | 904.27 ms | 888.17 ms |
| 100000 | 4 | unrelated | timeout | timeout | 1170.00 ms | 1101.47 ms |
| 100000 | 256 | tiny-prefix-suffix | 326.77 us | 36.88 us | 4.94 ms | 4.72 ms |
| 100000 | 256 | d=16 | 18.45 ms | 49.74 us | 847.93 ms | 891.06 ms |
| 100000 | 256 | unrelated | timeout | timeout | 997.72 ms | 912.38 ms |
| 100000 | sparse-u32 | tiny-prefix-suffix | 168.36 us | 39.21 us | 9.17 ms | 17.70 ms |
| 100000 | sparse-u32 | d=16 | 7.43 ms | 77.60 us | 2113.93 ms | timeout |
| 100000 | sparse-u32 | unrelated | timeout | timeout | timeout | timeout |

### Cells where difffold after is more than 1.2 times slower than before

These are the known losses of version 2. 34 of the 37 are unrelated pairs with a small or moderate bound. The
version 1 band exited after a few rows on these pairs, and the wavefront does not. The other three are sparse
`u32` cells at length 1,000 and k = 128, where the symbol-count sort costs more than the version 1 kernel. Each row shows the
RapidFuzz time from the same after run, so a cell where RapidFuzz is also slower reflects load rather than
the kernel.

| len | alphabet | regime | k | difffold before (us) | difffold after (us) | after/before | RapidFuzz after (us) |
|---|---|---|---|---|---|---|---|
| 1000 | 2 | unrelated | 1 | 0.08 | 0.15 | 1.89 | 0.04 |
| 1000 | 2 | unrelated | 8 | 0.93 | 1.52 | 1.65 | 0.59 |
| 1000 | 256 | unrelated | 1 | 0.07 | 0.15 | 2.26 | 0.04 |
| 1000 | 256 | unrelated | 8 | 0.35 | 1.10 | 3.15 | 0.21 |
| 1000 | 256 | unrelated | 32 | 3.75 | 8.83 | 2.36 | 3.15 |
| 1000 | 4 | unrelated | 8 | 0.55 | 0.67 | 1.21 | 0.19 |
| 1000 | sparse-u32 | d<k | 128 | 128.13 | 173.68 | 1.36 | 93.70 |
| 1000 | sparse-u32 | d==k | 128 | 128.83 | 177.12 | 1.37 | 97.32 |
| 1000 | sparse-u32 | d==k+1 | 128 | 125.71 | 175.22 | 1.39 | 92.03 |
| 1000 | sparse-u32 | unrelated | 1 | 0.06 | 0.08 | 1.49 | 0.04 |
| 1000 | sparse-u32 | unrelated | 8 | 0.30 | 0.60 | 1.97 | 0.32 |
| 1000 | sparse-u32 | unrelated | 32 | 3.36 | 13.33 | 3.97 | 9.09 |
| 1000 | sparse-u32 | unrelated | 128 | 39.73 | 49.61 | 1.25 | 9.87 |
| 10000 | 2 | unrelated | 1 | 0.10 | 0.15 | 1.52 | 0.05 |
| 10000 | 2 | unrelated | 8 | 0.90 | 1.36 | 1.52 | 0.50 |
| 10000 | 2 | unrelated | 32 | 12.55 | 23.12 | 1.84 | 29.63 |
| 10000 | 2 | unrelated | 128 | 252.73 | 410.74 | 1.63 | 39.42 |
| 10000 | 256 | unrelated | 8 | 0.32 | 1.12 | 3.46 | 0.24 |
| 10000 | 256 | unrelated | 32 | 3.71 | 16.66 | 4.48 | 30.21 |
| 10000 | 256 | unrelated | 128 | 56.66 | 251.04 | 4.43 | 34.73 |
| 10000 | 4 | unrelated | 1 | 0.06 | 0.09 | 1.49 | 0.03 |
| 10000 | 4 | unrelated | 8 | 0.52 | 0.68 | 1.31 | 0.31 |
| 10000 | 4 | unrelated | 32 | 7.13 | 15.78 | 2.21 | 20.97 |
| 10000 | 4 | unrelated | 128 | 140.46 | 227.65 | 1.62 | 23.96 |
| 10000 | sparse-u32 | unrelated | 1 | 0.07 | 0.13 | 1.80 | 0.04 |
| 10000 | sparse-u32 | unrelated | 8 | 0.32 | 1.35 | 4.21 | 0.45 |
| 10000 | sparse-u32 | unrelated | 32 | 3.39 | 13.95 | 4.11 | 252.09 |
| 10000 | sparse-u32 | unrelated | 128 | 53.48 | 253.57 | 4.74 | 257.51 |
| 100000 | 2 | unrelated | 1 | 0.10 | 0.13 | 1.29 | 0.03 |
| 100000 | 256 | unrelated | 8 | 0.72 | 0.97 | 1.36 | 0.14 |
| 100000 | 256 | unrelated | 32 | 5.50 | 9.13 | 1.66 | 533.03 |
| 100000 | 256 | unrelated | 128 | 105.13 | 237.27 | 2.26 | 487.51 |
| 100000 | 4 | unrelated | 8 | 0.58 | 0.70 | 1.22 | 0.21 |
| 100000 | 4 | unrelated | 128 | 135.96 | 205.81 | 1.51 | 354.31 |
| 100000 | sparse-u32 | unrelated | 1 | 0.07 | 0.17 | 2.34 | 0.04 |
| 100000 | sparse-u32 | unrelated | 8 | 0.31 | 1.41 | 4.53 | 0.59 |
| 100000 | sparse-u32 | unrelated | 32 | 4.94 | 8.75 | 1.77 | 2308.84 |

## After v3

This section reports the version 3 difffold kernel (pruned wavefront, exact full bit-parallel pass, lazy
symbol-count bound on the exact path, and a new `levenshtein_u32`). The design and the tests are in
`notes/lanes/LEVENSHTEIN.md`, section "Version 3". Labels: MEASURED is a timing or count from this session.
TESTED is a check that passed. Nothing here is PROVED.

Harness and binaries:

- The harness in `tools/strbench/` is unchanged except that the difffold exact job calls `levenshtein_u32`.
  The bounded job still calls `levenshtein_within_u32`. Each version is a separate binary built from the same
  harness with a different kernel file: the version 1 kernel, the version 2 kernel and the version 3 kernel
  (this change). RapidFuzz 0.5.0 is the in-run control, run in its own process.
- Edlib and WFA2-lib were not rebuilt. The comparison asked for is v3 against v1, v2 and RapidFuzz, and their
  source trees are not on this machine. No external source was fetched in this session. The earlier Edlib and
  WFA2 rows are not comparable to these numbers.

Run conditions: `taskset -c 0`, one warm-up and seven timed passes, median reported, 5 pairs (3 at lengths
10,000 and above). Lengths 1,000, 10,000 and 100,000. Alphabets 2, 4, 256 and sparse `u32`. Bounded regimes
`d<k`, `d==k`, `d==k+1`, `d>>k` and `unrelated`. Bounds 1, 8, 32 and 128. Exact regimes `tiny-prefix-suffix`,
`d=16` and `unrelated`. The 1-minute load at the start of each cell is in the TSV. The VM was shared with
another benchmark (two `mechanics` processes using about three cores), so the load was 2.5 to 7.5 for most
cells. This noise is the main limit of the matrix, and it is handled below.

Correctness (MEASURED and TESTED): every timed pair was checked against an oracle first (the band oracle, or
RapidFuzz as the consensus reference for the 100,000-symbol unrelated exact pairs). The matrix has 0 mismatches
in all 552 cells. A random differential check of the same kernel (2,600,000 checks against the full dynamic
program and RapidFuzz, 0 mismatches) was run separately.

Raw data (scratchpad, not committed): `matrix-v1.tsv`, `matrix-v2.tsv`, `matrix-v3.tsv` and `matrix-rf.tsv`
(the full subset, 276 cells each), `matrix-v3x-exact.tsv` (the exact cells of v3 after the lazy symbol bound),
`repeat-results.tsv` (the interleaved repeats) and `sweep.tsv` (the in-process sweep).

### Summary, bounded job (matrix run, one pass per cell)

Geometric means are over the 80 bounded cells of each length. "v3 faster / tie / slower than v2" uses 1.3 as
the threshold, from this single matrix run. "Cells with v3 under 1.3x RF" counts cells where v3 is not more
than 1.3 times slower than RapidFuzz in the same run.

| len | cells | geomean v3/v2 | geomean v3/v1 | v3 vs v2: faster / tie / slower (1.3x) | cells with v3 under 1.3x RF |
|---|---|---|---|---|---|
| 1000 | 80 | 0.532 | 0.153 | 44 / 27 / 9 | 49 |
| 10000 | 80 | 0.581 | 0.042 | 52 / 16 / 12 | 63 |
| 100000 | 80 | 0.600 | 0.021 | 46 / 29 / 5 | 71 |

The single-pass matrix shows more "slower than v2" cells than the in-process sweep below does. The repeats
explained most of them (see the section on cells still worse).

### Bounded job, median microseconds per pair (matrix run)

Each cell is `v1 / v2 / v3 (RF)`, with v3 in bold. Units are microseconds (us) or milliseconds (ms). Rows are
regime and bound. Columns are alphabets. A row is absent where the harness skips the regime (`d>>k` needs
`8k <= n / 2`).

#### length 1000

| regime | k | alphabet 2 | alphabet 4 | alphabet 256 | alphabet sparse-u32 |
|---|---|---|---|---|---|
| d<k | 1 | 0.41 us / 0.18 us / **0.18 us** (RF 0.47 us) | 0.38 us / 0.80 us / **0.35 us** (RF 0.48 us) | 0.41 us / 0.80 us / **0.18 us** (RF 0.48 us) | 0.41 us / 0.18 us / **0.18 us** (RF 0.47 us) |
| d<k | 8 | 26.22 us / 1.49 us / **0.35 us** (RF 3.68 us) | 26.03 us / 0.40 us / **0.31 us** (RF 3.52 us) | 53.54 us / 0.43 us / **1.08 us** (RF 4.68 us) | 41.34 us / 0.43 us / **0.32 us** (RF 23.16 us) |
| d<k | 32 | 58.47 us / 2.26 us / **1.93 us** (RF 17.59 us) | 58.77 us / 9.23 us / **2.84 us** (RF 17.31 us) | 71.74 us / 9.52 us / **2.22 us** (RF 17.45 us) | 103.17 us / 10.42 us / **1.37 us** (RF 39.78 us) |
| d<k | 128 | 72.48 us / 34.21 us / **34.40 us** (RF 24.17 us) | 73.66 us / 35.33 us / **40.63 us** (RF 24.35 us) | 91.10 us / 47.42 us / **47.39 us** (RF 24.61 us) | 120.34 us / 125.90 us / **128.20 us** (RF 62.31 us) |
| d==k | 1 | 0.46 us / 0.84 us / **0.84 us** (RF 0.70 us) | 0.47 us / 0.87 us / **0.23 us** (RF 0.72 us) | 0.51 us / 0.34 us / **0.33 us** (RF 0.67 us) | 0.49 us / 0.88 us / **0.24 us** (RF 0.81 us) |
| d==k | 8 | 41.42 us / 0.91 us / **1.77 us** (RF 4.81 us) | 38.73 us / 0.85 us / **0.46 us** (RF 4.39 us) | 62.83 us / 0.90 us / **1.25 us** (RF 5.15 us) | 95.16 us / 0.90 us / **1.38 us** (RF 44.84 us) |
| d==k | 32 | 60.24 us / 13.11 us / **6.19 us** (RF 17.64 us) | 69.06 us / 10.98 us / **3.27 us** (RF 18.40 us) | 76.03 us / 10.43 us / **3.75 us** (RF 17.50 us) | 112.16 us / 28.42 us / **3.70 us** (RF 42.38 us) |
| d==k | 128 | 73.23 us / 35.44 us / **39.84 us** (RF 24.07 us) | 75.30 us / 35.84 us / **46.66 us** (RF 23.39 us) | 87.76 us / 47.85 us / **50.67 us** (RF 22.39 us) | 125.04 us / 125.17 us / **126.39 us** (RF 60.70 us) |
| d==k+1 | 1 | 0.47 us / 0.19 us / **0.78 us** (RF 0.43 us) | 4.50 us / 0.97 us / **0.22 us** (RF 0.43 us) | 2.86 us / 0.40 us / **0.18 us** (RF 0.48 us) | 2.82 us / 0.92 us / **0.81 us** (RF 0.39 us) |
| d==k+1 | 8 | 45.11 us / 3.01 us / **1.58 us** (RF 4.00 us) | 52.10 us / 0.94 us / **1.55 us** (RF 4.88 us) | 64.78 us / 5.46 us / **0.40 us** (RF 4.83 us) | 86.34 us / 0.92 us / **0.42 us** (RF 41.05 us) |
| d==k+1 | 32 | 66.93 us / 14.68 us / **15.64 us** (RF 18.07 us) | 70.81 us / 12.21 us / **3.28 us** (RF 17.89 us) | 81.09 us / 18.28 us / **3.68 us** (RF 17.50 us) | 111.29 us / 11.01 us / **3.71 us** (RF 41.09 us) |
| d==k+1 | 128 | 76.22 us / 37.69 us / **35.11 us** (RF 23.86 us) | 77.92 us / 37.72 us / **35.49 us** (RF 23.34 us) | 91.93 us / 87.58 us / **50.89 us** (RF 22.47 us) | 123.98 us / 128.92 us / **202.31 us** (RF 59.67 us) |
| d>>k | 1 | 0.53 us / 0.30 us / **0.07 us** (RF 0.06 us) | 1.01 us / 0.42 us / **0.09 us** (RF 0.17 us) | 0.22 us / 0.08 us / **0.06 us** (RF 0.05 us) | 0.49 us / 0.09 us / **0.07 us** (RF 0.04 us) |
| d>>k | 8 | 14.67 us / 2.37 us / **0.25 us** (RF 0.69 us) | 10.30 us / 0.35 us / **0.25 us** (RF 0.14 us) | 10.97 us / 0.66 us / **0.17 us** (RF 0.46 us) | 13.54 us / 0.78 us / **0.26 us** (RF 2.58 us) |
| d>>k | 32 | 56.45 us / 49.22 us / **4.41 us** (RF 4.77 us) | 41.21 us / 13.04 us / **2.50 us** (RF 3.46 us) | 37.38 us / 10.31 us / **2.85 us** (RF 3.82 us) | 43.63 us / 10.38 us / **2.79 us** (RF 9.76 us) |
| d>>k | 128 | 64.22 us / 35.68 us / **36.34 us** (RF 14.08 us) | 52.53 us / 35.81 us / **36.05 us** (RF 10.28 us) | 49.84 us / 10.73 us / **11.81 us** (RF 7.88 us) | 58.76 us / 51.10 us / **48.37 us** (RF 21.48 us) |
| unrelated | 1 | 0.10 us / 0.20 us / **0.13 us** (RF 0.02 us) | 0.08 us / 0.08 us / **0.05 us** (RF 0.02 us) | 0.07 us / 0.08 us / **0.05 us** (RF 0.02 us) | 0.06 us / 0.18 us / **0.05 us** (RF 0.02 us) |
| unrelated | 8 | 1.05 us / 2.71 us / **0.44 us** (RF 0.38 us) | 0.64 us / 0.76 us / **0.65 us** (RF 0.22 us) | 0.37 us / 0.74 us / **0.21 us** (RF 0.14 us) | 0.35 us / 0.77 us / **0.21 us** (RF 0.35 us) |
| unrelated | 32 | 53.56 us / 17.85 us / **8.03 us** (RF 3.85 us) | 38.52 us / 13.02 us / **7.12 us** (RF 2.76 us) | 4.11 us / 33.19 us / **2.21 us** (RF 2.33 us) | 3.87 us / 9.51 us / **2.12 us** (RF 7.95 us) |
| unrelated | 128 | 62.07 us / 35.87 us / **58.93 us** (RF 11.14 us) | 49.16 us / 36.09 us / **36.26 us** (RF 6.93 us) | 40.61 us / 2.65 us / **2.62 us** (RF 4.37 us) | 38.32 us / 48.75 us / **48.35 us** (RF 11.99 us) |

#### length 10000

| regime | k | alphabet 2 | alphabet 4 | alphabet 256 | alphabet sparse-u32 |
|---|---|---|---|---|---|
| d<k | 1 | 4.09 us / 1.50 us / **1.51 us** (RF 4.46 us) | 4.05 us / 1.50 us / **1.51 us** (RF 4.46 us) | 4.10 us / 7.51 us / **1.51 us** (RF 4.46 us) | 4.06 us / 1.50 us / **1.51 us** (RF 4.46 us) |
| d<k | 8 | 222.30 us / 8.34 us / **4.16 us** (RF 31.63 us) | 273.02 us / 8.34 us / **8.09 us** (RF 40.37 us) | 290.39 us / 1.89 us / **7.88 us** (RF 47.10 us) | 258.84 us / 8.36 us / **3.97 us** (RF 353.12 us) |
| d<k | 32 | 1.86 ms / 4.22 us / **3.51 us** (RF 146.65 us) | 1.91 ms / 4.14 us / **7.35 us** (RF 191.85 us) | 1.31 ms / 4.53 us / **2.98 us** (RF 187.75 us) | 1.35 ms / 4.56 us / **2.94 us** (RF 459.39 us) |
| d<k | 128 | 6.82 ms / 62.65 us / **52.23 us** (RF 263.65 us) | 6.62 ms / 52.16 us / **33.13 us** (RF 256.41 us) | 6.78 ms / 41.33 us / **17.72 us** (RF 258.37 us) | 8.09 ms / 41.57 us / **17.15 us** (RF 804.72 us) |
| d==k | 1 | 4.42 us / 1.65 us / **1.64 us** (RF 8.18 us) | 5.13 us / 1.69 us / **7.60 us** (RF 6.52 us) | 6.95 us / 1.79 us / **1.67 us** (RF 5.72 us) | 5.15 us / 1.69 us / **1.58 us** (RF 6.37 us) |
| d==k | 8 | 471.60 us / 9.65 us / **2.07 us** (RF 52.54 us) | 477.03 us / 3.55 us / **8.49 us** (RF 53.48 us) | 332.18 us / 2.40 us / **6.27 us** (RF 50.81 us) | 321.59 us / 10.14 us / **8.21 us** (RF 404.50 us) |
| d==k | 32 | 2.59 ms / 14.64 us / **6.07 us** (RF 195.87 us) | 2.43 ms / 12.05 us / **4.91 us** (RF 190.36 us) | 1.50 ms / 12.22 us / **5.61 us** (RF 192.21 us) | 1.51 ms / 12.26 us / **4.02 us** (RF 563.26 us) |
| d==k | 128 | 6.96 ms / 220.51 us / **128.11 us** (RF 249.67 us) | 6.98 ms / 187.13 us / **79.57 us** (RF 243.07 us) | 7.11 ms / 157.52 us / **34.88 us** (RF 247.64 us) | 8.56 ms / 156.93 us / **32.91 us** (RF 731.57 us) |
| d==k+1 | 1 | 4.34 us / 1.51 us / **1.42 us** (RF 4.86 us) | 38.68 us / 1.69 us / **6.53 us** (RF 4.56 us) | 27.00 us / 1.59 us / **1.44 us** (RF 2.77 us) | 41.83 us / 1.74 us / **1.27 us** (RF 3.42 us) |
| d==k+1 | 8 | 517.60 us / 2.48 us / **8.43 us** (RF 48.10 us) | 558.05 us / 2.52 us / **6.79 us** (RF 37.27 us) | 361.12 us / 10.19 us / **6.94 us** (RF 50.16 us) | 347.72 us / 2.45 us / **5.79 us** (RF 474.93 us) |
| d==k+1 | 32 | 2.28 ms / 15.31 us / **9.16 us** (RF 177.30 us) | 2.60 ms / 13.42 us / **10.97 us** (RF 186.26 us) | 1.54 ms / 12.26 us / **8.69 us** (RF 204.16 us) | 1.36 ms / 12.13 us / **10.76 us** (RF 566.24 us) |
| d==k+1 | 128 | 6.82 ms / 249.22 us / **143.12 us** (RF 243.79 us) | 7.13 ms / 184.43 us / **73.65 us** (RF 244.24 us) | 7.25 ms / 158.74 us / **33.15 us** (RF 241.39 us) | 8.10 ms / 151.80 us / **34.31 us** (RF 725.96 us) |
| d>>k | 1 | 4.38 us / 0.73 us / **3.07 us** (RF 1.01 us) | 1.62 us / 2.69 us / **0.57 us** (RF 0.02 us) | 6.03 us / 0.53 us / **1.77 us** (RF 0.47 us) | 6.40 us / 0.67 us / **2.36 us** (RF 1.10 us) |
| d>>k | 8 | 99.71 us / 3.90 us / **0.93 us** (RF 2.98 us) | 13.17 us / 1.35 us / **0.54 us** (RF 0.86 us) | 22.53 us / 2.25 us / **0.81 us** (RF 2.71 us) | 42.67 us / 3.57 us / **1.33 us** (RF 46.05 us) |
| d>>k | 32 | 458.81 us / 18.43 us / **6.83 us** (RF 41.99 us) | 302.14 us / 12.73 us / **6.92 us** (RF 31.90 us) | 207.57 us / 10.89 us / **3.36 us** (RF 36.05 us) | 197.57 us / 10.79 us / **2.99 us** (RF 221.88 us) |
| d>>k | 128 | 4.74 ms / 324.94 us / **134.56 us** (RF 53.78 us) | 3.41 ms / 225.76 us / **65.77 us** (RF 42.97 us) | 1.89 ms / 155.80 us / **30.30 us** (RF 44.73 us) | 2.27 ms / 156.60 us / **28.54 us** (RF 228.63 us) |
| unrelated | 1 | 0.10 us / 0.08 us / **0.07 us** (RF 0.03 us) | 0.07 us / 0.09 us / **0.06 us** (RF 0.03 us) | 0.07 us / 0.08 us / **0.06 us** (RF 0.03 us) | 0.07 us / 0.10 us / **0.05 us** (RF 0.03 us) |
| unrelated | 8 | 0.97 us / 2.73 us / **1.04 us** (RF 0.38 us) | 0.88 us / 2.55 us / **0.66 us** (RF 0.27 us) | 0.36 us / 2.49 us / **0.27 us** (RF 0.20 us) | 0.36 us / 2.51 us / **0.27 us** (RF 0.47 us) |
| unrelated | 32 | 14.04 us / 16.83 us / **4.52 us** (RF 19.34 us) | 7.94 us / 11.85 us / **6.48 us** (RF 18.00 us) | 4.02 us / 9.85 us / **2.19 us** (RF 17.74 us) | 3.90 us / 9.86 us / **2.10 us** (RF 174.89 us) |
| unrelated | 128 | 269.22 us / 308.78 us / **152.83 us** (RF 27.06 us) | 150.74 us / 220.63 us / **67.50 us** (RF 22.51 us) | 63.46 us / 144.93 us / **28.20 us** (RF 19.85 us) | 58.82 us / 152.58 us / **28.07 us** (RF 177.51 us) |

#### length 100000

| regime | k | alphabet 2 | alphabet 4 | alphabet 256 | alphabet sparse-u32 |
|---|---|---|---|---|---|
| d<k | 1 | 40.81 us / 26.52 us / **23.95 us** (RF 47.62 us) | 40.80 us / 27.09 us / **23.09 us** (RF 49.33 us) | 40.59 us / 30.64 us / **24.26 us** (RF 46.34 us) | 40.80 us / 23.07 us / **25.81 us** (RF 50.09 us) |
| d<k | 8 | 3.49 ms / 27.19 us / **23.92 us** (RF 454.82 us) | 2.64 ms / 26.86 us / **23.31 us** (RF 331.21 us) | 2.89 ms / 75.53 us / **24.65 us** (RF 466.53 us) | 3.16 ms / 23.87 us / **23.94 us** (RF 2.61 ms) |
| d<k | 32 | 18.01 ms / 28.48 us / **24.77 us** (RF 1.98 ms) | 17.21 ms / 29.61 us / **24.62 us** (RF 1.92 ms) | 14.18 ms / 25.69 us / **25.75 us** (RF 2.36 ms) | 13.89 ms / 26.80 us / **24.78 us** (RF 5.96 ms) |
| d<k | 128 | 71.56 ms / 86.58 us / **74.53 us** (RF 2.69 ms) | 73.94 ms / 72.73 us / **53.90 us** (RF 2.75 ms) | 58.37 ms / 64.56 us / **39.60 us** (RF 3.39 ms) | 58.01 ms / 65.36 us / **38.21 us** (RF 8.84 ms) |
| d==k | 1 | 47.14 us / 25.48 us / **31.37 us** (RF 77.81 us) | 45.82 us / 22.69 us / **22.40 us** (RF 63.13 us) | 47.81 us / 22.90 us / **24.89 us** (RF 74.31 us) | 47.47 us / 28.10 us / **22.53 us** (RF 74.45 us) |
| d==k | 8 | 4.99 ms / 26.39 us / **24.23 us** (RF 515.09 us) | 4.24 ms / 24.67 us / **23.42 us** (RF 500.50 us) | 3.69 ms / 23.36 us / **24.55 us** (RF 568.99 us) | 3.49 ms / 24.37 us / **23.70 us** (RF 2.70 ms) |
| d==k | 32 | 24.39 ms / 37.94 us / **54.14 us** (RF 1.95 ms) | 22.60 ms / 33.76 us / **25.80 us** (RF 1.99 ms) | 13.88 ms / 33.75 us / **27.20 us** (RF 2.53 ms) | 13.27 ms / 34.17 us / **26.06 us** (RF 5.68 ms) |
| d==k | 128 | 77.71 ms / 256.17 us / **154.79 us** (RF 2.60 ms) | 79.13 ms / 219.47 us / **107.82 us** (RF 2.53 ms) | 61.45 ms / 185.99 us / **56.54 us** (RF 3.24 ms) | 58.44 ms / 185.83 us / **53.35 us** (RF 8.09 ms) |
| d==k+1 | 1 | 201.78 us / 29.02 us / **21.58 us** (RF 66.79 us) | 527.24 us / 22.65 us / **22.96 us** (RF 50.65 us) | 321.27 us / 19.41 us / **11.00 us** (RF 35.01 us) | 58.93 us / 25.80 us / **24.01 us** (RF 41.47 us) |
| d==k+1 | 8 | 4.95 ms / 30.08 us / **108.07 us** (RF 548.11 us) | 4.98 ms / 23.53 us / **27.82 us** (RF 521.37 us) | 3.10 ms / 23.46 us / **22.68 us** (RF 461.23 us) | 3.25 ms / 25.29 us / **18.35 us** (RF 2.11 ms) |
| d==k+1 | 32 | 25.18 ms / 37.97 us / **28.91 us** (RF 2.02 ms) | 22.60 ms / 33.82 us / **29.66 us** (RF 1.93 ms) | 14.53 ms / 32.96 us / **27.30 us** (RF 2.76 ms) | 14.68 ms / 36.23 us / **25.16 us** (RF 6.10 ms) |
| d==k+1 | 128 | 79.65 ms / 294.27 us / **160.85 us** (RF 2.59 ms) | 81.15 ms / 232.87 us / **100.09 us** (RF 2.51 ms) | 60.48 ms / 189.32 us / **59.77 us** (RF 3.43 ms) | 59.81 ms / 186.39 us / **52.62 us** (RF 7.67 ms) |
| d>>k | 1 | 31.25 us / 6.98 us / **12.15 us** (RF 8.45 us) | 35.97 us / 11.78 us / **3.32 us** (RF 1.99 us) | 20.00 us / 3.67 us / **3.37 us** (RF 9.48 us) | 36.32 us / 4.22 us / **3.57 us** (RF 5.35 us) |
| d>>k | 8 | 729.86 us / 2.70 us / **9.13 us** (RF 75.21 us) | 670.96 us / 2.49 us / **5.39 us** (RF 28.42 us) | 290.03 us / 8.26 us / **3.96 us** (RF 29.72 us) | 402.18 us / 3.11 us / **2.23 us** (RF 354.78 us) |
| d>>k | 32 | 3.94 ms / 19.68 us / **6.83 us** (RF 465.42 us) | 3.20 ms / 14.69 us / **3.98 us** (RF 370.40 us) | 1.82 ms / 12.84 us / **6.25 us** (RF 632.38 us) | 2.10 ms / 21.50 us / **3.34 us** (RF 2.25 ms) |
| d>>k | 128 | 13.27 ms / 346.65 us / **137.56 us** (RF 556.17 us) | 11.87 ms / 228.24 us / **73.43 us** (RF 523.63 us) | 7.90 ms / 161.31 us / **34.05 us** (RF 788.38 us) | 7.38 ms / 160.05 us / **39.69 us** (RF 2.77 ms) |
| unrelated | 1 | 0.18 us / 0.20 us / **0.13 us** (RF 0.03 us) | 0.07 us / 0.19 us / **0.12 us** (RF 0.03 us) | 0.07 us / 0.18 us / **0.11 us** (RF 0.02 us) | 0.07 us / 0.18 us / **0.11 us** (RF 0.02 us) |
| unrelated | 8 | 1.11 us / 2.75 us / **1.19 us** (RF 0.44 us) | 0.63 us / 2.61 us / **0.73 us** (RF 0.30 us) | 0.37 us / 2.53 us / **0.29 us** (RF 0.21 us) | 0.36 us / 2.52 us / **0.26 us** (RF 0.51 us) |
| unrelated | 32 | 14.73 us / 15.92 us / **10.24 us** (RF 245.07 us) | 8.43 us / 11.96 us / **6.68 us** (RF 236.28 us) | 4.15 us / 9.90 us / **2.29 us** (RF 367.39 us) | 3.80 us / 9.90 us / **2.11 us** (RF 2.01 ms) |
| unrelated | 128 | 539.31 us / 313.45 us / **126.14 us** (RF 267.90 us) | 151.52 us / 361.97 us / **68.27 us** (RF 239.29 us) | 62.42 us / 153.90 us / **28.14 us** (RF 383.05 us) | 58.87 us / 151.00 us / **27.73 us** (RF 1.94 ms) |

### Exact job (matrix run; v3 re-run after the lazy bound)

The v3 column is the re-run in `matrix-v3x-exact.tsv`, taken after the lazy symbol-count bound. The other
columns are from the matrix run. `timeout` means the 60 second limit was hit. Every ok cell has 0 mismatches.

| len | alphabet | regime | difffold v1 | difffold v2 | difffold v3 | RapidFuzz |
|---|---|---|---|---|---|---|
| 1000 | 2 | d=16 | 206.78 us | 4.10 us | **5.14 us** | 77.92 us |
| 1000 | 2 | tiny-prefix-suffix | 3.36 us | 1.20 us | **1.00 us** | 1.58 us |
| 1000 | 2 | unrelated | 571.16 us | 219.62 us | **84.44 us** | 107.20 us |
| 1000 | 256 | d=16 | 94.74 us | 4.29 us | **3.25 us** | 45.80 us |
| 1000 | 256 | tiny-prefix-suffix | 3.62 us | 1.98 us | **1.12 us** | 3.03 us |
| 1000 | 256 | unrelated | 708.39 us | 1.06 ms | **103.06 us** | 55.50 us |
| 1000 | 4 | d=16 | 134.06 us | 4.20 us | **3.58 us** | 46.73 us |
| 1000 | 4 | tiny-prefix-suffix | 6.18 us | 2.04 us | **0.94 us** | 6.76 us |
| 1000 | 4 | unrelated | 380.57 us | 595.05 us | **83.70 us** | 59.49 us |
| 1000 | sparse-u32 | d=16 | 83.14 us | 8.58 us | **2.88 us** | 148.68 us |
| 1000 | sparse-u32 | tiny-prefix-suffix | 3.54 us | 1.96 us | **1.12 us** | 4.14 us |
| 1000 | sparse-u32 | unrelated | 1.81 ms | 2.78 ms | **109.83 us** | 171.84 us |
| 10000 | 2 | d=16 | 1.52 ms | 7.86 us | **4.67 us** | 5.71 ms |
| 10000 | 2 | tiny-prefix-suffix | 43.03 us | 15.30 us | **7.85 us** | 111.96 us |
| 10000 | 2 | unrelated | 29.40 ms | 13.37 ms | **8.41 ms** | 4.78 ms |
| 10000 | 256 | d=16 | 938.38 us | 7.76 us | **3.81 us** | 3.56 ms |
| 10000 | 256 | tiny-prefix-suffix | 32.62 us | 3.47 us | **8.07 us** | 78.24 us |
| 10000 | 256 | unrelated | 29.99 ms | 41.90 ms | **7.16 ms** | 4.08 ms |
| 10000 | 4 | d=16 | 1.40 ms | 8.35 us | **4.23 us** | 2.80 ms |
| 10000 | 4 | tiny-prefix-suffix | 35.61 us | 15.22 us | **8.36 us** | 104.25 us |
| 10000 | 4 | unrelated | 27.33 ms | 21.47 ms | **7.85 ms** | 4.87 ms |
| 10000 | sparse-u32 | d=16 | 802.59 us | 7.15 us | **10.92 us** | 12.55 ms |
| 10000 | sparse-u32 | tiny-prefix-suffix | 29.68 us | 15.61 us | **7.99 us** | 201.24 us |
| 10000 | sparse-u32 | unrelated | 101.57 ms | 172.52 ms | **7.89 ms** | 14.39 ms |
| 100000 | 2 | d=16 | 17.48 ms | 50.98 us | **35.78 us** | 357.99 ms |
| 100000 | 2 | tiny-prefix-suffix | 242.90 us | 38.61 us | **24.08 us** | 3.49 ms |
| 100000 | 2 | unrelated | timeout | 994.23 ms | **799.25 ms** | 462.73 ms |
| 100000 | 256 | d=16 | 9.91 ms | 49.46 us | **38.61 us** | 370.19 ms |
| 100000 | 256 | tiny-prefix-suffix | 202.84 us | 38.12 us | **26.95 us** | 2.07 ms |
| 100000 | 256 | unrelated | 2052.11 ms | timeout | **834.05 ms** | 422.28 ms |
| 100000 | 4 | d=16 | 16.21 ms | 46.53 us | **27.56 us** | 382.60 ms |
| 100000 | 4 | tiny-prefix-suffix | 336.96 us | 39.88 us | **24.80 us** | 6.52 ms |
| 100000 | 4 | unrelated | timeout | 1715.10 ms | **752.11 ms** | 492.49 ms |
| 100000 | sparse-u32 | d=16 | 8.72 ms | 45.63 us | **32.15 us** | 1760.77 ms |
| 100000 | sparse-u32 | tiny-prefix-suffix | 192.73 us | 39.50 us | **26.76 us** | 8.05 ms |
| 100000 | sparse-u32 | unrelated | timeout | timeout | **678.64 ms** | timeout |

Exact summary. v1 and v2 time out on several unrelated pairs at length 100,000. v3 finishes every exact cell in
under 1 s. On unrelated pairs at length 100,000 RapidFuzz takes about 0.4 to 0.5 s and v3 about 0.7 to 0.8 s. On
related pairs (`tiny-prefix-suffix` and `d=16`) v3 is at or below RapidFuzz in nearly all cells.

### Cells where v3 is still worse than v1 or v2 by more than 1.2 times

Procedure. The matrix flagged 33 bounded cells where v3 was more than 1.2 times slower than v1 or v2. Each was
re-run three times with v1, v2 and v3 interleaved, and the median of the three runs per binary was taken
(`repeat-results.tsv`). Nine cells stayed above 1.2 times. Those nine were then checked in the in-process sweep
below, where both kernels run in one process in alternation, so both see the same machine state.

Still above 1.2 times after the interleaved repeats, with the in-process sweep ratio in brackets:

| len | alphabet | regime | k | repeat median v1 / v2 / v3 (us) | sweep v3/v2 (v3/v1) | classification |
|---|---|---|---|---|---|---|
| 1,000 | 2 | d==k | 1 | 0.45 / 0.22 / 0.84 | 1.02 (0.45) | noise: sweep equal to v2 |
| 1,000 | sparse | unrelated | 128 | 38.8 / 48.7 / 48.7 | 0.97 (1.19) | real, borderline: about 1.2 times v1 |
| 10,000 | 2 | d==k+1 | 8 | 538 / 2.44 / 4.10 | 0.58 | environment: v3 faster in the sweep |
| 10,000 | 256 | d<k | 8 | 296 / 1.89 / 7.59 | 0.95 | environment: bimodal between processes |
| 10,000 | 4 | d==k | 8 | 480 / 2.46 / 7.26 | 0.89 | environment: bimodal between processes |
| 100,000 | 256 | unrelated | 1 | 0.065 / 0.179 / 0.108 | 0.56 (1.37) | real, small: about 35 ns over v1 |
| 100,000 | 4 | d>>k | 8 | 669 / 2.53 / 5.34 | 0.53 | environment: sweep v3 6.6 us, v2 12.4 us |
| 100,000 | 4 | unrelated | 1 | 0.073 / 0.179 / 0.109 | 0.60 (0.60) | environment: the v1 ratio exists only in the matrix |
| 100,000 | sparse | unrelated | 1 | 0.066 / 0.178 / 0.108 | 0.62 (1.54) | real, small: about 40 ns over v1 |

The k=8 related cells at length 10,000 and above (the rows with bimodal or environment labels) moved between about
2 us and about 8 us from one process run to the next, for v2 as well as v3. Two runs of the same v2 binary on the
same cell gave 1.9 us and 8.4 us. A heap-buffer build of v3 showed the same two modes. Callgrind instruction
counts for the whole process were equal (7.79 M for v2 against 7.78 M for v3). These cells are classified as
machine-state noise, not as a kernel regression. The in-process sweep shows v3 at 0.53 to 0.95 times v2 on them.

Real remaining losses, meaning v3 slower than v1 or v2 by more than 1.2 times in the sweep as well as the matrix:

- Unrelated pairs at `k = 1` at length 100,000: about 35 to 40 ns over v1 (1.4 to 1.5 times), and 0.6 times v2.
  These are sub-0.2 us cells, so the absolute difference is at timer scale.
- Sparse unrelated pairs at length 1,000 with `k = 128`: about 1.2 times v1, and equal to v2.

### In-process kernel sweep (interleaved, one process)

`wfcmp sweep` (scratchpad, not committed) times the three `levenshtein_within_u32` functions in one process,
alternating between them, with seven repetitions and the median reported. The pairs come from
`strbench::make_pair`. Each kernel's answer is checked against RapidFuzz before timing. Both kernels see the same
machine state here, so this is the cleanest kernel-level comparison in this session.

| len | cells | geomean v3/v2 | geomean v3/v1 | cells more than 1.2x slower than v2 | cells more than 1.2x slower than v1 |
|---|---|---|---|---|---|
| 1,000 | 80 | 0.61 | 0.13 | 0 | 0 |
| 10,000 | 80 | 0.47 | 0.04 | 0 | 0 |
| 100,000 | 80 | 0.42 | 0.02 | 0 | 4 (all `k = 1` unrelated, 1.35 to 1.54 times) |

Per bound, the geometric mean of v3/v2 is 0.86 at k=1, 0.49 at k=8, 0.32 at k=32 and 0.44 at k=128.

### Limits

- One machine, shared with another benchmark. Timing modes flip by 2 to 4 times between processes, so the
  decisions above use the interleaved repeats and the in-process sweep. Ratios under 1.3 are treated as ties.
- Edlib and WFA2-lib are not in this comparison.
- The exact path still trails RapidFuzz on unrelated pairs (about 1.7 to 1.9 times). The full pass is not
  tuned further.
- Nothing here is PROVED. The correctness claims rest on the tests, the random differential check and the
  mutation checks recorded in `LEVENSHTEIN.md`.
