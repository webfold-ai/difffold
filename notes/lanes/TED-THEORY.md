# What the two recent TED papers say, and what the difffold data says

Sources read in full text (PDF extracted with pdftotext), not only abstracts.

## Nogler, Polak, Saha, Vassilevska Williams, Xu, Ye: arXiv 2411.06502 (v3, Mar 2025)  [read]
- Weighted TED is fine-grained equivalent to APSP; with Williams 2018 APSP this gives
  n^3 / 2^{Omega(sqrt(log n))}, the first truly subcubic TED algorithm.
- Unweighted TED: O~(n^{(3+omega)/2}), at most O(n^2.6857) with the best known omega; prior best
  O(n^2.9148) (Duerr 2023).
- Structure (Section 2.3): Spine Edit Distance (SED) from [BGHS19]. Input: two forests, one
  root-to-leaf spine each, and the similarity of every subtree pair except spine x spine. Output: the
  missing spine x spine similarities. Lemma 2.1: an SED algorithm in O(f(m) g(m')) gives TED in
  O(f(n) g(n') log^2 max(n, n')). SED is then reduced to APSP (Section 5). Min-plus product is the
  crucial subroutine of the earlier unweighted algorithms.
- The exact "T_MUL(n) + n^{2+o(1)}" expression quoted in a pasted analysis was NOT checked here; only
  the statements above were read.
- These are theoretical algorithms. At the n of real ASTs (up to about 6,000 nodes) the fast
  matrix multiplication constants would dominate; no practical implementation is claimed.

## Kociumaka, Shahali: arXiv 2507.02701 (ESA 2025)  [read]
- Bounded TED in O(n + k^6 log k), weighted and unweighted; prior unweighted O(n k^2 log n) and
  O(n + k^7 log k); prior weighted O(n + k^15).
- Uses periodic blocks and a modified universal kernel. Section 4: for a balanced string R the matrix
  M_R is built in O(|R|^3 log |R|) (Klein's algorithm) and the e-th power under the min-plus product
  gives the cost of aligning R^e, using fast exponentiation, O(log e) min-plus products.
- Equal-looking repeated blocks are valid operators only under the paper's conditions (balanced
  strings, free blocks); equal canonical subtree ids alone are not shown to be enough.

## What the difffold counters say (237 instrumented pairs, Experiment A)
The 11 pairs where difffold is slower than the APTED port, against the other 226:
- DP cells per (n+m)^2: 7.3 (slow) against 0.35 (fast). Median cells 1.06M against 0.36M.
- Time per DP cell: 9.0 ns against 11.9 ns, so the cost is the number of cells, not the cost of a cell.
- Median threshold attempts: 2 against 1, so threshold retries are not the cause.
- Shared-subtree fraction 0.88 against 0.99; normalised distance 0.15 against 0.014.
- `ted.rs` uses dense banded arrays and no hash table, so apeiron's table does not enter this cost.
Conclusion supported by the data: in the regime where difffold loses, the bottleneck is dense transition
work (cell count), not state access or retries. Not established: that a min-plus or SED-style batched
solver would beat a better decomposition strategy (APTED-style path choice) at these sizes.

## Honest gap to the theory
The bounded-TED bound is near-linear in n for fixed k. difffold's cell count on low-distance pairs is
about 0.35 (n+m)^2, which is far from near-linear, so the measured speedups come from a banded
quadratic-style algorithm, not from that theory. No complexity bound is claimed for `ted.rs`.
