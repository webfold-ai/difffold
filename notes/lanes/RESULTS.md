# Comparison lanes: measured results and what could not be run

Machine: shared cloud VM, single run unless stated. Corpus: OmniDiff's `src/test/data/diffs` (2,302
before/after pairs; Java, Go, C, Rust, Python, JS/TS, JSON, XML and others). Tags follow
`drafts/PAPER_STYLE.md`: measured, implemented, not run.

Unit-cost Levenshtein against Edlib, RapidFuzz, WFA2-lib and the difffold kernel, on integer token
sequences: [string baselines](STRING-BASELINES.md) (measured).

## Lane 1: lossless line text (exact objective)  [measured]
In-process, raw bytes to edit script, median of 15 repetitions, 2,302 pairs.

| tool | total ms | median us | p99 us |
|---|---|---|---|
| difffold-lines (recursion only, minimal) | 119 | 14.0 | 527 |
| similar 2.7.0 (no deadline, exact) | 140 | 14.1 | 754 |
| imara-diff 0.1.8 MyersMinimal | 164 | 22.2 | 734 |
| libgit2 xdiff, in process (git2 0.20, minimal) | 659 | 93.5 | 2855 |

Cost equals `similar` on all 2,302 pairs and `rapidfuzz` Indel on all 2,300 checkable pairs.
`imara-diff` differs from the exact byte-line cost on 44 pairs (28 lower, 16 higher) with both of its
Myers variants, so the cause is its tokenisation, not its solver cutoff. Not resolved for the 16
higher cases.
Worst case, random high-distance files (D about N): difffold 3.1 s, 3.7 s, 32 s against git
`--minimal` 0.73 s, 1.39 s, 9.2 s. Recursion-only code is 2.7 to 4 times slower there.

## Lane 1b: patch output  [measured]
`git apply` forward and reverse round trips: 4,602 of 4,602 succeed (minimal and histogram).
Patch-stage time (raw bytes to serialized unified diff): difffold 335 ms, similar 466 ms,
imara-diff 174 ms total. imara is faster at this stage. Not a win.

## Lane 2: structural (tree) correspondence
- difftastic 0.72.0 on 80 Java fixtures: difffold 3.8x faster at the median, 6.5x in total  [measured]
- accuracy of difffold against hand-authored ground truth, 1,001 fixtures: pair F1 0.998, 56.8% of
  fixtures perfect  [measured]. OmniDiff's own accuracy: not rerun (build deleted).
- GumTree 4.0.0-beta4: 80 fixtures timing only  [measured]; accuracy not scored.
- RTED/APTED/Zhang-Shasha: different objective, timing only where run; see lane results below.

### Git's xdiff, direct (no libgit2 patch objects)  [measured]
`libgit2/xdiff`, an unreleased snapshot after git 2.48.1, compiled with `gcc -O2` and called from a C harness (`xdl_diff`, context 0,
counting +/- lines in the emit callback), median of 15, same 2,302 pairs, bytes in memory:

| tool | total ms | median us | p99 us |
|---|---|---|---|
| difffold-lines (exact) | 119 | 14.0 | 527 |
| xdiff default | 270 | 36.4 | 1,255 |
| xdiff `XDF_NEED_MINIMAL` | 265 | 35.0 | 1,238 |

difffold is 2.2x faster in total and 2.5x at the median. The xdiff figure includes its callback
emission, which difffold's script construction does not do in the same form, so the ratio is an upper
bound on the algorithmic gap. (The earlier libgit2 `Patch::from_buffers` row, 659 ms, included
patch-object construction and is superseded by this one.)

**xdiff's "minimal" mode is not minimal.** On 9 of 2,302 real pairs, `XDF_NEED_MINIMAL` and
`git diff --minimal` report a larger edit cost than difffold (by 2 to 34 lines; 301 against 267 on the
largest), and `rapidfuzz` Indel independently confirms difffold's cost on all 9. Default and minimal modes
return identical costs on every pair. Source check: `xdl_cleanup_records` (`xprepare.c` lines 367-390)
discards lines that occur at least `min(sqrt(nrec), 1024)` times in the other file, and never reads the
minimal flag, which only enters the split heuristic in `xdiffi.c`. Causal test: the patch `notes/lanes/xdiff-no-discard.patch` changes only `(nm >= mlim) ? 2: 1` to `1` (never
discard). With that single change, xdiff returns the exact minimum on all 2,302 pairs in both modes
(0 differences from difffold and `rapidfuzz`). So the multimatch discard is the cause of the 9
non-minimal results. Whether the smaller scripts also give more useful hunks is not assessed.

## Lane 2b: general ordered tree edit distance (Zhang-Shasha objective)  [measured]
Unit insert, delete and relabel costs, deletion promotes children. Baselines: the Rust port `apted`
0.1.1 and the authors' Java APTED (unreleased snapshot after its 0.1.1 tag, JVM, 5 reps after warm-up, so small-tree Java
numbers include JIT warm-up). Real tree-sitter ASTs; every distance is asserted equal.

| cohort | pairs | vs Rust APTED port (total / median) | vs Java APTED (total / median) |
|---|---|---|---|
| median 143 nodes | 97 | 2.1x / 5.5x | 23.2x / 27.4x (JIT inflated) |
| up to 1,489 nodes | 150 (100 in the Java run) | 5.9x / 11.6x | 9.7x / 20.9x |
| median 3,061, max 5,958 nodes | 40 | 15.6x / 25.9x, never slower | 27.6x / 40.6x, never slower (min 2.3x) |

Where the speedup comes from (237 instrumented pairs): it tracks normalised distance
(correlation of log speedup is -0.68), not size (+0.40). Pairs below 5% normalised distance have a
median 16.7x speedup; at 30% or more it is 1.0x. All 11 pairs where difffold is slower have a
normalised distance of 0.11 or more. Larger pairs in this corpus have lower normalised distance, so
"speedup grows with size" is confounded. Plain Zhang-Shasha (the unpruned baseline in `ted.rs`) is
about 2x slower than APTED; the banding and early exit make it 18.6x faster than plain.
Exactness: a brute-force forest recursion agrees on 6,000 random small tree pairs.
Mapping, validation and executable replay (`ted_mapping`, `check_mapping`, `replay_script`): the optimal mapping is recovered by tracing back
through the forest tables. An independent validator checks one-to-one, ancestor preservation in both
directions and sibling order, and recomputes the script cost from the mapping alone. Validated on 4,000
random small pairs against the forest-recursion oracle and on all 237 real-AST pairs (every mapping
legal, script cost equal to the distance equal to APTED's). `replay_script` then executes the script (relabel,
delete with child promotion, insert deepest first) on a mutable copy of tree A and requires the result to
equal tree B exactly (labels, shape, sibling order) with an operation count equal to the distance; it passes
on the same 4,000 random pairs and all 237 real-AST pairs. Insert placement consults the structure of B, so
replay shows the mapping is executable and the operations compose to B, not that the script was derived
independently of B. Timing, large cohort, distance plus mapping recovery 13.5 s (difffold) against distance
only 109 s (APTED port): about 8.1x for those two measured paths; mapping recovery costs about 2x
difffold's own distance-only time (7.6 s).
Not established: asymptotic complexity, peak memory, recursion-only form.

## Lane 2c: correspondence accuracy against OmniDiff's hand-authored ground truth  [measured]
1,001 scorable fixtures (8 languages, Java is 515), micro-averaged. 748 other fixtures are unscorable
because difffold has no parser for their language, or the ground truth has no pairs. Ground truth is
the mapping OmniDiff's own authors wrote, and OmniDiff was tuned on this corpus, so its numbers are an
in-sample upper end.

| metric | difffold top-down (Selkow) | difffold general TED | OmniDiff |
|---|---|---|---|
| node-correspondence accuracy | 0.996 | 0.998 | 0.999 |
| pair F1 | 0.998 | 0.999 | 1.000 |
| changed-span F1 | 0.843 | 0.936 | 0.971 |
| perfect fixtures | 56.8% | 65.7% | 81.2% |
| near-perfect fixtures | 85.4% | 90.7% | 96.1% |

Against the top-down mapping, 75% of the failed decisions were wrap/unwrap changes, which the top-down
objective cannot express. The general objective (deleting a node promotes its children) recovers part
of that. It does not reach OmniDiff: classical TED has no move operation, and the ground truth contains
reorders and cross-parent moves where OmniDiff scores far higher. The general-TED run falls back to the
top-down mapping for trees over 20,000 nodes (fallback count not recorded). Files: `results/accuracy/`.

## Lane 2d: GumTree and RefactoringMiner accuracy  [measured, indicative]
See `notes/lanes/GUMTREE-RM.md`. On 200 small Java fixtures (scoped scoring, lenient to JDT-based tools):
OmniDiff 83.0% perfect, RefactoringMiner 80.5%, best GumTree matcher 73.5%, default GumTree 70.5%,
difffold general TED 59.0%, difffold top-down 48.0%. DiffBenchmark was built but not run.

## Lane 3: concurrent reconciliation (three-way merge)  [measured]
400 real scenarios per kind from the corpus. `disjoint` = left and right apply disjoint halves of a
real change, the correct merge is the after file byte for byte. `conflict` = both rewrite one hunk.

| tool | disjoint correct | false conflict | silently wrong | conflict flagged |
|---|---|---|---|---|
| difffold merge3 (diff3 on exact lines) | 392 | 7 | 1 | 400/400 |
| git merge-file | 392 | 6 | 2 | 400/400 |
| Mergiraf 0.20.0 | 379 | 4 | 17 | 400/400 |

Caveat: "silently wrong" means not byte-equal to the after file. Mergiraf is syntax-aware and may
reformat or place equivalent code differently, so its 17 are not shown to be semantically wrong.
Timing is not comparable (in-process library against separate processes).

## Lane 4: transfer deltas (sync)  [measured]
800 pairs, every delta applied and verified.

| tool | delta bytes | deflated | side channel | total ms |
|---|---|---|---|---|
| difffold line copy/insert delta | 402,438 | 159,493 | 0 | 144 |
| rsync algorithm (fast_rsync, 512 B blocks) | 1,323,142 | 478,621 | 537,120 signature | 55 |
| bsdiff (qbsdiff, bzip2 inside) | 229,198 | n/a | 0 | 1,831 |

bsdiff's patch is already compressed, so compare it with our deflated size (159 KB), not our raw
size. Ours is text-only and line-granular; rsync and bsdiff handle arbitrary binary.

## Lane 5: build impact  [proxy measured; Bazel tools not run]
`bazel-diff` and `target-determinator` need Bazel and a Bazel workspace, which this sandbox does not
have. Proxy: of 1,067 changed Java files, the exported interface (class headers, non-private
signatures and fields, imports) is unchanged in 835 (78.3%), so early cutoff would skip dependent
rebuilds where content-hash invalidation rebuilds every dependent. Interface extraction is
tree-sitter based and approximate; the corpus is hand-picked diffs, not a random sample of commits.

## Lane 5b: presentation (delta 0.20.1)  [measured]
400 real `git diff` patches (543 KB total), one process per patch, output discarded: `cat` baseline
713 ms, delta default 6,135 ms, delta without syntax theme 5,438 ms. That is about 13.6 ms of rendering
per patch beyond process start, far above the diff computation times in lanes 1 and 2. In this measured
short-lived pager pipeline delta dominated. The subtraction does not separate syntax highlighting, within-line
inference, formatting and I/O, so it is an end-to-end lane and not a universal rendering constant.

## Lane 6: web change products  [not run]
Firecrawl and Exa are paid external services that need API keys and send content off the machine.
Not run. The primitive they rely on, content-hash gate plus diff, is covered by lanes 1 and 1b.

## Not run for other reasons
- Beyond Compare: proprietary GUI.
- OmniDiff accuracy head to head: needs a rebuild of its binary (disk was freed by deleting it).

## Accuracy variant E (orphan-update hygiene on top of TED+kinds+moves)
Measured on 1001 pairs: perfect 66.7% (D: 66.2%), 91.9% (D: 91.7%), F 0.947 (unchanged). A small gain; OmniDiff remains at 81.2% perfect, so the gap (about 14.5 points) is still open.
