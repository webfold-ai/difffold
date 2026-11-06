# Ideas for difffold from the sister repositories

Part 2 of the accuracy and ideas study. Part 1 is `ACCURACY-MECHANICS.md`; the measured facts it
establishes decide the ranking here.

Labels used throughout:

- **MEASURED**: run in this study, numbers and method in `ACCURACY-MECHANICS.md`.
- **FOUND-IN-REPO**: read in a sister repository (path given, no commit hashes).
- **INFERRED**: my reasoning about how a found idea would apply. Not run. Treat as a hypothesis.
- **EXTERNAL**: general literature or practice that is not in any repo here. Not verified in this study.

## What was read

The task asked for the repositories to be read through the GitHub tools. I used the GitHub file
tools for the repository root listings, the READMEs of `ptyktos/research` and `ptyktos/sangdb`, the
`src` listings of `ptyktos/sangdb`, `ptyktos/modelfold` and `ptyktos/memoryfold`, `ptyktos/research/difffold/README.md`
and `ptyktos/memoryfold/src/tree_optimize.rs`. The rest of the reading (keyword searches, file heads) was done in the
read-only local clones of the same remotes that already exist on this machine, because the GitHub tools
have no code search. Nothing was cloned, fetched or modified in those repositories.

| repo | size | verdict for difffold |
|---|---|---|
| `ptyktos/research` | 1,680 files | Relevant. Holds the design notes of the OmniDiff-class differ (`drafts/omnidiff-apeiron/`), a FastLanes layout study, and a mirror of difffold itself (`difffold/`). |
| `ptyktos/sangdb` (and `sangdb-core`) | 129 and 37 files | Partly relevant: partition pruning, SimHash index, content-addressed chunk sync. `sangdb-server` and `sangdb-bench` are a server and competitor benchmarks, nothing for diffing. |
| `ptyktos/memoryfold` | 202 files | Marginal. One relevant technique (closed-form fit of a ranking from supervision, `src/spanscore.rs`). `doctree.rs`, `tree_optimize.rs`, `landscape_tree.rs` are document and retrieval trees, not edit distance. |
| `ptyktos/modelfold` | 509 files | Marginal. Count-table statistics (`src/countlm.rs`) and a DP on the hash table (`src/audio/music/dtw.rs`). No tree or sequence diff. |
| `ptyktos/seed-format`, `ptyktos/tokenizer` | 16 and 7 files | Nothing relevant. A checkpoint file format and an n-gram counter tokenizer. |
| `ptyktos/ptyktos-experiments` | 621 files | Nothing relevant. Language-model experiments. |
| `webfold-ai/apeiron` | 1,395 files | The substrate difffold already uses (`map::table`, `freq`). Other parts (GPU, quantisation) are not relevant. |
| `webfold-ai/webfold` | 1,195 files | A consumer: `src/diff.rs` diffs page snapshots with the `similar` crate. No tree diff. |

**Existing difffold-adjacent implementations.** There is no independent TED or diff implementation in
any of these repositories. `ptyktos/research/difffold/` is a mirror of an earlier difffold snapshot
(its `gitcompat/src/myers.rs`, `src/ted.rs` and notes are the same lineage), so it is not a second
opinion. `webfold/src/diff.rs` uses `similar`, which Lane 1 of `notes/lanes/RESULTS.md` already
compares against. OmniDiff itself (outside the list, but the reference implementation) is described in Part 1.

## Ranked ideas

Ranking is by expected benefit to difffold's stated weak point (accuracy against the hand-authored
ground truth) first, then speed and memory, discounted by risk. Part 1 shows that about 12 of the
13.6 points between difffold and OmniDiff on the engine subset are available from tie-breaking alone,
so the top ideas are about choosing among equal-cost mappings.

### 1. A secondary, context-aware cost to break ties, with weights fitted from the ground truth

- **Source.** FOUND-IN-REPO: `memoryfold/src/spanscore.rs` fits ranking weights from sentence-level
  supervision in one closed-form ridge solve over a fixed small feature lift, and reports held-out
  results separately. `modelfold/src/countlm.rs` and `tokenizer/src/lib.rs` keep count-table statistics whose merge is exact and order-free
  (hashtrinity `Table`). `research/drafts/omnidiff-apeiron/FROM-SCRATCH.md` proposes window-local DP
  costs from a class-pair table indexed by the pair itself.
- **What it is.** Keep the exact primary cost (so the distance is unchanged) and add a low-order secondary cost per pair
  from features of its context: root path, parent and grandparent kind, sibling position, subtree identity of the
  neighbouring siblings, depth difference, subtree size difference. Fit the feature weights offline.
- **How it applies.** `ted.rs::relabel_cost` is the single point where a pair cost enters; the secondary term can be packed into
  the low bits (`cost * K + secondary`) or kept as a second table. The traceback already has a tie policy
  (`prefer_match`); this replaces it with a cost.
- **Effect (MEASURED).** On the 586 fixtures of at most 2,500 nodes, plain optimal mapping is 70.5% perfect;
  one hand-written feature (root-path mismatch) gives 73.2% (68.9% against 66.2% on the 951 fixtures up to 20,000 nodes), depth difference 73.0%; a perceptron-fitted
  weighted sum of 11 features gives 76.3% (447 of 586) in two-fold cross-validation, 76.6% with move recovery. The ceiling for any tie-break is 83.6% (the share of fixtures whose
  ground truth is itself a minimum-cost mapping). Speed: a secondary cost does not change the pruning argument
  (every unmapped node still costs at least one primary unit); expect a small constant factor from the wider cell type.
- **Risk.** Overfitting: the ground truth is OmniDiff's authors' own and OmniDiff was tuned on it, so any fitted tie-break must be
  reported with cross-validation, and a held-out set that is not this corpus would be better. Wider cell values (u64, or u32
  with a smaller scale) cost memory in the banded tables. Weights are language-dependent in principle.
- **Test.** Two-fold cross-validation by fixture (done in the harness, `research/mechanics`, command `learn`); then
  leave-one-language-out; then a fresh sample of real commits scored with OmniDiff's mapping as a weak reference.
  Gate: distance identical to the unweighted run on all 237 real-AST pairs and the 4,000 random pairs.

### 2. Family-aware relabel costs (from the reference differ, not a sister repo)

Listed here because it is the cheapest accuracy change I found and it belongs next to idea 1.
FOUND-IN-REPO (the OmniDiff checkout, `src/diff/nodes.rs`, `kinds_update_allowed`): a cost-1 update is allowed between any two
identifier-like kinds and within operator families (comparison, arithmetic, bitwise, logical, assignment, increment).
difffold prices every cross-kind relabel at 2, the same as delete plus insert, so the traceback never emits one. MEASURED
in Part 1: a tie-break oracle restricted to pairs difffold can emit reaches 79.2%, one that may also use cross-kind
relabels reaches 82.6%. The family rule itself is worth less than that gap: MEASURED 413 to 417 perfect (+0.7 points) with the default tie policy, and +0.7 again on top of the root-path tie-break (429 to 433).

### 3. Hash-consed subtree identity as a certified shortcut inside the tree edit DP

- **Source.** FOUND-IN-REPO: `src/intern.rs` (invariant I1: id equality is deep structural equality) and `SPEC.md`
  (the test `identical_first_anchoring_would_be_wrong_here` shows that matching identical children first is not
  optimal for the top-down objective). `research/drafts/omnidiff-apeiron/FROM-SCRATCH.md` section 2 cites Merkle-style subtree
  addresses as licensed by the proofs of the apeiron corpus (the theorems it names are in a private corpus and are
  not independently checked).
- **What it is.** Use id equality only where it is provably safe: a pair of keyroots with equal ids has distance 0, so the window
  for that pair need not be filled, provided no enclosing window reads the skipped inner entries. Needs a proof
  or a restriction (for example only skip when both subtrees are leaves of the keyroot chain).
- **Effect (INFERRED).** Speed on low-distance pairs, where the shared-subtree fraction is 0.88 to 0.99 (`notes/lanes/TED-THEORY.md`),
  but those pairs are already 16.7x faster than APTED at the median, so the headroom is the 11 slow high-distance pairs, where the shared fraction is lowest.
  Expect little there. Memory: none.
- **Risk.** A wrong skip silently changes the distance. The top-down note above is a warning that identity shortcuts are not
  optimality-preserving by default.
- **Test.** Compare `ted` with and without the shortcut on 100,000 random tree pairs with planted repeats and on the 237 real pairs; assert equal distance and
  equal mapping validity; count cells.

### 4. A certified upper bound from unique-leaf anchors to start the threshold search

- **Source.** FOUND-IN-REPO: `research/drafts/omnidiff-apeiron/FROM-SCRATCH.md` section 1. On OmniDiff's 30 slowest fixtures, anchoring on leaves
  that occur exactly once on each side and solving only between anchors cut the DP from 9.62 M to 0.76 M cells (12.6x).
  The note itself says anchors are not optimality-preserving.
- **What it is.** Do not constrain the DP with the anchors. Solve the anchored problem first, take its cost as an upper
  bound `U`, and run the exact banded DP with `tau = U`. The result stays exact and the number of doubling attempts goes to one.
- **Effect (INFERRED).** `TED-THEORY.md` found that the slow cases lose on cell count, not on retries (median attempts 2 against 1),
  so a tighter `tau` helps only if `U` is close to the optimum, which anchoring makes plausible on the
  high-distance pairs. Probably modest.
- **Risk.** Low: exactness is not at risk, only the benefit.
- **Test.** On the 237 instrumented pairs record `U / optimum` and the cells at `tau = U` against the current cells.

### 5. Window pruning with cheap per-subtree summaries (zone-map style)

- **Source.** FOUND-IN-REPO: `sangdb/src/partition.rs` stores min and max per partition at write time and skips whole
  partitions whose statistics prove a predicate cannot match (`PartitionStats::can_match`). `apeiron/src/engine/kern/bitplane.rs` has the same
  two-stage "coarse bound first, exact only if the bound cannot rule it out" shape with a proved soundness lemma.
- **What it is.** Store, per subtree, its size and a small label histogram. Before filling a keyroot window, compute a lower bound on the tree distance
  of the pair (size difference, histogram L1 distance divided by two) and skip the window if it exceeds `tau`. `ted.rs` already skips
  windows by `|lml difference| > 2 tau` and has a global `label_lower_bound`; this is the per-window version.
- **Effect (INFERRED).** Fewer filled windows on high-distance pairs. Exact. Memory: one small histogram per node unless histograms are
  hashed into a few buckets.
- **Risk.** Low for exactness; the bound must be a true lower bound under the kind-aware costs (relabel 2 across kinds).
- **Test.** Count skipped windows on the 237 pairs; assert distance unchanged on random pairs.

### 6. SimHash candidates for moved or renamed subtrees

- **Source.** FOUND-IN-REPO: `sangdb/src/lsh.rs` (multi-table SimHash `band_code`, insert is a hash into buckets, no rebuild).
- **What it is.** After the exact mapping, hash each unmatched subtree by its label multiset and look up near-duplicates on the other
  side in O(n) instead of comparing all pairs. This is the candidate stage a GumTree-style move recovery needs.
- **Effect.** Accuracy is bounded by what moves are worth. MEASURED: the existing identical-subtree move recovery adds 0.3 to 0.5 points
  on the subset; 8.9% of the fixtures on the engine subset (12.0% of the 951 up to 20,000 nodes) have ground truth that is not a tree edit mapping at all (moves, reorders, N:M groups), and OmniDiff is perfect on only 42 of the 114 in the larger set. So the ceiling for a perfect move operator is real (up to 8.9 points) but the achievable part is small. Speed: neutral.
- **Risk.** False candidates; every accepted move needs a verification pass (same discipline as the longest-common-extension check in the notes).
- **Test.** Replay the move-bearing fixtures (`n_move > 0`, `n_reorder > 0` in the harness CSV) and report fixtures flipped to perfect.

### 7. Memory: flat child arrays and narrower band cells

- **Source.** FOUND-IN-REPO: `research/drafts/fastlanes-vs-simd-intrinsics/NOTES.md` (lane-interleaved integer layout, 2.2x from instruction-level parallelism alone, no vector registers).
  INFERRED application.
- **What it is.** `PostTree` keeps `kids: Vec<Vec<u32>>`; a CSR layout (one offsets array, one flat array) removes a heap allocation per node.
  The two banded tables are `u32` of size `(n+1) * (2 tau + 1)`; when `tau + 1 < 65536` a `u16` table halves them, and
  `tau < 255` allows `u8`. A 20,000-node pair with `tau = 500` is about 80 MB per table today.
- **Effect (INFERRED).** Roughly 2x on the tables for common `tau`, about the size of the child lists for the CSR change. A
  secondary tie-break cost (idea 1) pushes the other way, so decide the cell width after idea 1.
- **Test.** Peak RSS on the large cohort (median 3,061 nodes) before and after; distance identical.

### 8. Content-defined segmentation for very large line diffs

- **Source.** FOUND-IN-REPO: `sangdb/src/partition.rs` and `sangdb/src/raw_sync.rs` (gear-hash content-defined boundaries, content-addressed chunks).
  `notes/systems/rsync.md` and `mononoke-bonsai.md` in difffold already study the same family.
- **What it is.** Split both line sequences at content-defined boundaries and diff chunk by chunk so an insertion does not shift every boundary.
- **Effect.** Not optimality-preserving: a minimal script can cross a boundary. It would be an opt-in fast mode, not the exact engine.
  Lane 1 shows difffold is already faster than xdiff and `similar` on 2,302 real pairs, so this only matters for the adversarial
  large-distance case.
- **Test.** Edit-cost excess against the exact engine on the 2,302 pairs and on synthetic 10 MB files.

### 9. Bit-parallel LCS for the line differ's worst case

- **Source.** EXTERNAL (not in any sister repo). `notes/seq/myers99.md` explains why Myers 1999 does not transfer to the tree aligner; it does
  not discuss the line differ, where, after interning, the objective is a plain longest common subsequence over dense ids.
- **What it is.** For inputs where the edit distance D is close to N, replace the O(N D) middle-snake search with a bit-parallel LCS
  over blocks of 64 positions, O(N M / 64).
- **Effect (INFERRED).** Lane 1 reports the worst case (random high-distance files) at 3.1 s, 3.7 s and 32 s against git `--minimal` at 0.73 s, 1.39 s and 9.2 s.
  Bit-parallel LCS on 20,000 by 20,000 is about 6 M word operations, so tens of milliseconds, if the traceback is done in linear space.
  This closes the one lane where difffold loses.
- **Risk.** A second code path to prove. The Lean extraction work (`proof/`) covers the current Myers code only.
- **Test.** Differential test against the existing minimal differ on random inputs; benchmark on the Lane 1 high-distance set.

## Considered and not recommended

- **DP cells in a hash table (`modelfold/src/audio/music/dtw.rs`).** It keys DTW cells by packed coordinates in a `hashtrinity::CoordMap`. `ted.rs` uses dense banded arrays and
  `TED-THEORY.md` shows the cost is the number of cells, not the cost of a cell, so a hash lookup per cell is a loss.
- **Wavefront alignment (`notes/seq/wfa.md`, `biwfa.md`).** The notes already conclude that unit-step wavefronts do not transfer to subtree-size weights.
- **Retrieval trees (`memoryfold/src/tree_optimize.rs`, `doctree.rs`).** Expand and merge laws for page-index trees; unrelated to edit distance.
- **Matryoshka prefixes (`sangdb/src/mrl.rs`).** Coarse-to-fine re-ranking of embeddings; the analogue (coarse histogram bound, then exact) is already idea 5.

## What I could not establish

- Whether the theorems cited in `FROM-SCRATCH.md` (`SharedFold.prefix_fold_memo` and others) hold: they are in a private corpus that is not in any repository I could read.
- Any wall-clock effect of ideas 3 to 9. None was run; only the accuracy ideas (1 and 2) have measurements.
- Whether `webfold` would benefit from difffold's line differ in place of `similar`; its snapshots are small and the study of that (notes/webfold/INTEGRATION.md) is outside this task.
