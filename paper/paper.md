# Repairing a Top-Down Tree Matcher: Exact Identity, a Certified Core and a Cross-Level Pass

Draft 1.0, workshop-paper length. Every number in a table is taken from a file named in the table's
caption; every file is in this repository. Section 7 lists what was not run.

## Abstract

Structural diff tools that report *what moved* need a node correspondence between two parse trees,
not just an edit distance. The cheapest exact family of algorithms, ordered *top-down* tree
matching, pairs a node only if its parent is paired, so it cannot express a moved subtree, a
reordered child or a node wrapped in (or unwrapped from) a new parent. We start from a top-down
matcher that is exact by construction (hash-consed nodes, a threshold dynamic program whose result
is accepted only when an admissible bound certifies it, and replay of every edit script) and add a
bounded cross-level refinement: pair identical unmapped subtrees wherever they sit, drop
implausible tentative pairs, pair containers by shared mapped descendants, align inside the new
container pairs, and pair remaining equal leaves inside mapped ancestors. On the 998 scorable
fixtures of the public OmniDiff corpus (eight tree-sitter languages) the refinement raises
changed-span F1 from 0.844 to 0.965 and the fraction of fixtures with no visible mismatch from
56.8% to 75.3%. OmniDiff scores 0.973 and 82.1% on the same scorer; the paired bootstrap interval
of the changed-span difference includes zero, the perfect-fixture difference does not. Two phases and two
of the five thresholds were chosen on one half of the fixtures, the rest being inherited; the other half
gives 0.964. In paired timing on 120 fixtures
(Section 6.4), difffold's matching and refinement take 1/146 of OmniDiff's diff time, but the tree-sitter parse is
98% of difffold's end-to-end time, so with each tool's own preparation counted the total is 5.4 times lower
(not an order of magnitude; measured on a heavily loaded machine). The refined mapping is a heuristic repair, not an optimum of any objective;
the certified part is only the top-down core.

## 1 Introduction

A diff consumer such as a reviewer, a selective-testing tool or an agent that watches a document
needs to know which old node *is* which new node. Edit-distance algorithms answer a different
question: they return a cheapest script under an operation set. For ordered trees the choice of
operation set fixes what a correspondence can say. General tree edit distance (Zhang and Shasha)
lets a deleted node promote its children and has cubic-time algorithms that are optimal in the worst
case unless a standard conjecture fails; the *top-down* variant (Selkow) deletes whole subtrees and requires
matched parents, which makes it quadratic and amenable to pruning, but it reports a moved function
as one deletion plus one insertion.

This paper asks a narrow engineering question: **how much of the accuracy gap between an exact
top-down matcher and a tuned heuristic matcher can a small, bounded, cross-level repair pass
close, and at what cost in time?** Our answer, on one public corpus, is: most of it in changed-span
F1, less of it in per-fixture perfection, at a cost of about 2% of end-to-end time, because the
certified top-down core is cheap and the tree-sitter parse dominates (Section 6.4).

**Contributions.**

1. A precise statement of the matching problem and of what the top-down objective cannot express
   (Section 2).
2. `difffold`: an exact-identity, certified top-down core (Section 3.1, 3.2) and a six-phase
   cross-level refinement with a complexity argument and stated invariants (Section 3.3, 3.4).
3. An evaluation on 998 fixtures with metrics defined before results, a held-out half for the
   parameters, a per-phase ablation, a failure taxonomy, bootstrap intervals over fixtures and
   timing with and without the parse (Sections 5 and 6).
4. A list of what is not established (Sections 7 and 8).

We do not claim a new objective, optimality of the refined mapping, accuracy on code outside the
fixture corpus or an advantage over GumTree-family matchers on their own evaluation sets; none of
those was measured here.

## 2 Problem statement

An *ordered labelled tree* T has nodes V(T), a root, an ordered child list per node and a label per
node. Here a tree is a tree-sitter concrete syntax tree: every node is kept, a leaf's label is its
(kind, text) pair and an internal node's label is its kind. Let B (before) and A (after) be two
trees with n = |V(B)| and m = |V(A)|.

A **mapping** M is a partial bijection M ⊆ V(B) × V(A). Nodes of B outside M are *deleted*, nodes of
A outside M are *inserted*. We call a pair (b, a) *kind-compatible* if both are leaves, or both are
internal with equal kind (leaves of different text may be paired: that is an update).

**Top-down mapping (Selkow).** M is *top-down* if (root_B, root_A) ∈ M, every other pair has its
parents paired, and M preserves sibling order. The *top-down distance* is the minimum, over top-down
mappings, of the number of unpaired nodes plus the number of paired nodes with different labels.
It is computed by a recursion over aligned child lists:

```text
dist(x, y) = 0                                              if x and y are identical subtrees
           = [label x != label y] + align(kids x, kids y)    otherwise (roots always pair)

align(A, B) = min over order-preserving pairings of
              sum(size a : a deleted) + sum(size b : b inserted) + sum(dist(a, b) : (a, b) paired)
```

**What a top-down mapping cannot say.** (i) *Move*: a subtree whose parent changes. (ii) *Reorder*:
a child whose sibling order changes. (iii) *Wrap*: a new internal node inserted between a node and
its former parent; *unwrap* is the inverse. In each case the nodes below the affected one exist on
both sides, but no top-down mapping can pair them.

**Task.** Given B and A, output a kind-compatible mapping M that agrees as closely as possible with
the correspondence a careful human would draw. Agreement is measured against hand-authored mappings
(Section 5.2). The output is not required to be an optimum of any cost model, to be top-down or to
preserve order.

**Why not general tree edit distance.** General (Zhang-Shasha-style) edit distance can express wraps
and unwraps but not moves, and its best known algorithms are cubic in tree size in the worst
case; conditional lower bounds say that no strongly subcubic algorithm exists unless the all-pairs
shortest-paths conjecture fails (Bringmann et al.). The top-down objective has a quadratic-time
algorithm (Selkow). We keep the top-down core exact and fast and repair its output.

## 3 The difffold algorithm

### 3.1 Exact identity (I1)

Nodes live in an arena. `Arena::mk(label, kids)` returns an id; two nodes of one arena have equal ids
if and only if their labels and child id lists are equal (hash consing; Filliâtre and Conchon).
The hash only selects a bucket; equality is checked on a hit, so the property does not depend on the
hash function. Equality of two subtrees is therefore an integer comparison, and the arena stores one
copy of each distinct subtree.

Cost: one pass over each tree, expected O(n + m) hash operations. A test that injects a constant
bucket function exists because an earlier version of the interner failed exactly in that case
(`tests/boundaries.rs`, `constant_bucket_function_keeps_identity_and_distance_exact`).

### 3.2 Certified top-down alignment (C2) and replay (C3)

For child lists a (length p) and b (length q), let R_a(i) be the total size of a[i..] and R_b(j) that
of b[j..], and h(i, j) = |R_a(i) − R_b(j)|. Each inserted or deleted node changes the size difference
by one, so h is an admissible lower bound on the remaining cost. The alignment DP keeps a cell only
if F(i, j) + h(i, j) ≤ τ, starting from τ = h(0, 0) and widening τ until the final cell is kept. The
result is accepted only when the final cell is kept (**C2**): any path of cost at most τ survives
pruning, so the returned value is the true minimum. Recursive pair costs are memoised on the exact
(id, id) key, and equal leading and trailing children are stripped first.

Every script is replayed against the before-tree and must rebuild the after-tree id for id, with its
summed cost equal to the reported distance (**C3**, `diff_checked`). Replay shows reconstructability;
it does not show optimality or that the pairing is the intended one.

*Complexity.* Without pruning the DP over one pair of child lists has O(p·q) cells and the memo bounds
the number of distinct (id, id) pair costs by the number of distinct subtree pairs, so the whole
computation is O(n·m) in the worst case (the classical Selkow bound). Pruning only removes cells.
Identical subtrees cost O(1). On the fixtures, the cost is dominated by the DP on the changed region.

The pruning bound, the threshold decision, the widening search and the strip lemma are mechanised in
Lean over a model of the objective (five modules of about 910 lines, no `sorry`, no custom axiom,
`proof/Difffold/`). Separately, `proof/Kernel/` holds Lean theorems over the Aeneas translation of the
shipped `src/kernel.rs` (the threshold DP): its `fill_correct` states, under hypotheses listed in
`proof/README.md` (suffix sums supplied by the caller, a pair-cost oracle that respects the size bound,
total size below 2^27), that `fill` returns a result exactly when the grid optimum is at most τ and
then returns that optimum. It does not cover that the grid is the child-list alignment of two nodes
and that the oracle is the recursive distance (properties of `diff.rs`), the interner, replay or
anything in the refinement. These statements are as recorded in `proof/README.md`; they were not
re-checked with Lean for this paper. Everything else is tested against an independent oracle
(`tests/`), not proved.

### 3.3 Cross-level refinement

The top-down result is converted into a correspondence on preorder indices and then repaired. All
phases act only on nodes that are still unmapped, except phase 1, which may replace a *tentative*
pair (one inside a subtree that is not identical on both sides). `Options::FULL` runs all of the
following, in order (`src/refine.rs`).

0. **Seed.** Keep the top-down pairs except those between internal nodes of different kind. (The
   top-down objective expresses a wrap as a relabel of the wrapper to the wrapped node; such a pair is
   dropped so later phases can place both nodes properly.) Pairs inside identical subtrees are *firm*.
1. **Exact (moves and reorders of unchanged code).** Index unmapped after-subtrees of size ≥ 2 by arena
   id. Process unmapped before-subtrees largest first; pair each with an unmapped after-subtree of the
   same id, preferring one whose parent is the partner of its parent, otherwise the nearest in
   preorder, and only if the subtree has at least `anchor_below` = 3 nodes (smaller subtrees move only
   between paired parents). Because equal ids mean equal subtrees (I1), the two subtrees are paired node
   for node. Candidate lookup is an id comparison.
2. **Validate.** Bottom-up, drop a tentative internal pair whose Dice similarity of mapped descendants
   2|common|/(|desc b| + |desc a|) is below `keep` = 0.3. The top-down objective pairs two same-kind
   siblings whenever relabelling is cheaper than deleting one and inserting the other, however
   different their contents.
3. **Containers (bottom-up).** For each unmapped internal before-node, count for each unmapped
   after-node of the same kind how many of its descendants' partners lie inside it; pair with the best
   candidate if the Dice similarity reaches `dice` = 0.5.
4. **Recover.** For each container pair made in phase 3 (outermost first) run the certified top-down
   aligner on the two subtrees and add its pairs where both nodes are unmapped and of equal kind;
   then pair unmapped leaf children of equal label under paired parents, in order.
5. **Descend and retarget.** For each unmapped leaf (or tentative leaf pair whose texts differ), climb at
   most `hops` = 3 ancestors to the nearest mapped one and pair the leaf with the unmapped (or
   re-targetable) after-leaf of equal label inside the partner's subtree whose offset is closest.
   Such pairs are cross-level by construction.
6. **Orphans.** A leaf pair outside an identical subtree stands only if the parents of its two leaves are
   paired with each other, unless it was made in phase 5.

*Why this shape.* Phases 1 and 5 are move/wrap detection for unchanged code and leaves. Phases 2 and 3
are the bottom-up half of two-phase matchers (the Dice criterion is the one GumTree's bottom-up phase
uses); phase 4 is their recovery step. They differ from GumTree in that the top-down seed is an exact
optimum rather than a greedy match on subtree height, and in that identity of subtrees is an O(1) id
test.

*Complexity.* Let d be the maximum depth. Flattening, seeding and orphan removal are O(n + m). Phase 1
is O(n + m) hashing plus O(c log c) for sorting c candidates plus, for each before-subtree, a scan of the
after-candidates with the same id; the scan is bounded by the number of same-id pairs and is short on
real code because small subtrees are excluded; linking is O(size) and every node is linked at most once
in this phase. Phase 2 is O((n + m)·d). Phase 3 walks, for each unmapped before-node, its mapped
descendants and the ancestors of their partners: O(n·d²) in the worst case. Phase 4 runs the top-down
aligner on subtrees of pairs made in phase 3, so its cost is at most d times the top-down cost in the
worst case (nested pairs); on the corpus phase 3 makes 212 pairs in 59 of 998 fixtures (Table 4b). Phase 5 is
O(L·hops·(log m + k)) for L unmapped leaves and k same-label candidates inside the range. The worst
case for the refinement as a whole is therefore O((n + m)·d² + d·T) with T the top-down time, and
quadratic in the adversarial case of very many identical small subtrees. We do not have a better
worst-case bound; Section 6.4 reports the measured scaling.

### 3.4 Properties

For every input the refined result is (i) a partial bijection, (ii) kind-compatible on every pair,
(iii) deterministic (no hashing order or randomness reaches the output), and (iv) with all later phases
switched off, equal to the top-down mapping minus kind-changing internal pairs. These are tested
(`tests/refine.rs`) on hand-built moves, reorders, wraps and unwraps and on 59 random tree pairs. The
refined mapping is not a top-down mapping, not order-preserving and not an optimum of the top-down or
any other objective; it carries no certificate beyond (i) to (iv).

## 4 Related work

**Tree edit distance.** Selkow's top-down distance (Selkow 1977) and Zhang and Shasha's ordered tree
edit distance (Zhang and Shasha 1989) fix the two operation sets used here. RTED and APTED
(Pawlik and Augsten 2011, 2016) choose decompositions adaptively to speed up the general problem;
Bringmann et al. (2018) give a conditional cubic lower bound for it. `difffold` keeps a top-down
optimum as its core because it admits an admissible pruning bound.

**Change extraction and heuristic matching.** Chawathe et al. (1996) derive edit scripts from a
matching of hierarchical data; ChangeDistiller (Fluri et al. 2007) matches nodes bottom-up from leaf similarity. GumTree (Falleri et al. 2014) matches the largest
isomorphic subtrees top-down by height and then inner nodes bottom-up by Dice similarity of mapped
descendants, followed by a recovery step (Falleri et al. 2014); Falleri and Martinez (2024) revisit it for accuracy and
scalability. MTDiff (Dotzler and Philippsen 2016) optimises scripts for moves. The refinement
phases of `difffold` follow the same two-phase shape but start from an exact top-down mapping and use
O(1) subtree equality from hash consing; truediff (Erdweg et al. 2021) also identifies equal subtrees by (cryptographic) hashes, in a
different design: a linearly typed edit-script language, with a proof of linear run time for its
algorithm.

**Benchmarks.** Fan et al. (2021) test AST mapping algorithms differentially and report inaccurate
mappings for 20-29% (GumTree), 25-36% (MTDiff) and 21-30% (IJM) of the file revisions they examined; Alikhanifard and Tsantalis (2025)
build a benchmark of AST node mappings from 800 bug-fixing and 188 refactoring commits and
measure precision and recall against it. OmniDiff, the
baseline here, is an open-source tree-sitter based structural diff tool distributed with
hand-authored node mappings; its README cites no paper, so we cite its repository and commit (AGPL-3.0 with a
separate commercial licence). Its fixtures are the only ground truth used in this paper.

## 5 Evaluation design

### 5.1 Research questions

- **RQ1.** How accurate is the refined mapping compared with the top-down mapping and with OmniDiff,
  on the same fixtures and the same scorer?
- **RQ2.** What does each refinement phase contribute?
- **RQ3.** Do parameters chosen on part of the data transfer to the rest?
- **RQ4.** What does the refinement cost in time, with and without the parse, compared with the
  top-down core, OmniDiff and GumTree?
- **RQ5.** Where do the remaining errors concentrate?

### 5.2 Metrics (defined before results)

The scorer is `src/bin/score_accuracy/`. Ground truth is OmniDiff's `human_mapping.json` per fixture,
converted to tree-sitter preorder indices (every node, named and anonymous).

- **Pair precision, recall, F1.** A tool's pairs against the ground-truth pairs. ~99.8% of
  ground-truth pairs are unchanged context that any matcher gets right, so pair F1 saturates near 1.
- **Node-correspondence accuracy.** The share of graded decisions (pair, delete, insert, group
  member) judged correct.
- **Changed-span F1.** Over *tokens* (leaves that are not whitespace, comments or punctuation). A
  token is *changed* if it is unmapped, or its partner has a different label; a moved identical token
  is unchanged. Precision, recall and F1 compare the tool's changed tokens with the ground truth's.
  Micro: sum counts over fixtures. This is the metric closest to "what a reviewer sees highlighted".
- **Perfect fixture.** Zero *visible* mismatches against the ground truth, where visibility is
  OmniDiff's definition (a node with non-whitespace text of its own). *Near-perfect* is at most a few
  mismatches (as defined in the scorer).
- **Class accuracy.** Each failed decision is attributed to a root-cause class (local edit, sibling
  insert/delete, repeated children, reorder, cross-parent move, wrap/unwrap, wholesale rewrite,
  context); class accuracy is the share of that class's decisions that are correct. Definitions are
  in the scorer source.
- **Uncertainty.** Percentile bootstrap over fixtures (the unit of independence), 10,000 resamples,
  paired where two tools are compared (`harness/bootstrap_ci.py`).
- **Timing.** In process, per fixture and per stage, the median, minimum and maximum over n = 10 passes.
  difffold stages: *parse* (tree-sitter, both files), *convert* (arena and interner), *prod* (the
  production path: certified top-down diff with replay; for the refined tool also correspondence,
  flattening and refinement). OmniDiff stages: *parse* (tree-sitter only), *load* (parse plus the AST
  metadata its diff needs), *diff* (`diff_code_with_config`). Four views, each a sum of stages:
  *matching only* (difffold prod against OmniDiff diff); *own work* (difffold convert + prod against
  OmniDiff load minus parse plus diff, i.e. the shared tree-sitter parse taken out); *with parse*
  (difffold parse + convert + prod against OmniDiff load + diff); and the cold-process wall time of
  `dfold-cli` (process start to exit). Then medians and quantiles over fixtures; ratios (OmniDiff over
  difffold) are computed per fixture and also as ratios of totals. The headline is the *with parse*
  ratio, because it is what a caller who starts from files sees; the other views say where the time goes.

### 5.3 Setup

**Corpus.** The public OmniDiff repository (https://github.com/ivankovic/omnidiff, commit
`ee5ee5b43b39602ef68b6ebb30ddeeea5e843265`, crate 0.4.0) ships `src/test/data/diffs`, 1,761 before/after
fixtures with hand-authored `human_mapping.json` ground truth (Defects4J-derived, handmade, "full" and
stratified real-world changes). A fixture is *scorable* if it is in a language for which a tree-sitter
grammar is wired in here (C, Go, Java, JavaScript, Python, Rust, TSX, TypeScript), its ground truth loads
and has pairs, and node counts agree with OmniDiff's. 998 of 1,761 are scorable (515 Java); 763 are not,
758 of them for language (C++, C#, Kotlin, shell, HTML, JSON and others; the list is
`results/accuracy/unscorable.csv`). No fixture was dropped for a node-count mismatch. An earlier version
of this work scored 1,001 fixtures on a private fork of OmniDiff; the public corpus is a different
snapshot and those numbers are not mixed with these (`results/accuracy/previous-fork-run/`).

**Split.** To keep part of the parameter choice apart from reporting, fixtures are split by the low bit of
the upper half of the FNV-1a hash of `dataset/name` (`DFOLD_SPLIT=dev|test`): 505 *dev* and 493 *test*
fixtures. The split is **partial protection only**. The first implementation of the refinement (before
this split existed) fixed `dice` = 0.5, `keep` = 0.3, `min_exact` = 2 and the validate and orphan rules
after exploratory runs over all fixtures that were not recorded; these were not re-selected. What was
chosen on dev alone: `anchor_below` = 3 (highest dev changed-span F1, tied with 2, the larger taken),
`hops` = 3, and the design of the descend and retarget phases from dev failures. The test half was scored
after these were frozen. It had also been scored earlier in the work, with the configuration before the descend and retarget
phases existed (changed-span F1 0.955), and that number was seen before the phases were designed, so the test half is not
blind to their design.
Sweeps over the inherited thresholds on dev show they sit on a plateau (`results/accuracy/sweeps/dev-sweep.tsv`).

**Systems compared.** (a) *top-down*: `diff_checked` followed by `mapping::correspondence`, no
refinement. (b) *difffold*: top-down plus `refine` with `Options::FULL`. (c) *OmniDiff*: its own node
mapping dumped by `tools/omni_dump` (default `HeuristicConfig`), scored by the same scorer. (d) *GumTree*
4.0.0-beta4: accuracy on the Java fixtures with three matchers (Section 6.3) and cold-process time on a subset (Section 6.4).

**Machine and toolchain.** One shared four-vCPU virtual machine (Intel Xeon Processor at 2.30 GHz, 16 GB, Linux 6.18.44), Rust 1.97.0
(`cargo build --release`, opt-level 3, no LTO), OpenJDK 21.0.12.1, tree-sitter 0.26.13 with the grammar crates pinned in
`Cargo.lock` (C 0.24.2, Go 0.25.0, Java 0.23.5, JavaScript 0.25.0, Python 0.25.0, Rust 0.24.2, TypeScript 0.23.2), apeiron
revision `07ab506`. OmniDiff `ee5ee5b43b39602ef68b6ebb30ddeeea5e843265` built with its `ci` profile (release, no LTO, 16
codegen units); GumTree 4.0.0-beta4 from the release archive (sha256 `a9f94acc...a3ea`, full value in the machine files).
`difffold` commits and load averages are recorded in `results/accuracy/machine.txt` (accuracy) and
`harness/results/machine-t4.txt` (speed). The accuracy scorer is deterministic. All timing was taken while other jobs
kept the load average between 20 and 85 on the four vCPUs, and every timed process ran at `nice` 10.


## 6 Results

### 6.1 RQ1: accuracy on 998 fixtures

Table 1. Micro averages over all 998 scorable fixtures. Source: `results/accuracy/topdown/summary_tables.md`
(top-down and OmniDiff rows), `results/accuracy/summary_tables.md` (refined and OmniDiff rows). The OmniDiff
rows of the two files agree.

| metric | top-down | difffold (refined) | OmniDiff |
|---|---:|---:|---:|
| micro pair F1 | 0.998 | 1.000 | 1.000 |
| node-correspondence accuracy | 0.996 | 0.999 | 0.999 |
| changed-span precision | 0.741 | 0.974 | 0.962 |
| changed-span recall | 0.980 | 0.956 | 0.984 |
| **changed-span F1** | **0.844** | **0.965** | **0.973** |
| fixtures with zero visible mismatches | 56.8% | 75.3% | 82.1% |
| near-perfect fixtures | 85.4% | 92.5% | 96.4% |

Table 2. Percentile bootstrap over fixtures (10,000 resamples, 95%). Source: `results/accuracy/ci.md`.

Percentile bootstrap, 10000 resamples of 998 fixtures, seed 1. 95% interval.

| tool | micro pair F1 | micro changed-span F1 | perfect fixtures |
|---|---|---|---|
| difffold | 0.9995 [0.9993, 0.9997] | 0.9649 [0.9525, 0.9752] | 0.7525 [0.7265, 0.7786] |
| omnidiff | 0.9997 [0.9995, 0.9998] | 0.9729 [0.9625, 0.9815] | 0.8206 [0.7966, 0.8447] |
| difffold-baseline | 0.9980 [0.9973, 0.9985] | 0.8437 [0.7990, 0.8808] | 0.5681 [0.5381, 0.5982] |

Paired difference difffold minus omnidiff (same resamples):

| metric | difference |
|---|---|
| micro pair F1 | -0.0001 [-0.0003, -0.0000] |
| micro changed-span F1 | -0.0080 [-0.0175, +0.0013] |
| perfect fixtures | -0.0681 [-0.0892, -0.0471] |

Pair F1 is saturated (99.8% of ground-truth pairs are unchanged context) and is reported for
continuity only. The refinement removes most of the changed-span gap: 0.844 to 0.965, against OmniDiff's
0.973. The paired difference to OmniDiff is -0.008 with an interval that includes zero; OmniDiff's
perfect-fixture rate remains higher by 6.8 percentage points and that interval excludes zero. The
change is a trade: precision rises from 0.741 to 0.974 (the top-down matcher reported moved and wrapped
code as changed) while recall falls from 0.980 to 0.956 (the refinement sometimes pairs tokens the ground
truth calls changed). By language, difffold's changed-span F1 is above OmniDiff's on C (0.892 against
0.885), Go (0.989 against 0.966) and TSX (0.978 against 0.970) and below it on the other five, the
largest gap being Python (0.951 against 0.990); `results/accuracy/summary_tables.md`.

Micro changed-span F1 is dominated by a few large fixtures: ten of the 998 carry 50% of difffold's
changed-token errors (1,171 false plus missed tokens) and 50% of OmniDiff's (923). The bootstrap interval, the
macro averages in the same file and the per-fixture perfect rate should be read next to it.

Table 3. Decision accuracy by root-cause class (share of that class's graded decisions that are correct).
Source: `results/accuracy/topdown/summary_tables.md` and `results/accuracy/summary_tables.md`, section "Failures
by root-cause class".

| class | decisions (refined run) | top-down | refined | OmniDiff |
|---|---:|---:|---:|---:|
| local edit | 559 | 0.941 | 0.921 | 0.918 |
| sibling insert/delete | 42,186 | 0.936 | 0.942 | 0.972 |
| repeated children | 3,375 | 0.621 | 0.679 | 0.741 |
| reorder | 1,044 | 0.034 | 0.832 | 0.905 |
| cross-parent move | 1,101 | 0.186 | 0.860 | 0.809 |
| wrap / unwrap | 20,845 | 0.401 | 0.902 | 0.947 |
| wholesale rewrite | 3,983 | 0.952 | 0.969 | 0.968 |
| context | 5,033,129 | 1.000 | 1.000 | 1.000 |

Reorder, move and wrap decisions, which a top-down matcher cannot make, go from 0.034, 0.186 and 0.401 to
0.832, 0.860 and 0.902. On cross-parent moves the refined mapping is above OmniDiff's (0.860 against
0.809); on reorder and wrap/unwrap it is below. For the reorder and cross-parent-move classes every graded decision is a ground-truth *pair*, so these
accuracies are pair recalls of reordered and moved nodes: reorder 35 of 1,044 pairs recovered by the top-down
matcher, 869 by the refinement, 945 by OmniDiff; cross-parent move 205, 947 and 891 of 1,101. For wrap/unwrap
the pair recall is 829, 9,311 and 9,717 of 10,328 (`results/accuracy/class_pair_recall.csv`; the
top-down column is in `results/accuracy/topdown/`). The corpus has 127 ground-truth move roots, 1,301
wrap/unwrap roots and 108 reordered pairs (`results/accuracy/taxonomy.csv`).

### 6.2 RQ2: ablation of the refinement phases

Table 4. Cumulative phases on the 998 fixtures (difffold only, `DFOLD_REFINE` = the listed phases, all
other parameters as frozen). Source: `results/accuracy/ablation/*/SUMMARY-difffold-only.md`.

| phases | pair F1 | span P | span R | span F1 | perfect |
|---|---:|---:|---:|---:|---:|
| seed (top-down minus kind-changing pairs) | 0.998 | 0.741 | 0.980 | 0.844 | 59.1% |
| + exact | 1.000 | 0.952 | 0.965 | 0.958 | 69.8% |
| + validate | 1.000 | 0.952 | 0.965 | 0.958 | 69.8% |
| + containers | 1.000 | 0.952 | 0.965 | 0.958 | 69.8% |
| + recover | 1.000 | 0.955 | 0.964 | 0.960 | 70.3% |
| + descend | 1.000 | 0.971 | 0.957 | 0.964 | 74.4% |
| + retarget (= full) | 1.000 | 0.974 | 0.956 | 0.965 | 75.3% |

The exact-subtree phase accounts for almost all of the gain in span F1 (+0.114 of +0.121). The validate
and containers phases change none of the reported aggregates on this corpus: they are included because
they are the bottom-up half of the usual two-phase design and because recovery depends on container
pairs, but this ablation gives no evidence that either helps on these fixtures (the recover phase,
which consumes container pairs, adds +0.002). Descend and retarget add +0.005 span F1 and 5.0
percentage points of perfect fixtures, mostly by pairing leaves that the top-down seed relabelled.
Table 4b. What each phase did, summed over the 998 fixtures. Source: `results/accuracy/phase-counts.md`.

Refinement counters summed over 998 fixtures (Options::FULL).

| counter | total | fixtures where it is non-zero | meaning |
|---|---:|---:|---|
| seed | 5171228 | 998 | top-down pairs kept (kind-changing pairs removed) |
| dropped | 2534 | 363 | top-down pairs dropped for changing kind |
| exact | 12385 | 283 | nodes paired by the exact-subtree phase |
| invalid | 259 | 96 | tentative pairs dropped by validate |
| containers | 212 | 59 | container pairs made |
| recovered | 325 | 53 | nodes paired by recover |
| descended | 694 | 176 | leaves paired by descend and retarget |
| orphans | 316 | 99 | leaf pairs dropped by the orphan rule |

The ablation is cumulative and in one order; interactions between phases are not separated.

### 6.3 RQ3: held-out half and a second dataset

Table 5. Dev-chosen choices (`anchor_below`, `hops`, descend, retarget) frozen, scored on test. Source: `results/accuracy/split-dev/` and
`results/accuracy/split-test/` (`summary_tables.md`).

| half | fixtures | difffold span F1 | OmniDiff span F1 | difffold perfect | OmniDiff perfect |
|---|---:|---:|---:|---:|---:|
| dev | 505 | 0.966 | 0.974 | 75.6% | 81.0% |
| test | 493 | 0.964 | 0.972 | 74.8% | 83.2% |

The held-out half is within 0.002 of the dev half in changed-span F1 and the ordering to OmniDiff is
the same. This supports that the dev-chosen choices are not overfitted to individual fixtures (the inherited thresholds were not held out, Section 5.3); it is not an
out-of-corpus test, because both halves come from the same collection, and the design of two phases
(descend, retarget) was guided by dev failures. `results/accuracy/sweeps/dev-sweep.tsv` records the
one-at-a-time sweeps on dev: changed-span F1 stays within 0.963 to 0.966 over `dice` 0.3 to 0.7, 0.964 to 0.966 over `keep`
0.2 to 0.5 and 0.963 to 0.966 over `min_exact` 2 to 5, but ranges from 0.948 to 0.966 over `anchor_below` 2 to 12 and from
0.950 to 0.966 over `hops` 0 to 12; precision and recall trade against each other along both.

**GumTree on the Java fixtures.** We ran GumTree 4.0.0-beta4 in process (`tools/gumtree_eval/java/Eval.java`, JDT generator, one pass
per matcher per fixture; the run was split in two JVM sessions after an interruption, and only the first did warm-up) on the 515 Java fixtures, converted its mappings by byte range onto the tree-sitter preorder numbering
(`tools/gumtree_eval/gt2map`) and scored them with the same scorer. GumTree's JDT tree has no node for punctuation and for some wrappers,
so scoring every tree-sitter node (*raw*) charges it for nodes it cannot express and gives 0% perfect fixtures for every matcher; we report
the *scoped* scoring, which judges only the nodes GumTree's tree contains and is therefore lenient to GumTree and not to difffold or OmniDiff.

Table 7. Java fixtures only (515), micro averages, same scorer. Source: `results/accuracy/gumtree-4.0.0-beta4/COMPARE.md`.

| tool | changed-span F1 | perfect fixtures | in-process matching, median |
|---|---:|---:|---:|
| GumTree `gumtree-simple` (default), scoped | 0.958 | 74.2% | 1.19 ms |
| GumTree `gumtree-hybrid-id`, scoped | 0.961 | 74.0% | 1.61 ms |
| GumTree `gumtree-classic`, scoped | 0.846 | 31.3% | 429 ms |
| difffold (refined) | 0.965 | 75.9% | see Table 6 |
| OmniDiff | 0.978 | 83.9% | see Table 6 |

On this corpus and scoring, difffold's refined mapping is level with GumTree's default and hybrid matchers (changed-span F1 0.965 against 0.958 and 0.961;
perfect fixtures 75.9% against 74.2% and 74.0%) and ahead of `gumtree-classic`; OmniDiff is ahead of all of them. We did not compute intervals for the GumTree
comparison, the leniency of the scoped scoring favours GumTree, and the corpus is OmniDiff's. GumTree's matching time excludes
its 42 ms median JDT parse of the two files (`times.tsv`); the cold-process comparison is in Section 6.4.

**A second ground truth: DiffBenchmark's Defects4J oracle.** The only other public mapping ground truth we could
run is the Defects4J oracle of DiffBenchmark (Alikhanifard and Tsantalis; `hrd-oracle/adb-paper/d4j-exp`, 996 files of 800
bugs, derived from RefactoringMiner's output with manual fixes). It is a second *annotation*, not a second
*input set*: its source files are OmniDiff's Defects4J fixtures (996 directories; the 444 that carry OmniDiff ground truth are part of
Section 6.1, about half of them in the dev half), and difffold's top-down and refined mappings were converted onto RefactoringMiner's JDT trees by the adapter in
`tools/diffbenchmark_adapter/` (byte-range matching, same-type pairs only, plus a completion step for JDT wrapper nodes that
tree-sitter has no counterpart of; without the completion the precision of the top-down engine collapses, see
`notes/lanes/DIFFBENCHMARK.md`). We ran DiffBenchmark's own scoring code (`HRDBenchmarkComputer` over HRDGen3 renderings) for RefactoringMiner 3.0.10
(`RMD`), GumTree 3.0 greedy (`GTG`) and simple (`GTS`), difffold top-down (`DFT_TD`) and difffold refined (`DFT_RF`). The metric is
the benchmark's: true positives, false positives and false negatives of mappings between nodes of the two JDT trees (abstract
mappings plus program elements), reported here raw, without the adjustment for mappings all tools share, and the number of files with no false
positive or negative ("perfect").

<!-- DFB:begin -->
The run covers all 800 bugs and all 996 oracle files (it was interrupted twice, by a full disk and by an out-of-memory kill, and resumed from its append-only outputs; `conversion.csv` therefore counts only the last resumed part, 250 bugs). Table 8 reports counts recomputed from the per-file records.

Table 8. DiffBenchmark Defects4J oracle, 996 files, raw counts. Source: `results/diffbenchmark/rerun-refine/SUMMARY.md`, computed by `harness/dfb_summary.py` from `records-NO_FILTER.csv` in the same directory.

| tool | TP raw | FP | FN | precision (raw) | recall (raw) | F1 (raw) [95% interval] | perfect files |
|---|---|---|---|---|---|---|---|
| RMD | 596954 | 140 | 315 | 0.9998 | 0.9995 | 0.9996 [0.9995, 0.9997] | 881 (88.5%) |
| GTG | 593907 | 1139 | 3362 | 0.9981 | 0.9944 | 0.9962 [0.9958, 0.9966] | 209 (21.0%) |
| GTS | 596209 | 761 | 1060 | 0.9987 | 0.9982 | 0.9985 [0.9982, 0.9987] | 649 (65.2%) |
| DFT_TD | 595302 | 1686 | 1967 | 0.9972 | 0.9967 | 0.9969 [0.9963, 0.9975] | 449 (45.1%) |
| DFT_RF | 596565 | 987 | 704 | 0.9983 | 0.9988 | 0.9986 [0.9983, 0.9988] | 641 (64.4%) |

Paired F1 difference of DFT_RF to each other tool (same resamples):

| tool | difference | 95% interval |
|---|---|---|
| RMD | -0.00103 | [-0.00129, -0.00081] |
| GTG | +0.00236 | [+0.00209, +0.00265] |
| GTS | +0.00011 | [-0.00005, +0.00027] |
| DFT_TD | +0.00164 | [+0.00123, +0.00210] |

Perfect files (no false positive or negative): RefactoringMiner 88.5%, GumTree 3.0 simple 65.2%, difffold refined 64.4%, difffold top-down 45.1%, GumTree 3.0 greedy 21.0%. The refinement lifts the perfect-file rate of the top-down engine by 19.3 points on this oracle and puts it level with GumTree simple in raw F1 (difference +0.00011, interval [-0.00005, +0.00027], which includes zero; GumTree simple has 8 more perfect files, 649 against 641). It remains below RefactoringMiner (difference -0.00103, interval [-0.00129, -0.00081]), from whose output the oracle was built. The benchmark's own summary (`summary-NO_FILTER.csv` in the same directory) reports 884, 209, 652, 452 and 644 perfect files, three more than Table 8 for every tool but GreedyGumTree: three files (`Jsoup/87` twice, `Jsoup/92`) were in flight when the run was killed and were run again, so their records appear twice (15 identical duplicate rows, which the benchmark's summarizer adds up and `harness/dfb_summary.py` collapses). Table 8 counts each file once. Raw F1 differences are tiny because almost all mappings are shared by every tool; the perfect-file rate and the paired intervals are the informative columns. The perfect-file counts of RefactoringMiner, both GumTree matchers and difffold top-down are identical to the earlier recorded run on all 996 files (881, 209, 649, 449; `results/diffbenchmark/summary-NO_FILTER.csv`), so the harness reproduces. Conversion of difffold's mappings onto JDT trees in the resumed part: the refined mapping converts 664,335 pairs with 9 cross-type drops and no conflicts, against 663,004 and 683 cross-type drops for top-down (`conversion.csv`). This is a second annotation of overlapping inputs, the adapter's conversion between tree-sitter and JDT trees is part of what is measured, and the oracle favours RefactoringMiner.
<!-- DFB:end -->


### 6.4 RQ4: speed with and without the parse

**One headline.** With each tool's own preparation counted (difffold: tree-sitter parse, arena build, match and
refine; OmniDiff: tree-sitter parse, AST-metadata load, diff), difffold used **5.4 times less total time** on
120 Java, Go and C fixtures timed fixture by fixture against OmniDiff (median per-fixture ratio 8.8, 10th to 90th
percentile 4.4 to 42.0). That is not an order of magnitude: the tree-sitter parse and arena build are 98% of
difffold's time (5,226 of 5,345 ms), and the matching and refinement the paper is about are 2% (119 ms). Counted without the
parse on either side, the ratio is 20.3 (matching only: 146). Machine load was 68 to 85 on four vCPUs throughout,
so these are loaded-machine figures (Section 7).

Table 6. Paired, interleaved in-process timing, 120 fixtures drawn from the 350 of run `t4` (seed 1), ten passes per
fixture and tool, OmniDiff over difffold. Totals are sums over fixtures of the per-fixture median over the passes
(left) and of the per-fixture minimum (right). Source: `harness/results/paired-t4/SUMMARY.md` and `paired.csv`.

| view | OmniDiff total ms | difffold total ms | total ratio | median per-fixture ratio (p10 to p90) | total ratio, minima |
|---|---:|---:|---:|---:|---:|
| matching only, top-down core | 17,405 | 6 | 3,094 | 2,977 (211 to 17,185) | 2,555 |
| matching only, with refinement | 17,405 | 119 | 146 | 347 (57 to 597) | 302 |
| own work, parse removed on both sides, with refinement | 24,859 | 1,225 | 20.3 | 67.7 (13.0 to 118.7) | 33.2 |
| with parse, with refinement (OmniDiff load includes AST metadata) | 29,045 | 5,345 | **5.4** | **8.8** (4.4 to 42.0) | 6.4 |
| with parse, with refinement (OmniDiff tree-sitter parse only) | 21,591 | 5,345 | 4.0 | 6.8 (3.1 to 40.7) | 4.6 |

*Matching only* is difffold's production path (certified top-down diff with replay, correspondence, flattening and
refinement) against `diff_code_with_config`. *Own work* is difffold's arena build plus matching against OmniDiff's
AST-metadata load plus diff. The "parse only" row omits OmniDiff's metadata and so understates its
cost; the metadata is required by its `diff_code`. The top-down core on its own is 6 ms over these 120
fixtures; the refinement is 20 times that (119 ms) but 2% of the end-to-end time.

The unpaired run, in which OmniDiff (run `omni_time`) and difffold (`dfold-cli --reps 10`) were timed in different
load windows over all 350 fixtures, gives 3.6 for the same with-parse view and 88 for matching only
(`harness/results/unpaired-t4/SUMMARY.md`); we take the paired figures as primary and the difference between the
two as an indication of the measurement noise under this load. Median-of-passes and minimum-of-passes agree to within 20%
on the with-parse ratio (5.4 and 6.4).

Cold-process wall time (process start to exit, `dfold-cli`, 350 fixtures, up to ten rounds, shuffled order;
`harness/results/SUMMARY-t4.md`): top-down 19.7 s in total (median 15.9 ms, p90 146.6 ms, p99 604 ms); with
refinement 20.4 s (16.2, 151.0, 608 ms), i.e. the refinement adds 3.6% to the cold wall time of the command.
`git diff --diff-algorithm=myers`, which does not parse, takes 1.9 s (median 3.8 ms) on the same files.
GumTree 4.0.0-beta4 as a command (`gumtree textdiff`, cold JVM per call, default `gumtree-simple` matcher), timed in the same
shuffled rounds as difffold's cold process on 24 fixtures (seed 1, ten rounds each; `harness/results/SUMMARY-gtcmp-t4.md`): median
3,498 ms per call against 11.6 ms (top-down) and 10.2 ms (refined), total 94.4 s against 0.72 s and 0.76 s, p90 7,080 ms against 92 ms. This is the
command-line experience including JVM start and JIT warm-up, not a matching-time comparison (GumTree's in-process matching after warm-up has a median of
1.2 ms, Table 7); the load average was 62 to 79 during these runs.

*Scaling.* Over the 120 paired fixtures, the least-squares slope of log time on log node count is 0.88
for the refinement alone (per-fixture minima; 9 to 100,456 nodes; `harness/results/paired-t4/SUMMARY.md`; 0.91 over the
350 fixtures of the unpaired run), 1.01 for the arena build, 1.29 for the tree-sitter parse and 0.27 for the certified top-down core, whose cost follows the size of the changed
region rather than of the file. The refinement is therefore close to linear on these inputs, in line with the
argument of Section 3.3 and not a proof of it. The largest fixture (100,456 nodes, a generated C test file) takes 607 ms
to parse, 174 ms to build the arena, 0.6 ms for the top-down core and 21.7 ms for refined matching; OmniDiff's load
and diff on it take 1,582 ms and 2,119 ms in the same pass.


### 6.5 RQ5: where the remaining errors are

Measured as the excess of difffold's failed decisions over OmniDiff's, 58.1% of the net excess is in the
sibling insert/delete class and 42.5% in wrap/unwrap, 9.6% in repeated children and 3.5% in reorder;
classes where difffold fails less (cross-parent move, local edit, context) contribute negatively, so the
shares sum to more than 100% (`results/accuracy/summary_tables.md`, section "Failures by root-cause
class"). Fixtures where difffold has more visible mismatches than OmniDiff:
164 of 998 (16.4%), 114 of them containing a wrap or unwrap; OmniDiff is perfect and difffold is not in
94 (9.4%). Inspection of the dev-half failures shows two recurring patterns: (i) a repeated or
long-distance identical subtree is paired as a move when the ground truth records a deletion and an
insertion, and (ii) punctuation tokens (`(`, `)`, `{`, `}`, `;`) around a changed wrapper are paired
with a nearby equal token instead of being left unmatched. Two attempted fixes, restricting cross-parent
moves to subtrees that are unique on both sides and excluding punctuation from the leaf descent, did not
improve changed-span F1 on dev and were not adopted (they are not in the repository).


## 7 Threats to validity and what was not run

**Ground truth and scorer.** The ground truth is the mapping hand-authored by OmniDiff's authors, with
their notion of visible nodes, and OmniDiff was developed against these fixtures. Ambiguous cases (wrap,
group matches, duplicated code) are therefore decided in OmniDiff's favour, and OmniDiff's numbers are
an in-sample upper end. The scorer reproduces OmniDiff's own checker on OmniDiff's output (3,251 visible
mismatches in both, zero/non-zero agreement 100% on 998 fixtures; `results/accuracy/summary_tables.md`,
"Calibration"), which validates the scorer for OmniDiff's mapping; it ignores operation kinds
(identical versus update) and the subtree-closure step of groups, which OmniDiff's checker enforces.
No independent annotation of difffold's output exists.

**Selection and leakage.** The dev/test split is by fixture name hash, not by project, so the two halves
contain fixtures from the same repositories and, for Defects4J, from the same project histories. The
held-out result bounds overfitting of thresholds only to the extent that fixtures are independent. Two
phases were designed while reading dev failures. The corpus was also used by the previous version of
this work to choose what to build (the failure taxonomy of the top-down matcher), so the whole corpus
is not blind to the design.

**Coverage.** Eight languages; Java is 52% of the scorable fixtures; the corpus is changes in open-source
repositories curated by OmniDiff's authors, with a preference for difficult cases, and says nothing about
the distribution of everyday diffs, about documents other than source code, or about languages without a
wired grammar (758 fixtures were not scorable for that reason). No temporal web or document data was
used.

**Metric.** Changed-span F1 is a token-level view that excludes comments and punctuation; micro averages
are dominated by a few large fixtures (ten fixtures carry half of the errors of either tool), so we also give
the bootstrap interval over fixtures, the perfect-fixture rate and per-class accuracy. The paired
difference in changed-span F1 to OmniDiff is not distinguishable from zero in this corpus; that is not
evidence of equality, only of the interval's width (about 1 point). The class attribution is the scorer's
heuristic root-cause assignment, not a causal analysis.

**Ablation.** Cumulative in one order. The null result for validate and containers may be specific to this
corpus (few unmatched same-kind containers remain after the exact phase); we did not construct inputs
on which they matter.

**Timing.** The machine is a shared four-vCPU VM. During every timing run the one-minute load average was
between 20 and 85 (recorded per fixture in `harness/results/cli-t4.csv` and in the paired file), mostly
other jobs of the same host, and all of our timed processes ran at `nice` 10. Absolute times are therefore
several times those of an earlier run on a quiet machine of the same size (`results/fixtures-java-go-c.csv`,
OmniDiff median 9.6 ms there); we report per-fixture minima beside medians for that reason and
interleave the two tools fixture by fixture in the paired run, but a ratio measured under this load is
still less reliable than one measured on an idle machine, and we have not repeated it on one. OmniDiff was
timed in process through its library (parse, AST metadata load, `diff_code_with_config`), not through its
command-line binary, whose JSON rendering and process start are not included; OmniDiff's load step
computes AST metadata that `diff_code` needs, difffold's convert step builds the arena that `diff`
needs, and the with-parse view adds each tool's own preparation. GumTree was timed as a cold JVM
process on a 24-fixture subset, interleaved with difffold's cold process in the same rounds. All timings are single-threaded for the Rust tools.

**Not run.**
- GumTree accuracy outside Java (its Go and C generators were not run for accuracy) and any interval for the GumTree
  comparison; RefactoringMiner accuracy on the OmniDiff corpus (earlier indicative results for a different GumTree snapshot
  and corpus snapshot are in `notes/lanes/GUMTREE-RM.md`); difftastic and diffsitter accuracy and timing (earlier 80-fixture
  wall-clock results are in `harness/results/`).
- The DiffBenchmark RefOracle (the benchmark paper's main oracle) and the Zenodo/GitHub datasets
  of GumTree 3 and BDiff, which have no ground-truth mapping.
- General (Zhang-Shasha-style) tree edit distance with the refinement: the scorer supports `DFOLD_TED`
  but the refinement was not combined with it.
- Idle-machine timing and multi-machine timing.


## 8 Reproducing

Everything below runs from a clean checkout plus an OmniDiff checkout at the recorded commit. Paths in
`results/` and `harness/results/` that name scratch directories are the recording machine's.

```sh
# tests (no parser needed)
cargo test --release --locked -p difffold            # includes tests/refine.rs
cargo fmt --all --check && cargo clippy --release --locked -p difffold -p difffold-harness -p gitcompat --all-targets --features difffold/ts -- -D warnings
#   with Rust 1.97 add `-A clippy::manual_is_multiple_of -A clippy::unnecessary_sort_by` (two pre-existing lints); linebench does not build on main

# OmniDiff's own mappings, and the accuracy tables (results/accuracy/)
#   tools/omni_dump is its own workspace; edit the absolute `omnidiff` path in its Cargo.toml to your checkout
(cd tools/omni_dump && cargo build --profile ci) && tools/omni_dump/target/ci/omni_dump DIFFS DUMP
cargo build --release --locked -p difffold --features ts --bin score_accuracy
harness/accuracy.sh DIFFS DUMP target/release/score_accuracy OMNIDIFF_CHECKOUT
harness/dev_sweep.sh DIFFS target/release/score_accuracy results/accuracy/sweeps/dev-sweep.tsv

# speed (harness/results/*-t4.*)
python3 harness/select_fixtures.py --diffs DIFFS --baseline BASELINE.csv --work WORK --out manifest-t4.tsv --slowest 50 --sample 300 --seed 1
cargo build --release --locked -p difffold-harness     # dfold-cli, cli_bench
(cd tools/omni_dump && cargo build --profile ci --bin omni_time)
target/release/cli_bench --manifest manifest-t4.tsv --tools tools-t4.tsv --out cli-t4.csv --max-reps 10 --slow-ms 5000 --seed 1 --tmp TMP
python3 harness/paired_speed.py --manifest manifest-t4.tsv --diffs DIFFS --dfold-cli target/release/dfold-cli --omni-time OMNI_TIME --out paired-t4.csv --n 100 --reps 10
python3 harness/stage_summary.py --paired paired-t4.csv --out harness/results/paired-t4
```

`BASELINE.csv` for `select_fixtures.py` is a table with columns `repository,path,language,status,bytes_before,
bytes_after,elapsed_ms`; for `t4` it was built from file sizes (so "slowest 50" means the 50 largest inputs),
because OmniDiff's own `benchmark_diff_pairs` timings were not produced here. `harness/results/machine-t4.txt`
and `results/accuracy/machine.txt` record the machine, toolchain and source revisions.


## References

Verified against the publisher record (Crossref) or arXiv on 2026-11-12.

- Alikhanifard, P., Tsantalis, N. (2025). A novel refactoring and semantic aware abstract syntax tree differencing tool and a benchmark for evaluating the accuracy of diff tools. ACM Transactions on Software Engineering and Methodology 34(2), 1-63. doi:10.1145/3696002. arXiv:2403.05939.
- Bringmann, K., Gawrychowski, P., Mozes, S., Weimann, O. (2018). Tree edit distance cannot be computed in strongly subcubic time (unless APSP can). Proc. 29th ACM-SIAM Symposium on Discrete Algorithms (SODA), 1190-1206. doi:10.1137/1.9781611975031.77.
- Chawathe, S. S., Rajaraman, A., Garcia-Molina, H., Widom, J. (1996). Change detection in hierarchically structured information. Proc. ACM SIGMOD 1996, 493-504. doi:10.1145/233269.233366.
- Dotzler, G., Philippsen, M. (2016). Move-optimized source code tree differencing. Proc. 31st IEEE/ACM International Conference on Automated Software Engineering (ASE), 660-671. doi:10.1145/2970276.2970315.
- Erdweg, S., Szabó, T., Pacak, A. (2021). Concise, type-safe, and efficient structural diffing. Proc. 42nd ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI), 406-419. doi:10.1145/3453483.3454052.
- Falleri, J.-R., Morandat, F., Blanc, X., Martinez, M., Monperrus, M. (2014). Fine-grained and accurate source code differencing. Proc. 29th ACM/IEEE International Conference on Automated Software Engineering (ASE), 313-324. doi:10.1145/2642937.2642982.
- Falleri, J.-R., Martinez, M. (2024). Fine-grained, accurate and scalable source differencing. Proc. IEEE/ACM 46th International Conference on Software Engineering (ICSE), 1-12. doi:10.1145/3597503.3639148.
- Fan, Y., Xia, X., Lo, D., Hassan, A. E., Wang, Y., Li, S. (2021). A differential testing approach for evaluating abstract syntax tree mapping algorithms. Proc. 43rd IEEE/ACM International Conference on Software Engineering (ICSE), 1174-1185. doi:10.1109/ICSE43902.2021.00108. arXiv:2103.00141.
- Filliâtre, J.-C., Conchon, S. (2006). Type-safe modular hash-consing. Proc. 2006 Workshop on ML, 12-19. doi:10.1145/1159876.1159880.
- Fluri, B., Würsch, M., Pinzger, M., Gall, H. C. (2007). Change distilling: tree differencing for fine-grained source code change extraction. IEEE Transactions on Software Engineering 33(11), 725-743. doi:10.1109/TSE.2007.70731.
- Pawlik, M., Augsten, N. (2011). RTED: a robust algorithm for the tree edit distance. Proceedings of the VLDB Endowment 5(4), 334-345. doi:10.14778/2095686.2095692.
- Pawlik, M., Augsten, N. (2016). Tree edit distance: robust and memory-efficient. Information Systems 56, 157-173. doi:10.1016/j.is.2015.08.004.
- Selkow, S. M. (1977). The tree-to-tree editing problem. Information Processing Letters 6(6), 184-186. doi:10.1016/0020-0190(77)90064-3.
- Zhang, K., Shasha, D. (1989). Simple fast algorithms for the editing distance between trees and related problems. SIAM Journal on Computing 18(6), 1245-1262. doi:10.1137/0218082.

Software (not papers): OmniDiff, https://github.com/ivankovic/omnidiff, commit ee5ee5b43b39602ef68b6ebb30ddeeea5e843265 (crate version 0.4.0). GumTree 4.0.0-beta4, https://github.com/GumTreeDiff/gumtree (release archive, sha256 a9f94accb853c993f7b6497949ba9f91c2d1f7e20975b479333d9bf79deca3ea). tree-sitter 0.26.13 and grammar crates as pinned in `Cargo.lock`.
