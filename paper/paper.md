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
of the changed-span difference includes zero, the perfect-fixture difference does not. Parameters
were chosen on one half of the fixtures and the other half gives 0.964. The pipeline is faster than
OmniDiff in matching and, with the tree-sitter parse counted on both sides, the headline ratio is
given in Section 6.4. The refined mapping is a heuristic repair, not an optimum of any objective;
the certified part is only the top-down core.

## 1 Introduction

A diff consumer such as a reviewer, a selective-testing tool or an agent that watches a document
needs to know which old node *is* which new node. Edit-distance algorithms answer a different
question: they return a cheapest script under an operation set. For ordered trees the choice of
operation set fixes what a correspondence can say. General tree edit distance (Zhang and Shasha)
lets a deleted node promote its children and has a cubic-time algorithm family that is believed
optimal in the worst case; the *top-down* variant (Selkow) deletes whole subtrees and requires
matched parents, which makes it quadratic and amenable to pruning, but it reports a moved function
as one deletion plus one insertion.

This paper asks a narrow engineering question: **how much of the accuracy gap between an exact
top-down matcher and a tuned heuristic matcher can a small, bounded, cross-level repair pass
close, and at what cost in time?** Our answer, on one public corpus, is: most of it in changed-span
F1, less of it in per-fixture perfection, at a time cost that is a fraction of the top-down time
(Section 6.4).

**Contributions.**

1. A precise statement of the matching problem and of what the top-down objective cannot express
   (Section 2).
2. `difffold`: an exact-identity, certified top-down core (Section 3.1, 3.2) and a five-phase
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
shortest-paths conjecture fails (Bringmann et al.). The top-down objective avoids that barrier by
construction. We keep the top-down core exact and fast and repair its output.

## 3 The difffold algorithm

### 3.1 Exact identity (I1)

Nodes live in an arena. `Arena::mk(label, kids)` returns an id; two nodes of one arena have equal ids
if and only if their labels and child id lists are equal (hash consing; Filliâtre and Conchon).
The hash only selects a bucket; equality is checked on a hit, so the property does not depend on the
hash function. Equality of two subtrees is therefore an integer comparison, and the arena stores one
copy of each distinct subtree.

Cost: one pass over each tree, expected O(n + m) hash operations. A test that injects a constant
bucket function exists because an earlier version of the interner failed exactly in that case
(`tests/contracts.rs`).

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
`proof/`). The Rust code is not extracted or formally linked to that model; agreement of the code
with the model is tested against an independent oracle (`tests/`), not proved.

### 3.3 Cross-level refinement

The top-down result is converted into a correspondence on preorder indices and then repaired. All
phases act only on nodes that are still unmapped, except phase 2, which may replace a *tentative*
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
   aligner on the two subtrees and add its pairs where both nodes are unmapped and kind-compatible;
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
worst case (nested pairs); on the fixtures few pairs are made in phase 3 (Section 6.2). Phase 5 is
O(L·hops·(log m + k)) for L unmapped leaves and k same-label candidates inside the range. The worst
case for the refinement as a whole is therefore O((n + m)·d² + d·T) with T the top-down time, and
quadratic in the adversarial case of very many identical small subtrees. We do not have a better
worst-case bound; Section 6.4 reports the measured scaling.

### 3.4 Properties

For every input the refined result is (i) a partial bijection, (ii) kind-compatible on every pair,
(iii) deterministic (no hashing order or randomness reaches the output), and (iv) with all later phases
switched off, equal to the top-down mapping minus kind-changing internal pairs. These are tested
(`tests/refine.rs`) on hand-built moves, reorders, wraps and unwraps and on 60 random tree pairs. The
refined mapping is not a top-down mapping, not order-preserving and not an optimum of the top-down or
any other objective; it carries no certificate beyond (i) to (iv).

## 4 Related work

**Tree edit distance.** Selkow's top-down distance (Selkow 1977) and Zhang and Shasha's ordered tree
edit distance (Zhang and Shasha 1989) fix the two operation sets used here. RTED and APTED
(Pawlik and Augsten 2011, 2016) choose decompositions adaptively to speed up the general problem;
Bringmann et al. (2018) give a conditional cubic lower bound for it. `difffold` keeps a top-down
optimum as its core because it admits an admissible pruning bound.

**Change extraction and heuristic matching.** Chawathe et al. (1996) derive edit scripts from a
matching of hierarchical data; ChangeDistiller (Fluri et al. 2007) matches leaves by text similarity
and inner nodes bottom-up by shared leaves. GumTree (Falleri et al. 2014) matches the largest
isomorphic subtrees top-down by height and then inner nodes bottom-up by Dice similarity of mapped
descendants, followed by a recovery step; a later version makes the matching scalable (Falleri and
Martinez 2024). MTDiff (Dotzler and Philippsen 2016) optimises scripts for moves. The refinement
phases of `difffold` follow the same two-phase shape but start from an exact top-down mapping and use
O(1) subtree equality from hash consing; truediff (Erdweg et al. 2021) also identifies equal subtrees by (cryptographic) hashes, in a
different design: a linearly typed edit-script language, with a proof of linear run time for its
algorithm.

**Benchmarks.** Fan et al. (2021) test AST mapping algorithms differentially and report that a
nontrivial share of file revisions receive inaccurate mappings; Alikhanifard and Tsantalis (2025)
construct a benchmark of mapping ground truth from Defects4J and refactoring commits. OmniDiff, the
baseline here, is an open-source tree-sitter based structural diff tool distributed with
hand-authored node mappings; it has no accompanying paper that we know of, so we cite its repository
and commit. Its fixtures are the only ground truth used in this paper.

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
- **Timing.** Per stage (parse, intern, top-down, refine) the median, minimum and maximum over n = 10
  passes per fixture; then medians and quantiles over fixtures; ratios are per fixture.

### 5.3 Setup

<<SETUP>>

## 6 Results

<<RESULTS>>

## 7 Threats to validity and what was not run

<<THREATS>>

## 8 Reproducing

<<REPRO>>

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
