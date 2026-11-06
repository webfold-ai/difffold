# Why difffold's structural diff scores 66.7% perfect and OmniDiff 81.2%

Part 1 of the accuracy and ideas study. Part 2 is `IDEAS-FROM-SISTER-REPOS.md`.

Labels: **MEASURED** (run in this study, harness in `research/mechanics`), **FOUND-IN-REPO** (read in a repository,
path given), **INFERRED** (my reasoning, not run). Numbers are single runs on a shared 4-core VM; all are
counts of fixtures, so there is no timing noise in them.

## Summary

Two sets are used. **U** is the 951 scorable fixtures with at most 20,000 nodes (95% of the 1,001; the other 50 use the
top-down fallback in the published runs and are not covered by the engine). **S** is the 586 of them with at most 2,500 nodes, where every experiment ran.

1. **MEASURED. The headline gap is mostly a tie-breaking gap, not an objective gap.** On U the ground truth is itself a
   minimum-cost tree edit mapping under difffold's own cost model on **767 fixtures (80.7%)**; on S on 490 (83.6%). Exact TED can
   reach it there, but difffold's raw TED mapping is perfect on only 624 of the 767 (81.4%; on S 411 of 490, 83.9%) because the optimum is not unique and
   the traceback picks a different optimal mapping. On the other 184 fixtures of U it is perfect on 6 (on S: 2 of 96).
2. **MEASURED. Decomposition of the gap to OmniDiff.** On U: OmniDiff 781 perfect, difffold's raw TED mapping 630, a gap of 151 fixtures:
   87 (58%) are tie-breaking inside the optimal set, 26 (17%) are fixtures where the human mapping is a legal
   tree edit mapping but costs more than the minimum, 38 (25%) are fixtures where the human mapping is not a tree
   edit mapping at all (moves, reorders, N:M groups). On S the same split is 48, 17 and 19 of 84.
3. **MEASURED. Ceilings.** Choosing the best optimal mapping with the ground truth in hand: U 760 (79.9%), S 484 (82.6%); on S 464 (79.2%) if
   only pairs that difffold's traceback can emit are allowed; analytically the share of fixtures whose ground truth is optimal, U 80.7% and S 83.6%.
   A deterministic, ground-truth-free tie-break reaches 68.9% on U (from 66.2%) and 73.2% on S (from 70.5%) with one hand-written feature, 73.9% on S with a family-aware relabel on top,
   and **76.3% on S (two-fold cross-validated) with 11 fitted context features**. Changing the cost model within the families tried
   moves the oracle ceiling between 78.3% and 84.1% on S and never moves the default result by more than +1.2 points.
4. **MEASURED. Moves are not the main lever, but they grow with file size.** The ground truth is not a tree edit mapping on 8.9% of S and 12.0% of U (17.0% of the fixtures above 2,500 nodes). The existing identical-subtree
   move recovery adds 0.3 to 0.5 points on S and 1.0 point (10 fixtures) on the oracle in U. OmniDiff itself is perfect on 42 of the 114 such fixtures in U.
5. **MEASURED (S). The failures are small and mostly punctuation.** In the tie bucket (71 failing fixtures) 53 have at most two failing
   decisions and 50 fail only on anonymous tokens (`,`, `{`, keywords). The recurring example is a list element inserted with its trailing comma:
   two optimal mappings differ only in which `,` is called the new one. If anonymous tokens were not scored, difffold's raw mapping would be
   perfect on 81.6% of S instead of 70.5%.
6. **FOUND-IN-REPO. OmniDiff does not optimise the exact TED objective.** It is a pipeline of hash descent, name-keyed matching, exact APTED only
   inside already matched pairs, about two dozen further passes, and GumTree-style move recovery. Its own paper reports that the human mapping is strictly costlier than the cheapest
   one on 3.2% of fixtures and that "each of" its preference passes "can cost more than the cheapest mapping".

## 1. Method

### Harness
`research/mechanics` (its own crate, outside the root workspace; `cargo +1.89.0 build --release` there). It reuses the scorer's front end
copied from `src/bin/score_accuracy.rs` (tree-sitter parse, ground-truth loading, taxonomy, `evaluate`). A fixture is **perfect** when it has zero
visible mismatching decisions, exactly as in `results/accuracy/`. A decision is a ground-truth pair, delete, insert or group member.

The harness adds `wted.rs`, a banded Zhang-Shasha with arbitrary per-node costs, a lexicographic secondary cost packed in the low bits
(`primary * 2^36 + secondary`), a traceback, and a count of optimal mappings. The shift bound `|i - j| <= cap / m0` is the same argument
as in `src/ted.rs`.

### Validation (MEASURED)
- `cargo test` in `research/mechanics` checks value, number of optimal mappings, and mapping legality and cost against brute-force enumeration
  of every legal mapping on 300 random tree pairs (up to 6 nodes each, random pair costs including forbidden pairs and random secondary costs, so ties occur: more than 20 of the 300 have several optimal mappings).
- With difffold's cost model and default tie policy, the engine's number of failing decisions equals the library mapping's on **all 586** fixtures of S
  (2,216 failing decisions on both sides). So the engine reproduces `difffold::ted::ted_mapping` for scoring purposes.
- The harness reproduces the published accuracy rows: top-down 569/1001 (56.8%), TED with kinds 656 (65.5%), plus move recovery 663 (66.2%),
  plus orphan-update hygiene ("variant E") 668 (66.7%). The unmodified `score_accuracy` run gave 65.4% for plain TED, 65.5% with kinds and 66.7% for variant E on the same checkout.
  OmniDiff's per-fixture result is read from `results/accuracy/fixtures.csv` (813/1001 = 81.2%); OmniDiff was not rerun.

### Experiments
For each fixture the harness computes:
- `copt`, the minimum cost under difffold's model (kind-aware relabel 0, 1 within a kind, 2 across kinds; insert and delete 1).
- The **oracle tie-break**: among all mappings of cost `copt`, the one with the fewest failing decisions (visible failures weigh 2^17, invisible 1). It is exact for pair, delete and insert decisions; group
  decisions are modelled only approximately, so the oracle can under-report by the 9 "anomaly" fixtures below. "Oracle strict" allows only pairs difffold's traceback can emit (no cross-kind relabels).
- **Realisability of the ground truth**: whether the ground-truth pairs form a legal tree edit mapping (order and ancestry preserving, checked by `difffold::ted::check_mapping`), and if so its minimum cost (`gt_cost`) over all completions that keep every ground-truth decision.
  If not legal, the largest legal subset of the pairs (`gt_drop` is how many pairs must be given up).
- The **number of optimal mappings**, by a disjoint count recursion in the same DP (x deleted, or x mapped and y inserted, or x mapped to y).
- Alternative cost models and secondary (tie-break) costs, each with a default-tie run and an oracle run.

### Coverage
Engine arms run on S (586 fixtures with at most 2,500 nodes), because each arm is a full TED. The library arms (top-down, TED, D, E) run on all 1,001. A reduced set of arms (raw optimal mapping, oracle, root-path and depth tie-breaks, two cost-model oracles, legality of the ground truth) was
also run on the 365 fixtures with 2,500 to 20,000 nodes, which gives U. The 50 fixtures above 20,000 nodes are not covered (OmniDiff is perfect on 32 of them, variant E's top-down fallback on 26).
S is representative of the whole: difffold 71.2% against OmniDiff 84.8% on S, 67.5% against 82.1% on U, 66.7% against 81.2% overall, and the gap is present in every size bucket
(81.2% against 91.9% under 300 nodes; 57.1% against 72.6% from 10,000 to 20,000 nodes).

## 2. What OmniDiff optimises (FOUND-IN-REPO)

Sources are in the OmniDiff checkout (version 0.3.0): `src/diff.rs` (module comment), `src/diff/apted/common.rs`, `src/diff/nodes.rs`,
`research/papers/introductory-paper/main.tex`, `research/plots/variables.tex`, `research/data/quality/ground_truth_conflicts.md`, `research/data/quality/move_attribution.md`.

- **A pipeline, not a distance.** Passes in order: hash descent (identical subtrees, then same-shape subtrees), nested-condition collapse, leading siblings, syntax-aware matching
  (flat containers by Myers, qualified names, imports, greedy anchor blocks, with **APTED run only inside each matched pair**), residual passes (bottom-up propagation, unique-type matching,
  a Myers LCS fallback), **GumTree-style move recovery** for byte-identical, large-enough subtrees deleted on one side and inserted on the other, then three refine and re-tag passes
  (mutual ancestors, leaf-neighbour agreement, wrap growth), then delete or insert for whatever is left. The paper says of its preference passes: "each of them can cost more than the cheapest mapping".
- **Cost constants are all 1** (`COST_INSERT`, `COST_DELETE`, `COST_UPDATE`). The rename cost obeys a stated rule: below delete plus insert is a preference, at or above it is a prohibition.
  Cross-kind pairs are prohibited **except** identifier-like kinds with each other and kinds within a shared operator family (comparison, arithmetic, bitwise, logical, assignment, increment), per language.
  A leaf update across unpaired parents is checked against ancestor context (`update_context_supported`; its comment says a shared depth budget "separates a deep rename (3 levels before, 1 after: passes) from skeleton reuse that is deep on both sides").
- **The authors measured the same two mismatches this study finds.** RA1.2: of 1,217 fixtures with a human mapping the human cost equals the minimum under unit costs and a free move on 1,052, is strictly higher on 39 (3.2%), and so is lower on the remaining 126 (arithmetic from the counts, not a figure the paper states).
  The main reason they give is that humans treat groups of tokens as a unit (their example is matching the `return` keywords of an added and a deleted function). RA1.1: 12.2% of fixtures need an N:M mapping that no insert/delete/update/move script expresses.
- **The ground truth has unsettled conventions.** `ground_truth_conflicts.md` lists conventions answered both ways in the fixtures, for example whether a leaf of a replaced expression is renamed into new code or deleted and inserted
  (74 of 1,198 human `update` entries cross unpaired parents). `move_attribution.md` argues that a mapping does not say which of several equally faithful readings (one line moved past five, or five moved past one) is "the move".
- **Consequence for the comparison.** OmniDiff is neither exact TED nor a pure heuristic matcher, and it is tuned on this corpus (the ground truth is its authors' own). Its numbers are an in-sample upper end.

## 3. Where the ground truth sits relative to difffold's model (MEASURED, S)

| ground truth is | fixtures | share of S | difffold raw TED perfect | OmniDiff perfect |
|---|---|---|---|---|
| a legal tree edit mapping of minimum cost | 490 | 83.6% | 411 (83.9%) | 459 (93.7%) |
| a legal tree edit mapping, costlier than the minimum | 44 | 7.5% | 1 | 18 |
| not a tree edit mapping (moves, reorders, N:M) | 52 | 8.9% | 1 | 20 |

The same table on U (951 fixtures):

| ground truth is | fixtures | share of U | difffold raw TED perfect | OmniDiff perfect |
|---|---|---|---|---|
| a legal tree edit mapping of minimum cost | 767 | 80.7% | 624 (81.4%) | 711 (92.7%) |
| a legal tree edit mapping, costlier than the minimum | 70 | 7.4% | 2 | 28 |
| not a tree edit mapping (moves, reorders, N:M) | 114 | 12.0% | 4 | 42 |

For the 365 fixtures above 2,500 nodes alone the shares are 75.9%, 7.1% and 17.0%, and the raw mapping is perfect on 217 (59.5%) against OmniDiff 284 (77.8%) and the oracle 276 (75.6%).

For the 44, the excess cost `gt_cost - copt` has median 8 (quartiles 2 and 31, maximum 229 among the 43 that fail; on U median 8, quartiles 2 and 18, maximum 229). For the 52, the number of ground-truth pairs
that no legal mapping can contain has median 5 (75th percentile 9, maximum 94). OmniDiff's own count (section 2) puts the human-equals-minimum share at 86.4% (1,052 of 1,217) under a free move; the 83.6% here is the share under no move operation, on a smaller and differently sampled set of fixtures. They are the same kind of quantity and similar in size; I did not reconcile them fixture by fixture.

### Failing fixtures by mechanism (raw TED mapping fails; 173 of 586 on S)

On U (321 failing of 951): TIE 130 (40.5%), EXPRESSIVENESS 109 (34.0%), OBJECTIVE 68 (21.2%), ANOMALY 14 (4.4%). The table below is S, where the decision counts were collected.

| mechanism | fixtures | share | failing decisions | share of decisions |
|---|---|---|---|---|
| **TIE**: some optimal mapping is perfect | 71 | 41.0% | 216 | 9.7% |
| **OBJECTIVE**: ground truth legal but costlier than optimum | 43 | 24.9% | 1,231 | 55.6% |
| **EXPRESSIVENESS**: ground truth is not a tree edit mapping | 50 | 28.9% | 680 | 30.7% |
| **ANOMALY**: ground truth legal and optimal, but my oracle is not perfect (group decisions) | 9 | 5.2% | 89 | 4.0% |

Fixture counts and decision counts point in opposite directions: ties are the most numerous failures but cost few decisions each (3 on average), the objective bucket is a quarter of the fixtures but over half of the failed decisions.
The 9 anomalies all fail on `repeated_children` decisions (N:M groups), where my penalty model is approximate; for them the ground truth is optimal, so a perfect optimal mapping exists and they belong to the tie ceiling.

### Number of optimal mappings (MEASURED)
| | fixtures | unique optimum | median optimal mappings | 90th percentile |
|---|---|---|---|---|
| raw TED perfect | 413 | 81% | 1 | 3 |
| raw TED failing | 173 | 14% | 4 | about 2,900 |
| of which TIE bucket | 71 | 0% | 3 | up to 15,600 |

Of the 71 tie fixtures, 29 have exactly two optimal mappings and 45 have at most four. The 24 failing fixtures with a unique optimum are 19 expressiveness, 4 objective and 1 anomaly: none is a tie fixture, which is the consistency check the count has to pass. 77 of the 413 passing fixtures also have more than one optimal mapping (the traceback picked a good one).

## 4. The mechanisms with examples

### 4.1 Tie-breaking (hypothesis b): confirmed, and it is the largest lever
The recurring minimal case is a list element inserted together with its comma. `handmade/rust-add-value-to-enum` adds `InlinedByteJ,` at the end of an enum body; `stratified/java-genymobile-scrcpy-add-enum-value` adds `AUDIO,`.
Every `,` has the same label, so shifting which comma is "the new one" costs the same. The ground truth keeps each comma with the element before it. The raw mapping fails exactly one decision (a `,` pair) in each. 
`stratified/java-genymobile-scrcpy-only-insert` is the same with a `{`. In the 71 tie fixtures: 50 fail only on anonymous tokens, 53 on at most two decisions.

What the secondary costs buy (S, perfect fixtures; baseline 413 = 70.5%):

| tie-break (secondary cost on a pair) | perfect | with move recovery |
|---|---|---|
| none (library default, prefers matching) | 413 (70.5%) | 415 (70.8%) |
| parent kind differs | 414 (70.6%) | 416 |
| siblings' identities differ (previous and next sibling subtree) | 400 (68.3%) | 402 |
| depth difference | 428 (73.0%) | 430 (73.4%) |
| sibling index difference | 423 (72.2%) | 425 |
| parent kind and sibling index | 426 (72.7%) | 428 |
| root path differs | 429 (73.2%) | 431 (73.5%) |
| root path plus sibling identities | 428 (73.0%) | 430 |
| **family-aware relabel plus root path** | 433 (73.9%) | |
| **11 weighted features, fitted, two-fold cross-validated** | **447 (76.3%)** | 449 (76.6%) |
| oracle, library-emittable pairs only | 464 (79.2%) | 466 |
| oracle, any optimal mapping | 484 (82.6%) | 487 (83.1%) |
| ground truth is an optimal mapping (analytic) | 490 (83.6%) | |

The fitted row is a structured perceptron trained on one half of S (fixtures whose oracle is perfect) and tested on the other half, both ways. The features are mismatch indicators: parent kind, grandparent kind, root path, previous-sibling and next-sibling subtree identity, depth difference, sibling index
difference, parent subtree identity, subtree size difference, anonymous-token-with-different-path, label difference. Learned weights are small (0 to 3 quarter units of the primary cost), which is why they
act only as tie-breaks. Both halves learned similar weights (depth difference, sibling index difference, previous-sibling identity and parent-subtree identity carry most). Two folds on one corpus is a weak validation: see section 7.

### 4.2 Objective (hypotheses a and c): real, about a fifth of the gap, and not fixed by the cost-model families tried
A minimum-cost mapping rewards matching cheap shared skeleton tokens of unrelated statements, which the human mapping calls delete plus insert.
- `stratified/rust-zed-industries-zed-change-mods` (excess 1): `#![cfg(not(target_os = "windows"))]` becomes `mod cosmic_text_system;`. The optimum relabels the identifier `target_os` into `cosmic_text_system` (cost 1); the ground truth deletes and inserts (cost 2). This is the "stray rename" convention that OmniDiff's own conflicts file lists as unsettled.
- `stratified/c-ollama-ollama-change-imports` (excess 8): the optimum maps `#include` directives of different headers onto each other; the human deletes and inserts whole directives.
- `java-defects4j-cli-1-commandline` (excess 118): replaced `import` lines are mapped statement-for-statement with identifier relabels, saving the scaffolding nodes `java . util . ;` per import at cost 1 each.
- `stratified/tsx-langflow-ai-langflow-split-import-3` (excess 2): the human matches `React` across a restructured import, which costs 2 more than the optimum.

By class (raw TED, failing visible decisions on S): `sibling_ins_del` has 715, of which 554 (77%) are in the objective bucket. This is the class where the model rewards spurious matches.

Cost-model families (S, perfect fixtures with the library's default tie / with an oracle tie-break):

| cost model | default tie | oracle tie |
|---|---|---|
| kinds: relabel 0 / 1 same kind / 2 other (difffold) | 413 (70.5%) | 484 (82.6%) |
| unit: any differing label 1 (the plain TED run) | 406 (69.3%) | 459 (78.3%) |
| no relabel (every relabel costs delete plus insert) | 289 (49.3%) | 490 (83.6%) |
| internal nodes cheaper than leaves | 411 (70.1%) | 481 (82.1%) |
| internal nodes dearer than leaves | 413 (70.5%) | 484 (82.6%) |
| anonymous tokens cheaper | 413 (70.5%) | 484 (82.6%) |
| context: +1 if parent kind differs | 417 (71.2%) | 488 (83.3%) |
| context: +2 (prohibit) if parent kind differs | 400 (68.3%) | 493 (84.1%) |
| context: +1 if root path differs | 420 (71.7%) | 472 (80.5%) |
| context: +2 (prohibit) if root path differs | 349 (59.6%) | 478 (81.6%) |
| family-aware: cost-1 updates among identifier-like kinds and within operator families (OmniDiff's rule) | 417 (71.2%) | 481 (82.1%) |

Reading: no per-pair cost model changes the default result by more than +1.2 points (`context: +1 root path`), several make it much worse, and the oracle ceilings sit between 78% and 84%. The union over all eleven oracles is 502 (85.7%), a little above
OmniDiff's 84.8%. The objective-bucket fixtures need a cost that depends on whether the parent statements correspond, which a per-pair cost cannot express; the orphan-update hygiene step of variant E is a post-hoc version of it (it gained 1.2 points on all 1,001).

### 4.3 Expressiveness (hypothesis c, "no move operation"): real but small and hard
52 fixtures (8.9% of S) have ground truth that is not a tree edit mapping; difffold's raw mapping fails 51 of them (50 land in the expressiveness bucket, one has an oracle-perfect optimal mapping because of how groups are scored). Failing decisions by class in this bucket: all 90 `reorder` and all 55 `cross_parent_move` decisions, plus 235 of 466 `wrap_unwrap` decisions.
- `stratified/c-neovim-neovim-small-change` moves two `extern` declarations below an include and prefixes them with `DLLEXPORT`; the human also updates `type_identifier` to `identifier`, a cross-kind update that difffold prices as delete plus insert.
- `small/javascript-typescript-interesting-small-edit-refactor` rewrites `var _a = [0, undefined], a = _a[0], b = _a[1];` into `var [a, b] = [0, undefined];`, a wrap/unwrap with a duplicated source.
- `handmade/typescript-async-await` wraps a callback into a promise and `async` arrow.

Move recovery of identical dead subtrees (the harness runs the same `recover_moves` as variant D) adds 2 fixtures on the raw mapping and 3 on the oracle. A perfect move operator is bounded by 83.6% plus at most 8.9% (92.5%) on S, which is a bound of what could be reached, not something shown; OmniDiff, which has move recovery and other passes, is perfect on 20 of the 52.

### 4.4 Preprocessing and representation (hypothesis d): mostly scoring granularity, not tree construction
- Node counts of difffold's tree-sitter tree equal OmniDiff's on all 1,001 fixtures (`results/accuracy/HEAD-TO-HEAD.md`, 0 mismatches), so the node set is not the problem.
- The internal-node label is its kind only and a leaf's label includes its text; neither blocks the ground truth (the GT-optimal share is 83.6% under this representation).
- Anonymous tokens are visible nodes in the scorer (`is_visible` is true for every leaf), so each ambiguous `,` or `;` can fail a fixture. Counting only named nodes: raw TED 478 (81.6%), variant E 483 (82.4%), oracle 500 (85.3%) of S, against 413, 417, 484. Nearly all of this 11-point difference is the tie bucket
  (65 failing fixtures fail only on anonymous tokens; the oracle repairs 50 of them). OmniDiff's own named-only number was not computed.

### 4.5 The five failure classes, one line each (S, raw TED; failing visible decisions by bucket tie / objective / expressiveness)
| class | decisions | tie | anomaly | objective | expressiveness | reading |
|---|---|---|---|---|---|---|
| local_edit | 35 | 25 | 0 | 4 | 6 | tie: which leaf is the update |
| sibling_ins_del | 715 | 58 | 8 | 554 | 95 | spurious skeleton matches (objective) |
| repeated_children | 404 | 26 | 70 | 245 | 63 | N:M groups and repeated siblings |
| reorder | 90 | 0 | 0 | 0 | 90 | needs a reorder operation |
| cross_parent_move | 55 | 0 | 0 | 0 | 55 | needs a move operation |
| wrap_unwrap | 466 | 48 | 8 | 175 | 235 | half expressible by TED, half not |
| wholesale_rewrite | 106 | 0 | 0 | 106 | 0 | one fixture |
| context | 345 | 59 | 3 | 147 | 136 | collateral damage in the failing fixtures |

Concrete fixtures (names are `dataset/fixture`): reorder, `stratified/c-genymobile-scrcpy-add-to-import-path-and-move-imports-around`, `stratified/tsx-mui-material-ui-move-import`, `stratified/go-grafana-grafana-real-small-change-with-a-move`;
cross-parent move, `handmade/typescript-async-await`, `handmade/rust-hash-optimization`, `small/go-lazygit-switch-to-strings`; wrap/unwrap, `small/javascript-typescript-interesting-small-edit-refactor`, `defects4j/java-defects4j-cli-12-gnuparser`;
sibling insert and its context damage as a tie, `stratified/java-genymobile-scrcpy-only-insert`, `stratified/tsx-mui-material-ui-add-to-empty-block`; sibling insert and delete as an objective mismatch, `defects4j/java-defects4j-cli-1-commandline`, `stratified/c-ollama-ollama-change-imports`.

On all 1,001 fixtures with variant E (6,285 failing visible decisions): wrap_unwrap 31%, sibling_ins_del 25%, context 16%, repeated_children 13%, reorder 7%, cross_parent_move 3%, local_edit 2%, rewrite 2%. The earlier finding that 75% of the gap was wrap/unwrap (`results/accuracy/HEAD-TO-HEAD.md`) was
against the top-down objective, which cannot express a wrap at all; with the general TED mapping wrap/unwrap is the largest single class by decisions but, as the table shows, only half of it is outside the TED model.

## 5. Ceilings (S = 586 fixtures; OmniDiff 497 = 84.8%)

| hypothesis and change | perfect | ceiling or achieved | how known |
|---|---|---|---|
| current: raw optimal mapping | 413 (70.5%) | achieved | MEASURED |
| current best published: variant E | 417 (71.2%) | achieved | MEASURED |
| (b) deterministic tie-break, one feature (root path) | 429 (73.2%) | achievable now | MEASURED |
| (b) plus family-aware relabel | 433 (73.9%) | achievable now | MEASURED |
| (b) fitted 11-feature tie-break, two-fold cross-validated | 447 (76.3%) | achievable, validation weak | MEASURED |
| (b) oracle, library-emittable pairs | 464 (79.2%) | ceiling for tie-breaking with difffold's traceback pairs | MEASURED |
| (b) oracle, any optimal mapping | 484 (82.6%) | ceiling for tie-breaking, approximate on groups | MEASURED |
| (b) ground truth optimal | 490 (83.6%) | analytic ceiling for tie-breaking | MEASURED |
| (c) cost-model alternatives, best default result | 420 (71.7%) | +1.2 over baseline | MEASURED |
| (c) cost-model alternatives, union of oracles | 502 (85.7%) | ceiling if the cost model were free to differ per fixture | MEASURED |
| (c) move operation, identical dead subtrees | +2 to +3 fixtures | achieved | MEASURED |
| (c) move operation, perfect | up to 92.5% | bound only | INFERRED |
| (d) score named nodes only | 478 (81.6%) | scoring change, not an algorithm change | MEASURED |

The same ceilings on U (951 fixtures; OmniDiff 781 = 82.1%; only the arms that were run on the large fixtures):

| change | perfect | how known |
|---|---|---|
| current: raw optimal mapping | 630 (66.2%) | MEASURED |
| current best published: variant E | 642 (67.5%) | MEASURED |
| deterministic tie-break, root path | 655 (68.9%) | MEASURED |
| deterministic tie-break, depth difference | 654 (68.8%) | MEASURED |
| oracle tie-break, any optimal mapping | 760 (79.9%) | MEASURED |
| oracle tie-break plus identical-subtree move recovery | 770 (81.0%) | MEASURED |
| ground truth is an optimal mapping (analytic ceiling) | 767 (80.7%) | MEASURED |
| oracle under the no-relabel or the prohibit-on-parent-kind cost model | 776 of 950 (81.7%) | MEASURED |

The realistic target with only tie-breaking is about 76 to 79% on S; with a ground-truth-free rule that is as good as the oracle it would be 82.6% and would put difffold within 2.2 points of OmniDiff on S without any move operation.

## 6. Recommendations, ranked by expected accuracy gain per unit effort

1. **Contextual tie-break as a secondary cost (+2.7 to +3.4 points now, up to +5.8 fitted).** Add the root-path mismatch (and depth) as a low-order term in `relabel_cost`, packed so it never changes the primary distance. Effort low for the hand rule (73.2 to 73.9%), medium for fitted weights and the wider cell type. Gate: distance identical to the current engine on the 237 real pairs and 4,000 random pairs.
2. **Learn the weights, with a proper held-out set (up to 76.3% already, ceiling 82.6%).** The 11 features already carry most of the signal; adding neighbour-aware features that depend on the mapping of neighbours (token ownership: a comma follows the element it belongs to) needs a two-pass or column-wise tie-break and is where the remaining 6 points are. Effort medium to high.
3. **Family-aware relabel (+0.7 points, +0.7 on top of the path tie-break).** OmniDiff's own rule. Effort low (a table of kinds). The oracle uses more cross-kind relabels than any family rule covers (3.4 points separate the two oracles), so the realistic gain is the measured 0.7.
4. **Context-dependent update validation, i.e. generalise variant E's hygiene (small, uncertain).** The objective bucket (7.5% of S, 17 fixtures OmniDiff wins) needs "an update across unpaired parents is a delete plus insert". Variant E gained 1.2 points of the whole corpus doing this after the fact. Doing it inside the DP needs parent-pair-aware costs, which breaks the per-pair cost structure. Effort high, gain at most about 3 points.
5. **Near-identical move recovery (at most 1 point).** Only if items 1 to 3 are done; the expressiveness bucket is 8.9% of S and OmniDiff gets less than half of it. See Part 2, idea 6.
6. **Do not**: switch to unit relabel (-1.2), forbid relabels (-21), or forbid cross-context matches of equal labels by cost (-10.9 for root path): all measured worse with the default tie policy.

## 7. What I could not determine, and caveats

- **Larger fixtures.** The full set of arms covers S only; fixtures of 2,500 to 20,000 nodes have the reduced set, and the 50 fixtures above 20,000 nodes have none. The fitted tie-break, the family-aware relabel, the neighbour tie-breaks and the per-class decision counts are S only.
  The shares move with size (expressiveness grows from 8.9% to 17.0%), so the S-only percentages of tie-break gain probably overstate what applies to the largest files.
- **OmniDiff was not rerun.** Its per-fixture results come from `results/accuracy/fixtures.csv`; its named-only number and its own tie behaviour are not measured, so "OmniDiff breaks ties better" is inferred from its being perfect on 459 of the 490 GT-optimal fixtures where difffold gets 411, not observed.
- **The oracle is exact only for pair, insert and delete decisions.** Group (N:M) decisions are modelled approximately; the 9 anomaly fixtures show the size of the error (1.5 points of S at most, in the conservative direction).
- **Two-fold cross-validation on one corpus** that is OmniDiff's in-sample ground truth. The fitted 76.3% may not transfer; the hand rules are less exposed. No held-out corpus exists in the repository.
- **Why OmniDiff is perfect on 59 of the 71 tie fixtures** was not traced pass by pass; I did not instrument its pipeline.
- **The 20,000-node cutoff** excludes the 50 largest fixtures, where the expressiveness bucket is probably larger still.
- **Cost-model families** were chosen by me; I did not search for a better per-pair cost, and the "per-pair costs cannot express parent correspondence" argument is a structural argument, not a proof that no such family helps.
- Group decisions, invisible nodes (weight 1) and `wholesale_rewrite` fixtures (2 in S) are scored as the scorer scores them.

## 8. Reproduce
```
cd research/mechanics
cargo +1.89.0 test --release                       # engine against brute force
cargo +1.89.0 build --release
target/release/mechanics <omnidiff>/src/test/data/diffs out.csv 2500 3        # all arms, fixtures up to 2500 nodes
MECH_ARMS=fam:none,fam:path,neigh,oraclestrict MECH_SKIPLIB=1 target/release/mechanics <diffs> out2.csv 2500 3
MECH_DUMP=1 target/release/mechanics <diffs> out.csv 0 1 <fixture-name>       # show the first mismatched decisions
target/release/mechanics learn <diffs> 2500 3 12                               # fitted tie-break, two-fold cross-validation
```
The per-fixture CSVs behind the tables are in `results/mechanics/`: `arms-s.csv` (all arms, S), `arms-neigh-strict.csv` and `arms-family.csv` (the later arms, S),
`arms-big.csv` (reduced arms, 2,500 to 20,000 nodes), `learned-cv.txt` and `learned-training-log.txt` (the fitted tie-break).
