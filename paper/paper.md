# Correspondence, Not Distance: History, Limits and a Certified Tree Differ

Draft 0.2. Status: **in progress**. Sections marked `PENDING` wait on runs that have not finished;
nothing in them is a result. Claim tags follow `drafts/PAPER_STYLE.md`:
**[M]** measured by a named run, **[F]** formal (mechanised, or a stated identity), **[I]** implemented
but not benchmarked, **[H]** hypothesis with a falsification condition, **[D]** design.
A dagger (†) marks a source taken from the project's research notes and not re-read for this draft.

## Abstract

A diff is usually treated as a distance: the cheapest edit script between two snapshots. For the
systems that now consume diffs (code review, selective testing, web monitors, browser and crawler
agents), the useful object is a **correspondence**: which parts of the old observation represent the
same thing as which parts of the new one, what changed, and what evidence supports that claim. The
two are not the same, and neither is the true edit history, which two snapshots may not determine.
We trace how the meaning of "difference" moved from edited characters to matched lines, to moved
syntax, to maintained histories, and state the limits that any design must respect: identifiability,
the cost of reading input and writing output, conditional hardness, and memory traffic. We then
describe `difffold`, an exact solver for an explicitly restricted objective (top-down ordered-tree
edit distance) built on a hash-consed arena whose identity is exact by construction, a threshold
dynamic program that accepts a result only when an admissible bound certifies it, and a replay
contract enforced on every script. On 997 Java, Go and C fixtures from the OmniDiff corpus, its
intern-plus-diff time totals 1.24 s against 16.7 s for OmniDiff's recorded diff time, with p99
4.3 ms against 126.7 ms **[M]**. The objectives differ, so this compares cost, not quality; accuracy
against hand-authored ground truth is not yet measured. The pruning bound, the threshold decision
and the minimality of the result are mechanised in Lean over a model of the objective, with no
`sorry` and only the standard axioms; the Rust code is not extracted or linked to those proofs
**[F, model only]**. We propose, as design and not result, a provenance-carrying version DAG that separates
content, occurrence and version identity, keeps historical, optimal and presented deltas distinct,
and reserves exact inference for regions where history is missing.

## 1 Introduction

Given two observations of a document, three different questions share the word "diff":

1. **Historical.** What edits did the author or the system actually perform?
2. **Optimal.** What is the cheapest transformation under a stated operation set and cost model?
3. **Presented.** What explanation is most useful to a person or an agent?

A pair of snapshots can support several histories with the same cheapest script, and a short script
can misdescribe the transformation (arXiv:2403.05939†). Identifying which question a tool answers
is therefore part of evaluating it. We use **correspondence** as the unifying concept: the relation
between old and new parts that persisted, with the evidence for it.

Four stages are kept apart throughout: **representation** (raw bytes, parsed DOM, accessibility tree,
extracted blocks, typed records), **correspondence** (which old node is which new node),
**edit classification** (insert, delete, update, move, split, merge), and **consumption**
(highlighting, index invalidation, agent state). A "better algorithm" can be a better parser or a
better formatter. We therefore run an algorithm-controlled comparison (same representation and cost
model, different matchers) apart from an end-to-end comparison (each tool's own pipeline).

**Contributions.**

1. A historical and conceptual account of diffing as correspondence, with a table of what each
   lineage solved and left open (Section 2). [survey; sources in the references]
2. A statement of the limits on any design (Section 3).
3. An exact solver for the top-down objective with exact identity, a certified threshold DP and a
   replay contract, and a same-objective ablation and boundary-test plan (Section 5). [I] [M partial]
4. Measured cost against OmniDiff on a shared fixture corpus, with the comparison's limits stated
   (Section 8). [M]
5. A design for maintained provenance that makes repeated inference unnecessary where history is
   known (Section 6). [D] [H]

## 2 History and landscape

The story is not that diff algorithms got faster. It is that researchers repeatedly changed what a
difference means.

### 2.1 Sequences: define an objective, then solve it

Levenshtein (1966) defined edit distance over insertions, deletions and substitutions. Wagner and
Fischer (1974) gave the dynamic program, with time proportional to the product of the lengths.
Hirschberg (1975) reconstructed a longest common subsequence in quadratic time and linear space by
running a forward and a reverse pass and meeting in the middle. The achievement was a minimum-cost
explanation under a stated operation set, not recovery of the actual edits. The distinction

```text
actual editing history   !=   minimum-cost transformation   !=   best explanation
```

survives every later generation.

Unix `diff` appeared in the early 1970s and in Fifth Edition Unix in 1974†. Hunt and McIlroy (1976)
and Hunt and Szymanski (1977) made line comparison practical by exploiting matching positions
instead of filling the whole matrix. The lesson reused in this paper is that equality should be made
cheap first, and then computation spent deciding how equal pieces correspond. Repeated lines
(braces, blank lines, duplicated records) limit this: cheap equality does not make alignment
unambiguous.

Ukkonen (1985) made the work depend on the distance rather than always filling the matrix. Myers
(1986) viewed the problem as a shortest path through edit-cost frontiers and skipped runs of
matches, giving O(ND) for insertion and deletion distance D. Myers (1999) then packed DP state into
machine words. Wavefront alignment (Marco-Sola et al. 2021) advances score-ordered frontiers for
gap-affine costs, and its bidirectional form (Marco-Sola et al. 2023) reconstructs an optimal
alignment in working memory proportional to the alignment cost. Git exposes myers, minimal, patience
and histogram; they are strategies with different trade-offs, not a progression. Minimum edit count
does not determine a useful display: repeated lines admit several equally cheap alignments, so tie
breaking and temporal stability must be measured apart from cost.

### 2.2 Trees: structure helps and changes the problem

Selkow (1977) defined the top-down distance, in which a node can be matched only if its parent is.
Tai (1979) gave the first polynomial algorithm for the unrestricted ordered-tree model, and Zhang
and Shasha (1989) the practical reference algorithm. The detail that separates the two models is the
meaning of deleting a node. In classical tree edit distance, deletion **promotes the node's children
into its parent**, which is how a disappearing wrapper keeps its contents. In the top-down model a
deleted node takes its subtree with it, and matched pairs need matched parents. The second model is
cheaper and cannot align across levels. A wrapper insertion that disrupts every descendant
alignment is therefore a consequence of the objective, not an implementation bug. It also means
Zhang-Shasha and APTED are not objective-matched baselines for a top-down solver.

Demaine, Mozes, Rossman and Weimann (2009) gave an optimal decomposition algorithm for tree edit
distance. RTED (Pawlik and Augsten 2011) and APTED (2016) made the choice of decomposition strategy
the optimisation target, aiming at robust time and memory across tree shapes. Their optimality claim
concerns a stated class of strategies, not semantic correspondence. The consequence worth testing is
that the strategy should depend on the tree's shape, repetition and expected edit cost.

### 2.3 Domain knowledge and moves: infer intent

Chawathe, Rajaraman, Garcia-Molina and Widom (1996) treated hierarchical change detection for
databases, documents and version management, and exploited properties of the data to beat a general
method. That is a recurring result worth stating plainly: **a more informative domain model can
outperform a more sophisticated generic algorithm.** ChangeDistiller (Fluri et al. 2007), GumTree
(Falleri et al. 2014), MTDiff (Dotzler and Philippsen 2016) and RefactoringMiner's later AST-diff
work target readable, move-aware source changes, and a 2025 retrospective† reports higher
statement-level precision and recall for RefactoringMiner 3.0 in the evaluated comparison. What this
lineage did not remove: ambiguous matches between duplicated code, one-to-many and many-to-one
correspondence, cross-file transformations, and mappings that produce short scripts and still
misstate the change.

The identical-first counterexample belongs here. Locally obvious equal pairs can obstruct a better
global alignment (Section 5.3 and a pinned test). Equality is evidence and a basis for reuse; it is
not a mandatory anchor.

### 2.4 Avoid rediscovering changes

rsync (Tridgell and Mackerras 1996) minimises transferred bytes with rolling and strong checksums,
and also network round trips (one) and CPU; it does not optimise edit count or readability, so the
best diff depends on the resource minimised.

Incremental computation retains dependencies and repairs results rather than recomputing. The two
families should not be run together. Self-adjusting computation (Acar) is eager and totally ordered.
Adapton (Hammer et al. 2014) exists to differ from it: it stores **no change objects**, dirties
dependency edges eagerly, and on demand compares a value with the label on the edge to cut off
recomputation early when the input is unchanged. So "snapshot comparison infers what changed,
incremental maintenance preserves it" is too clean: Adapton avoids work by early cutoff on equal
values, not by recording edits. The lesson for derived data (Section 6.1) is the edge label, not an
edit log.

Large source-control systems move repeated repository knowledge into a service. Anthropic's report†
on its in-house system, Scion, describes server-side changesets, content-addressed storage and
recursively maintained derived data. It credits Piper and Sapling in the main text and Meta's Mononoke
and Bonsai in a footnote, states that it is not a general Git replacement, and reports a roughly
200 times smaller CPU and memory footprint. That figure compares the whole Scion fleet with the
earlier Git-mirror fleet, is self-reported, and gives no method or period; it is not a per-query or
per-diff result and must not be quoted as a faster diff. Scion stores changes against the first
parent only, by design, and infers copies and moves afterwards from a derived index. Only Bonsai
records copy-from edges explicitly. A press report† (dated 2026-03-11, via another outlet) that OpenAI
was "reportedly developing" a GitHub alternative says nothing about its design and was unconfirmed
by OpenAI; it is evidence of pressure on developer platforms and not of a diff method.

### 2.5 Negative results shape the search

Backurs and Indyk (2015) showed that a strongly subquadratic exact string edit distance would
contradict SETH. Bringmann, Gawrychowski, Mozes and Weimann (2018) connected a strongly subcubic
algorithm for unrestricted ordered-tree edit distance to a breakthrough for all-pairs shortest
paths. Both are conditional. They redirected effort towards small distance, restricted inputs,
approximation, dynamic maintenance and preprocessing. Whether the top-down objective inherits a
barrier is **open**; it is a restricted recurrence and must be analysed as one.

### 2.6 The lineages side by side

| lineage | what changed about "difference" | solved | left open | bearing on difffold |
|---|---|---|---|---|
| Edit distance, DP | a minimum-cost explanation | exact objective, memory (Hirschberg) | no notion of intent or identity | oracle, replay |
| Unix diff, LCS | matching lines | practical files | repeated material | cheap equality first |
| Distance-sensitive (Ukkonen, Myers, WFA) | work follows the distance | O(ND), frontier methods | high-distance rewrites | threshold schedule |
| Tree edit distance | structure counts | polynomial exact models | cubic-class cost, shape sensitivity | objective definition |
| Decomposition (RTED, APTED) | strategy follows shape | robust time and memory | not semantic quality | shape-aware dispatch |
| Move-aware heuristics | moves and intent | readable code diffs | ambiguity, multi-mapping | recovery, evaluation design |
| Domain models | data properties help | beats generic methods | needs the right model | identity-aware matching |
| Transfer and incremental | cost to consume the change | bytes sent, recomputation | external state not owned | maintained history |

### 2.7 Recurring failure modes of claims

| attractive claim | why it is insufficient |
|---|---|
| minimum script = true history | several histories give the same snapshots |
| equal subtree = correct anchor | equality does not establish occurrence correspondence |
| better parser = semantic equivalence | syntax alone does not establish behaviour |
| constant-time diff handle = constant-time computation | work moved to ingestion, maintenance or later materialisation |
| more general objective = better product | extra search can cost more than its accuracy gain |

## 3 The limits of the problem

These are the constraints a design has to respect. They are statements about the problem and the
machine, not about difffold.

**3.1 Identifiability.** Two snapshots do not in general determine the history that produced them.
Swapping two identical cards, or deleting one card and inserting an identical one, are
indistinguishable in the final states. No algorithm can recover identity that the inputs do not
contain, so a benchmark must mark such cases as ambiguous and a matcher must be allowed to abstain.
[F as a logical remark; no theorem is claimed]

**3.2 Reading input and writing output.** A procedure that must distinguish "equal" from "differs
at the last position" has to examine every position unless it is handed a trusted summary or prior
preprocessing. Producing k explicit edits costs at least k. Any constant-time claim is therefore a
claim about maintained state or handles, never about explicit fresh inputs.

**3.3 Conditional hardness.** Section 2.5 applies to the general string and tree problems and does
not automatically apply to restricted recurrences. The honest statement for the top-down objective
is that its cost has not been shown to be intrinsically cubic, and that this paper's results are
about an implementation on corpora, not about worst-case complexity.

**3.4 Memory traffic.** On real hardware the cost of a table is the number of memory blocks touched,
not the number of operations. Within apeiron's model of memory, a lookup that confirms by comparing
a fixed-width coordinate touches strictly fewer blocks than one that reads the stored key (the
`CoordinateReadout` file, about the substrate's own cost model, not about this implementation). We
use the principle as a design guide for what the interner and memo store: fixed-width ids and exact
64-bit pair keys.

**3.5 What each proposed cost claim must state.** Every claim that something is cheap, constant or
free must answer six questions.

| question | required answer |
|---|---|
| what is preprocessed? | inputs, versions, pair results, or all of them |
| where is the work paid? | ingestion, mutation, background processing or query |
| what is returned? | boolean, handle, distance, script or expanded output |
| which identities are trusted? | canonical content, observed occurrence or inferred correspondence |
| what is exact? | equality, replay, history or optimality under a named objective |
| what grows? | stored history, cache, boundary state, processors or output |

Parallel results state their work separately: constant parallel time with O(n^e) work on a CRCW PRAM
(a recent dynamic-string result, arXiv:2604.12696†, which the reading found to be about longest common extension of a dynamic string and not a diff result) is not constant sequential work.

## 4 Impact and use cases

The consumer determines which correspondence property matters and what a wrong answer costs.

| use | property that matters | cost of a wrong answer | tier of Section 6 that serves it |
|---|---|---|---|
| code review | readable, move-aware mapping | misread intent, missed regression | optimal plus presented delta |
| merge and rebase | stable occurrence identity | silent mis-merge | historical delta where recorded |
| selective testing and CI | which targets are affected | skipped test or wasted run | dependency invalidation, not text diff |
| changelogs, supply-chain review | what behaviourally changed | missed malicious change | presented delta with provenance |
| web and crawl monitoring | same entity, noise suppressed, acquisition failure vs removal | false deletion, alert fatigue | optimal delta with abstention |
| agent action preconditions | the state an action depends on changed | stale action accepted | relevant-state revalidation |
| index and answer invalidation | which chunks and records are stale | stale retrieval, wasted re-indexing | dependency graph on deltas |
| config, document, data sync | transferred bytes or applied patch | divergence | transfer delta, not semantic delta |
| versioned object storage with concurrent writers | exact-byte patches, convergence, a published ref that never points at a partial state | silent divergence, lost edits | Sections 6.7 to 6.11 |

For web monitoring four things must stay distinct: discovery of new pages, freshness of observation,
change in a known page, and entity correspondence. What the two vendors document (snapshots of their
documentation taken 2026-11-03†):

- Exa exposes a freshness control, `maxAgeHours`, from -1 to 720, and marks each result's source as
  cached or crawled. The reading found no observed-at timestamp.
- Firecrawl's entity identity is the exact URL. Its JSON comparison is LLM extraction (documented at
  5 credits per page). In crawl monitors, "removed" means "no longer discovered", which also happens
  when a crawl limit or depth cuts a page off.
- Neither documents a login-wall or similar acquisition error class.

A failed fetch, a login wall or a timeout is an acquisition failure and never a deletion. Unchanged
extracted text does not imply unchanged interaction state, and changed HTML does not imply changed
extracted knowledge.

## 5 System: difffold

### 5.1 Objective

Ordered labelled trees, unit cost per node. For nodes x, y:

```text
dist(x, y) = 0                                              if x = y
           = [label x != label y] + align(kids x, kids y)    otherwise (roots always pair)

align(A, B) = min over ordered pairings of A and B of
              sum(size a for deleted a) + sum(size b for inserted b) + sum(dist(a, b) for paired)
```

This is the Selkow top-down distance, which deletes whole subtrees and needs matched parents. It is
not classical tree edit distance. **[D]**

### 5.2 Exact identity (I1)

`Arena::mk(label, kids)` hashes (label, kids) to a bucket in an apeiron `freq::Table<u64, u32>` and
reuses an id only if the label and child ids equal the stored ones. For nodes of one arena, equal
ids hold if and only if labels and child id lists are equal, for **any** bucket function. This is a
statement about the arena and says nothing about occurrences: identical subtrees at two positions
share one id and are two occurrences. **[I]**

A first version of this interner passed the merge arguments to `insert_with` in the wrong order
(the table calls `f(new, old)`), so a second node landing in an occupied bucket became unreachable
and I1 failed. Random tests did not see it because real fold values rarely collide. A test that
injects a constant bucket function exposed it, and the fix uses the table's last-write mutator.
**[M: the test fails before the fix and passes after]**

### 5.3 Threshold alignment (C2)

For child lists a (length n) and b (length m), let R_a(i) be the total size of a[i..] and R_b(j) that
of b[j..], and let h(i, j) = |R_a(i) - R_b(j)|.

*Lemma (admissibility).* The cost of aligning two forests X and Y is at least |size X - size Y|,
because each inserted or deleted node changes the size difference by one and a paired node's own cost
does not reduce it. So h(i, j) bounds the remaining cost from below. **[F: `h_admissible`, `tedit_bound`,
`hLists_admissible` in the Lean model, Section 8.9; also checked on small lists by
`tests/boundaries.rs`]**

*Algorithm.* F(i, j) is the cost of aligning a[..i] with b[..j] **using only kept cells**; it can
overestimate the true prefix minimum F*(i, j). A cell is kept when F(i, j) + h(i, j) <= tau. Start tau
at h(0, 0) and grow it until the final cell is kept.

*Claim.* Any path of total cost at most tau survives, and the final cell holds the true minimum
whenever that minimum is at most tau. The argument is on F* and R*, the true prefix and remaining
minima: if F*(i, j) + R*(i, j) <= tau, an optimal prefix path cannot cross a pruned cell, because at
the first pruned cell c on it F(c) = F*(c) and F*(c) + h(c) <= F*(c) + R*(c) <= tau would keep it;
therefore F(i, j) = F*(i, j) and the cell is kept. **[F: `prune_sound`,
`path_cells_kept`, `decision` in the Lean model, Section 8.9; also tested against an independent
oracle]**

The recursive pair cost dist(a_i, b_j) is computed only when F(i-1, j-1) + |size a_i - size b_j| +
h(i, j) <= tau. Pair costs are memoised on the exact 64-bit (id, id) key. Equal leading and trailing
children are stripped first. Matching identical children first and filling gaps is **not** used, and
a test pins the counterexample `[big, small]` against `[small, big']`. **[M]**

### 5.4 Replay (C3)

A script is a tree of Keep(id), Del(id), Ins(id) and Upd(from, to_label, kids). `apply(before,
script)` walks the before-tree beside the script, refuses any mismatch, and rebuilds the after-tree
through `mk`. The checked entry point asserts that the rebuilt id equals the target and that the
script's cost equals the reported distance. Replay shows reconstructability, not optimality and not
correct identity. **[M: every fixture in Section 8]**

### 5.5 Tests

Fourteen contract tests run in debug and release. They compare against an independent oracle (plain
recursion, a full DP, no memo, strip or pruning) on random mutated and unrelated pairs, on every
tree of at most five nodes over two labels against every other (over 100,000 pairs, in every
configuration), and on wide repetitive lists. They check the threshold contract (tau below, at and
above the optimum), bound admissibility against the true remaining cost at every cell of small lists,
identity under a constant bucket function, symmetry, the triangle inequality, and refusal of a script
against the wrong tree. Costs are unit costs only; custom costs are untested. **[M]**

## 6 Proposed architecture: maintain correspondence instead of reconstructing it

Everything in this section is **[D]**, with hypotheses where stated. It is the product direction, not
a result.

### 6.1 Three identities

```text
ContentId     exact canonical subtree content            (the interner)
OccurrenceId  this particular entity or node occurrence  (not yet implemented)
VersionId     one immutable observed state
```

Two identical cards share a ContentId and need not share an OccurrenceId. A card keeps its
OccurrenceId while its content changes. The interner supplies the first only.

Three refinements follow from reading the systems literature and the vendor documentation (Section 4).

- **An observation is not an event.** A VersionId records an attempt: when it was observed, the
  freshness policy requested, whether the result was cached or live, the acquisition outcome, the
  extractor version, and the ContentId of the payload. A removal is recorded only on positive
  evidence; otherwise the record says "not observed" with a reason.
- **Occurrence assignments are claims.** Neither vendor goes beyond URL equality, and Bonsai gives
  only copy-from edges, so entity correspondence is ours to build and is inferred. An OccurrenceId
  assignment carries its provenance (asserted by the site or inferred by a matcher, plus the matcher
  version) and lives outside the content hash.
- **Derived data carries edge labels.** Key each derived value by its input ContentIds, the extractor
  or matcher version and the configuration. Mark it dirty when an input ContentId changes and cut off
  when the re-derived ContentId is unchanged (the Adapton mechanism). This covers "changed HTML does
  not imply changed extracted knowledge" and non-deterministic LLM extraction.

### 6.2 Record edits when they happen

For mutations the system controls or reliably observes, record operations directly:
insert, delete, update, move, wrap and unwrap, each with occurrence identities. A move then is an
event, not an inference from similarity. This holds only for systems and clients that record it:
Scion stores first-parent changes and infers moves afterwards, and Bonsai alone records copy-from.

### 6.3 Three deltas, never one

| delta | question | property |
|---|---|---|
| historical | what happened according to trusted events | keeps moves and identity; may contain cancelling operations; not minimal |
| optimal | cheapest under a named objective | difffold's exact core; may disagree with history |
| presented | most useful explanation | groups a likely move, suppresses noise, carries provenance for every inference |

```rust
historical_delta(before, after)
optimal_delta(before, after, objective)
present_delta(delta, policy)
```

### 6.4 Four tiers

- **Tier 0, known facts.** Equal ContentIds are equal subtrees. A recorded transition returns its
  delta handle. A cached exact result for the pair, objective and representation policy is returned.
  The maintenance cost stays on the books.
- **Tier 1, compose recorded transitions.** A to B to C composes lazily; materialisation later
  cancels, coalesces and emits what is asked. Retained history, composition cost and query speed are
  explicit trade-offs.
- **Tier 2, reconcile the unknown frontier.** Parse and intern an external snapshot; find regions
  without provenance; run difffold there; store inferred correspondences separately from observed
  identity. Equality is candidate evidence and reuse, not a forced anchor.
- **Tier 3, budgeted exact refinement.** Keep L <= d* <= U, where L is a proved bound and U the cost
  of a replay-valid script; L = U certifies optimality. A fixed-time API can answer "not yet
  certified"; it cannot promise an exact answer within the same budget for every input.

### 6.5 Composable frontier summaries (speculative)

Instead of memoising (subtree_a, subtree_b) to a distance, summarise how a region interacts with its
boundary: the possible boundary states, the minimum cost between them, and reconstruction witnesses.
Regions combine through a small interface. With boundary width b and r recomputed regions the target
would be T = O(f(b) * r + k) for k emitted operations. **[H]** Falsified if the boundary state needed
for correct composition grows with the region (unmatched sibling sequences, cross-boundary moves,
wrappers spanning regions, repeated ambiguous nodes), so that the summary is as large as the table it
replaces. The first task is to define a sufficient boundary state and measure how it grows on the
simplest case, move-free sibling alignment.

### 6.6 Experiments

1. **Persistent versions with recorded edits.** Generate histories with preserved occurrence
   identity. Compare independent snapshot diffing, recorded-delta composition, recorded history with
   events deliberately missing, and reconciliation after a full provenance break. Measure capture and
   maintenance cost as well as query latency.
2. **Cross-version memoisation.** Cache keys include before ContentId, after ContentId, objective and
   representation policy. A thresholded "exceeds tau" result is not an exact distance and is stored
   as such.
3. **Replayable composite deltas.** Immutable DAGs of Identity, PrimitiveEdit, Compose and
   RegionPatch. Measure construction, materialisation, memory growth, repeated traversal and how much
   simplification can be deferred.
4. **Bounded-interface summaries.** As in Section 6.5.

### 6.7 Three contracts that must stay separate

```text
storage durability      !=  replicated convergence
replicated convergence  !=  a correct program or document
Git-compatible output   !=  a Git-compatible repository
```

The layered programme is: native edits become CRDT operations; external snapshots go through
difffold reconciliation; both feed a versioned change graph stored as immutable objects; snapshots
are materialised deterministically; a compatibility layer emits Git diffs and patches. difffold does
not solve storage, concurrency or compatibility. It supplies exact reconciliation for external states
and a replay-checked structural view. Native editing must not be downgraded to snapshot diffing and
then asked to rediscover the operation history it already had.

### 6.8 Object storage layout and publication

Assuming S3 means an object-store backend and not an S3-compatible server:

```text
objects/    raw bytes and immutable encoded structures
changes/    immutable operations and changesets
snapshots/  materialised states and checkpoints
refs/       small mutable pointers to published versions
```

Raw bytes stay available: parsed trees and CRDT state must not be the only representation if lossless
Git interoperability is wanted. Publication of one reference: write all newly referenced immutable
objects, confirm them, update the reference conditionally against its previous value, and on a
conditional failure fetch, reconcile or retry. Amazon S3 offers `If-None-Match` for create-if-absent
and `If-Match` for conditional replacement†. That is an optimistic primitive for a single reference
object and is not a multi-object transaction. The reference state carries an application revision or
publication id so retries and history are explicit.

An S3 ETag is a storage precondition token and not a content id; depending on upload method and
encryption it need not be an MD5†. The arena's collision-safe identity is in-memory and does not give
globally collision-free object names: objects addressed only by a digest need either a stated
cryptographic assumption or a collision-detection and disambiguation rule. S3-compatible backends
need their conditional writes and consistency tested and not assumed.

### 6.9 Replication granularity and the convergence ladder

Start with the authoritative lossless text and let structure be derived:

| data | candidate model |
|---|---|
| source-file content | sequence or text CRDT |
| file namespace | explicit directory and file identity with defined rename and delete semantics |
| metadata | maps or registers that surface concurrent values where needed |
| binary files | immutable blobs with explicit concurrent-version selection |
| parsed AST or DOM | derived representation, initially |
| crawled observations | immutable observations, not collaborative edits |

Convergence means replicas holding the same set of changes reach the same state (the guarantee
Automerge states†). It does not mean the merged program compiles or that two agents' intentions are
compatible: one agent renaming a function and its callers while another adds a caller of the old
name converges and breaks. So states carry separate statuses, none implying the next:

```text
replication-converged -> materialised -> parse-valid -> typecheck-valid -> policy-approved -> published
```

For a browser or crawler, two observers seeing different prices are not concurrent authors of one
field: they differ in time, account, region, session state and capture completeness. Merge the
observation records and their provenance; do not merge extracted values into one purported source
truth.

### 6.10 Git compatibility levels

| level | meaning | scope |
|---|---|---|
| external diff helper | Git invokes difffold for selected comparisons | smallest |
| apply-compatible patch | output is accepted by `git apply` | needs exact patch encoding |
| CLI substitute | the relevant `git diff` options, statuses and modes | much broader |
| Git object export | blobs, trees, commits and refs | repository interoperability |
| Git server replacement | clone, fetch, push and ecosystem behaviour | a separate platform project |

Git supports external diff commands through `GIT_EXTERNAL_DIFF` and attributes†, which is the
cleanest first integration, and an external helper that renders a structural display is not
thereby producing an applicable patch. Two modes follow. **Review mode** carries structural moves,
wrappers, correspondence and explanations. **Patch mode** is a Git-compatible transformation of
exact bytes; moves inside a file appear in it as deletions and insertions, and richer move metadata
travels alongside the patch. Binary files need a deliberate path (Git emits applicable binary diffs†),
not a text fallback.

The bridge invariant, interpreted over exact bytes and relevant file metadata and not over parsed
trees:

```text
GitApply(A, Patch(A, B)) = B
Materialise(ApplyOperations(S, O)) = B
```

A Git patch carries no CRDT causal identity, so importing one means choosing a base state and
translating its edits into operations against that state; the format does not supply that. There are
two certificates and the first does not imply the second: the **structural** certificate (the tree
script reconstructs the target canonical tree) and the **materialisation** certificate (the
translated operations reconstruct the intended bytes). Comments, whitespace, encoding and parser
error recovery can separate them. The first implementation uses structural results for
correspondence and presentation and keeps a byte-level fallback that guarantees exact
reconstruction.

### 6.11 The three-replica compatibility harness

One demanding vertical slice before any server: three agent replicas, a small repository, immutable
object storage, native text operations, Git patch import and export, and difffold reconciliation of
external edits.

| injected case | tests |
|---|---|
| duplicate and reordered operation delivery | replication correctness under the chosen protocol |
| offline edits then synchronisation | convergence and retained history |
| two writers publishing the same ref | conditional publication and retry |
| crash after object upload, before the ref update | unreferenced objects without a partial published version |
| rename versus edit; delete versus edit | namespace and content identity; an explicit conflict policy |
| concurrent function rename and new caller | convergence versus semantic validity |
| Git patch imported against an older base | base-aware translation |
| binary, CRLF and no-final-newline files | lossless compatibility |
| repeated identical subtrees | content identity versus occurrence identity |
| checkpoint and history compaction | whether supported old or offline replicas can still recover |

No unbounded "all operations eventually merge" claim is made after garbage collection: the
supported replicas, history horizons and resynchronisation procedures are defined. Measured for the
whole system: bytes stored per edit, bytes synchronised, native-operation versus snapshot-import
cost, materialisation latency, patch generation and application correctness, peak memory, conflict
and semantic-invalid-state frequency, publication retries, and cross-version diff-cache reuse. A
constant-time delta handle counts only with the ingestion, publication and materialisation work
included.

### 6.12 Milestone order

First, external diff-helper compatibility and lossless patch round trips over an immutable version
store (Git compatibility levels one and two, under way). Then CRDT editing for native clients. The
sequence establishes compatibility at once, preserves the exactness work, and introduces concurrency
without making every subsystem a new research problem simultaneously.

### 6.13 What webfold has today, and a first slice

From a code reading of webfold and superdocuments (`notes/webfold/INTEGRATION.md` and
`INVENTORY.md`; nothing was built or run, so none of this carries a performance or accuracy claim).
The four items below were spot-checked against the source by the lead.

- The only change detector, `watch.rs`, diffs rendered Markdown lines. An empty render is reported as
  `Unavailable`, which is the false "gone" of Section 4: a failed or empty observation read as a
  removal. A login or challenge page that renders some text becomes a content change. Over MCP each
  `change_watch_check` builds a fresh watch state, so every check reports first-seen.
- Richer acquisition status exists in the browser layer (`BrowserState` and related types) and does
  not reach the record, the watch events or the index.
- A BLAKE3 Merkle DOM signature exists in `node_signature.rs` and its only caller prints CLI rows. It
  omits `href`, `src`, `value`, `checked` and `disabled`, so a changed link destination or control
  state is invisible, and empty subtrees get no digest, so deleting one is invisible.
- Block signatures disagree across crates: superdocuments' `html/extract.rs` still uses FNV-1a while
  webfold's copy uses a different mix. They are built from the body before its heading or quote
  prefix is added and exist for boilerplate counting; reusing them as change identity would be wrong.

Reported by the survey and not individually re-checked: derived data (postings, embeddings,
file windows) is replaced wholesale and never invalidated by dependency; the JSONL content hash uses
a toolchain-dependent hasher and nothing compares it; `AxNode` is an ordered role-and-name tree, a
natural target for action-precondition checks, while `webmcp` addresses controls by index into a
list that shifts when the DOM changes; superdocuments' `DocumentGraph` regions carry no ids; no
multi-version page corpus exists in the bench repositories read.

**First slice (design, about a week):** a status-gated, block-level change feed for one URL with
difffold as the engine. An `ObservationStatus` type allows "removed" only between two complete,
trusted observations and otherwise yields "not comparable". An adapter turns blocks into a tree
whose labels carry the Markdown prefix, normalised text and link destinations. Content digests are
persisted and occurrence ids are carried across the correspondence. Acceptance tests: replay
equality; a status gate under which a 404, a challenge, a login page and an empty render never
produce a delete, with a negative control; a link-only change; occurrence stability; cross-process
determinism (difffold's `u32` labels need a persisted label table or digests to be stable between
processes); and unchanged conversion output. The status gate is the highest-value fix and needs no
differ.

Not evidenced: that speed measured on Java, Go and C transfers to web trees; how well the Selkow
objective handles wrapper-div redesigns, which cost the whole subtree; whether block diffs beat the
existing line diff on real pages. Moves are not supported.

## 7 Experimental method

### 7.1 Hypotheses

| id | hypothesis | falsified if |
|---|---|---|
| H1 | Structural matching beats block-level sequence alignment on correspondence enough to justify its cost. | Myers or histogram on content blocks has equal or higher mapping F1 on the controlled corpus at lower latency. |
| H2 | Identity and role constraints improve precision more than a more expensive generic solver. | A generic solver with matched costs equals the constrained matcher's identity-switch rate. |
| H3 | Explicit move and wrap handling improves persistent entity identity. | Wrong-entity matches do not fall on move, reorder and wrap cases when recovery is on. |
| H4 | Rejecting ambiguous matches reduces dangerous false matches while retaining useful coverage. | The accuracy-versus-coverage curve has no knee. |
| H5 | A cheap-first hybrid approaches the best matcher's accuracy at lower tail latency. | Accuracy is below the best single matcher by more than the noise floor, or p99 is not lower. |
| H6 | The best representation differs by task. | One representation dominates every task. |
| H7 | Maintained provenance makes a query proportional to its output on known history. | Query latency on recorded history grows with snapshot size. |
| H8 | A byte-exact patch mode round-trips through `git apply` on every fixture pair and edge case. | Any pair where `git apply` of the patch does not reproduce the after-bytes exactly. |

### 7.2 Two tracks

**Same objective.** Only the top-down recurrence is compared. The ladder is: full DP with structural
comparison; plus exact interning; plus memoisation; threshold DP with the same interning and memo;
and threshold DP with alternative first thresholds and growth factors. Costs, tie breaking and script
construction are kept consistent. This isolates what interning, memoisation and pruning each buy.

**Cross objective.** git's four algorithms, Difftastic, OmniDiff, GumTree, Zhang-Shasha, APTED and
difffold, each labelled with its objective. Zhang-Shasha and APTED allow child promotion on deletion
and are not objective-matched to a top-down solver. RefactoringMiner is included for code fixtures
only and is not evidence about DOM behaviour.

### 7.3 Datasets

(a) OmniDiff's hand-authored fixtures with mapping ground truth. (b) A controlled mutation corpus with
recorded lineage, split by site and not by pair, ambiguity marked rather than penalised. (c) A shape
and performance corpus varying node count, changed fraction, depth, branching, repeated subtrees and
near-identical sibling lists independently. (d) Real temporal web observations with independent
annotation: **not collected**. This paper makes no external-validity claim until they are.

### 7.4 Metrics

Correspondence: node and entity mapping precision, recall and F1; changed-span precision and recall;
perfect-case rate; identity switches across a sequence. Classification: insert, delete, update and
move precision and recall. Noise: false changes under declared-irrelevant transformations.
Ambiguity: accuracy against coverage. Performance: p50, p95, p99, peak memory, timeout and fallback
rates, with parse, match, edit generation, serialisation and replay separated; four timing views
(parse included for all, parse excluded for all, matching only, full production path including
validation) and paired per-fixture ratios with randomised tool order. A budget-exceeded
approximation is never labelled exact. Where a metric needs mapping ground truth, highlight
annotations alone are not used to claim identity.

## 8 Results

### 8.1 Cost against OmniDiff's recorded time **[M]**

Machine: 4 vCPU cloud VM, one run, release build, measured after the interner fix, after the
interner moved onto apeiron's certified `Table` (about 7% slower in total than the earlier
hashtrinity-port table) and after the DP moved into the extractable kernel. OmniDiff's figure
is its recorded `diff_code` time on parsed trees; difffold's is interning plus diff. Both exclude the
tree-sitter parse. 997 Java, Go and C fixtures.

| | OmniDiff | difffold |
|---|---|---|
| total | 16,735 ms | 1,239 ms |
| median | 9.6 ms | 0.89 ms |
| p90 | 33.5 ms | 2.3 ms |
| p99 | 126.7 ms | 4.3 ms |
| worst | 302.8 ms | 47.7 ms |

Per-fixture ratio: minimum 1.4, median 9.2, maximum 215; total ratio 13.5. Adding the tree-sitter
parse to difffold's time and not OmniDiff's lowers the total to 4.1, which is not a symmetric
comparison. The objectives differ (Section 5.1), the measurement is one run, and nothing here is a
claim about accuracy.

### 8.2 Why OmniDiff's slow cases were slow **[M]**

Callgrind on a 182 ms OmniDiff fixture: about 90% of instructions in the APTED dynamic program,
about 3% in tree-sitter, under 2% in hashing and allocation. Across the 30 slowest fixtures 88% of the
DP cells were in the single largest APTED call (a residual of 450 to 850 nodes per side taken from
files of 5,000 to 15,000 nodes) and identical forest pairs essentially never repeated. Cutting that
residual at leaf anchors unique to both sides cut the cell count 12.6 times; that estimate counts
cells and not accuracy, and anchoring is not used in the solver (Section 5.3).

### 8.3 Threshold rounds **[M]**

The slow difffold cases are wholesale rewrites. The `widenings` counter sums extra rounds over every
nested align; across the corpus it is 207,771 over 377,949 distinct pair computations, about 0.55
extra rounds per pair. It is not a count of outer attempts, and "46,000 rounds" in an earlier note
referred to such a sum. An outer attempt count and a per-pair distribution are part of the ablation
harness (built, not yet run).

### 8.4 Same-objective ablation `PENDING`

The harness `ablate` records, for each configuration, distance-only and distance-plus-script time,
cells visited and kept, aligns, rounds and maximum rounds, memo hits and misses, peak bytes,
interning time and replay time, with configuration order shuffled per fixture. It has been built and
not run.

### 8.5 Accuracy against ground truth `PENDING`

*Mapping precision, recall, F1 and perfect-diff rate for both tools on the same fixtures and metric,
with a failure taxonomy (local relabel, sibling insert and delete, repeated children, reorder,
cross-parent move, wrap and unwrap, wholesale rewrite) and the cross-parent-move bound. From
`results/accuracy/SUMMARY.md`.*

### 8.6 Wall clock against external baselines `PENDING`

*p50, p99, maximum and peak memory per tool under the four timing views, with fallbacks and failures
shown. From `harness/results/SUMMARY.md`.*

### 8.7 Controlled corpus: wrap, move, duplicates, ambiguity `PENDING`

*Per-case tables, by-site split; false recovered identity reported apart from a missed move and a
correct abstention.*

### 8.8 Git compatibility `PENDING`

*Round-trip pass rate of the patch mode over the fixture corpus and edge cases (CRLF, no final newline, binary, NUL, non-UTF-8, mode change), patch size and generation time against `git diff` under four algorithms, and which of the two certificates hold per case. From `gitcompat/SUMMARY.md`.*

### 8.9 Mechanised proofs **[F, model only]**

Lean 4.31.0 (the version apeiron pins), no Mathlib, five modules of about 910 lines, no `sorry` and
no custom axiom. Re-checked from clean object files; the headline theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`, or on `propext` and `Quot.sound` alone (`proof/AXIOMS.txt`).
Every theorem is about the Lean model of the top-down objective, not about the Rust code.

| theorem | what it says |
|---|---|
| `h_admissible`, `tedit_bound`, `hLists_admissible` | the size difference bounds the cost of any alignment, and every top-down edit, from below, so the bound `h` is admissible |
| `prune_sound`, `path_cells_kept` | with `h <= R*`, every cell on a path of cost at most tau is kept and holds exactly the true prefix minimum, although the DP computes from kept predecessors only |
| `decision`, `result_is_min` | the final cell holds a result iff the true minimum is at most tau, and then it is that minimum |
| `search_min`, `search_total` | the widening loop returns the true minimum, and returns within `k + 1` rounds when the minimum is at most tau + k |
| `skip_sound` | skipping the recursive pair cost under the size bound changes no kept value |
| `prune_correct_lists`, `widen_correct_lists`, `fstar_is_opt` | the above end to end on child lists, with the result an optimal alignment |
| `strip_safe`, `strip_safe_iff` | pairing equal leading and trailing children at cost zero loses no optimality; no triangle inequality is needed |

`prune_sound` is stated in the corrected form of Section 5.3: it does not assert that the DP's prefix
value is a lower bound, only that cells on paths of cost at most tau are kept and exact.

**Against caretaker's evidence standard.** caretaker (the review and maintenance agent in this
organisation) records a Rust claim as proven by the Lean kernel only when Charon extraction, Aeneas
translation and the Lean check all pass for the same source with each stage's input digest equal to
the previous output digest, and it rejects calling a weaker model a proof. By that standard the
theorems above are about a model and the Rust claim is **not yet proven**. What exists for the Rust
code: the alignment kernel (`src/kernel.rs`) is the only implementation of the threshold DP and is
what the library calls; Charon (commit b104e24) and Aeneas (release 505b6ca, archive digest
verified) extract it with no errors; the Lean kernel elaborates the result for the recorded digest
chain; and three small theorems (`adiff`, `umin`, `Row.at`) are checked over the extracted code.
The tool binaries are the stock release and not apeiron's patched build. The extracted loop
functions have no specification yet, so the model theorems do not yet transfer to the Rust.

The interner's bucket heads now live in apeiron's certified `Table`, whose canonical object is
`Apeiron.Table.HMap`; the identity theorem over that object is not yet written.

Not proved: replay soundness; exact identity of the arena for any bucket function with last-write
semantics (the defect found by the constant-bucket test lived there, and its fix is covered by a
Rust test and not a proof); that the Rust recursion computes the model's distance; any link from the
Rust code to these theorems, since Aeneas and Charon extraction was not attempted; and agreement with
apeiron's own axiom-audit policy, which was not read against these results.

## 9 Limitations

- The objective is the top-down distance. Cross-parent moves, wrap and unwrap, split and merge are
  outside it; ground-truth pairs of those kinds bound what a top-down matcher can reach, and the
  cost comparison in Section 8.1 compares different problems.
- Speed numbers are one run on one machine against OmniDiff's recorded times; variance is not yet
  characterised, and the paired, randomised-order, four-view protocol of Section 7.4 has not been
  run.
- Wrapper recovery is a prototype question. It should be built only if the failure taxonomy shows
  wrappers account for a meaningful part of the accuracy gap, and its output must be kept apart from
  the exact core's cost: a recovered interpretation is not an optimum under an enlarged operation
  set.
- The threshold schedule is open: wholesale rewrites spend the most rounds, and a better first
  threshold is not found.
- Hash-consing makes identity exact inside one arena. Cross-arena or cross-process identity needs a
  content address with its own collision policy, which is not claimed.
- Costs are unit costs; custom cost models are untested.
- Mathematical statements in Section 5 are mechanised over a Lean model (Section 8.9) and tested
  against an oracle; the Rust code is not extracted or formally linked to the model, so the
  guarantee is that the algorithm as modelled is correct and that the implementation agrees with
  an oracle on the tested cases. Measured sections are benchmarks. Neither is evidence for the
  other. Section 6 is design.
- No real temporal web observations were collected, so nothing here is evidence about real-site
  behaviour.
- Sections 6.7 to 6.11 are design. Only Git compatibility levels one and two are being built; object
  storage, CRDT editing and the three-replica harness have no implementation, and no claim about
  S3-compatible backends is made.

## References

- Levenshtein, V. I. (1966). Binary codes capable of correcting deletions, insertions and reversals. Soviet Physics Doklady 10(8).
- Wagner, R. A., Fischer, M. J. (1974). The string-to-string correction problem. J. ACM 21(1).
- Hirschberg, D. S. (1975). A linear space algorithm for computing maximal common subsequences. CACM 18(6).
- Hunt, J. W., McIlroy, M. D. (1976). An algorithm for differential file comparison. Bell Labs CSTR 41.
- Hunt, J. W., Szymanski, T. G. (1977). A fast algorithm for computing longest common subsequences. CACM 20(5).
- Selkow, S. M. (1977). The tree-to-tree editing problem. Information Processing Letters 6(6).
- Tai, K.-C. (1979). The tree-to-tree correction problem. J. ACM 26(3).
- Ukkonen, E. (1985). Algorithms for approximate string matching. Information and Control 64.
- Myers, E. W. (1986). An O(ND) difference algorithm and its variations. Algorithmica 1.
- Zhang, K., Shasha, D. (1989). Simple fast algorithms for the editing distance between trees and related problems. SIAM J. Computing 18(6).
- Myers, G. (1999). A fast bit-vector algorithm for approximate string matching based on dynamic programming. J. ACM 46(3).
- Chawathe, S. S., Rajaraman, A., Garcia-Molina, H., Widom, J. (1996). Change detection in hierarchically structured information. SIGMOD 1996.
- Tridgell, A., Mackerras, P. (1996). The rsync algorithm. Technical report TR-CS-96-05, Australian National University.
- Fluri, B., Wuersch, M., Pinzger, M., Gall, H. (2007). Change distilling: tree differencing for fine-grained source code change extraction. IEEE TSE 33(11).
- Demaine, E. D., Mozes, S., Rossman, B., Weimann, O. (2009). An optimal decomposition algorithm for tree edit distance. ACM Trans. Algorithms 6(1).
- Pawlik, M., Augsten, N. (2011). RTED: a robust algorithm for the tree edit distance. PVLDB 5(4).
- Falleri, J.-R., Morandat, F., Blanc, X., Martinez, M., Monperrus, M. (2014). Fine-grained and accurate source code differencing (GumTree). ASE 2014.
- Hammer, M. A., Phang, K. Y., Hicks, M., Foster, J. S. (2014). Adapton: composable, demand-driven incremental computation. PLDI 2014.
- Backurs, A., Indyk, P. (2015). Edit distance cannot be computed in strongly subquadratic time (unless SETH is false). STOC 2015.
- Pawlik, M., Augsten, N. (2016). Tree edit distance: robust and memory-efficient. Information Systems 56 (arXiv:1805.06869).
- Dotzler, G., Philippsen, M. (2016). Move-optimized source code tree differencing. ASE 2016.
- Bringmann, K., Gawrychowski, P., Mozes, S., Weimann, O. (2018). Tree edit distance cannot be computed in strongly subcubic time (unless APSP can be). SODA 2018.
- Marco-Sola, S., Moure, J. C., Moreto, M., Espinosa, A. (2021). Fast gap-affine pairwise alignment using the wavefront algorithm. Bioinformatics 37(4).
- Marco-Sola, S., Eizenga, J. M., Guarracino, A., Paten, B., Garrison, E., Moreto, M. (2023). Optimal gap-affine alignment in O(s) space. Bioinformatics 39(2).
- Git documentation: diff-algorithm option. https://git-scm.com/docs/diff-algorithm-option.html
- Wilfred Difftastic documentation: diffing, tricky cases. https://difftastic.wilfred.me.uk
- † arXiv:2403.05939: AST-diff evaluation and RefactoringMiner mapping accuracy.
- † Anthropic (2026-10-13). Redesigning source control (Scion). https://www.anthropic.com/research/redesigning-source-control
- † TechRadar (2026). OpenAI reportedly building a GitHub alternative.
- † Exa documentation: freshness and monitors. https://exa.ai/docs
- † Firecrawl documentation: change tracking and monitoring. https://docs.firecrawl.dev/features/change-tracking
- † Amazon S3 documentation: conditional writes (If-None-Match, If-Match). https://docs.aws.amazon.com/AmazonS3/latest/userguide/conditional-writes.html
- † Automerge documentation: getting started and glossary (convergence statement). https://automerge.org/docs/hello/
- † Git documentation: git-diff (GIT_EXTERNAL_DIFF, binary diffs). https://git-scm.com/docs/git-diff
- † 2025 ChangeDistiller retrospective (IEEE TSE). arXiv:2604.12696 (Albert, longest common extension of a dynamic string, CPM 2026); abstract read only.
