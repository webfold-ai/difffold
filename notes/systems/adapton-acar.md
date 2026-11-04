# Adapton (Hammer, Phang, Hicks, Foster, PLDI 2014) and Acar's self-adjusting computation

Read on 2026-11-03.

## Provenance of what I read
- Adapton PLDI 2014: FULL TEXT (pdftotext of the 11-page PDF), fetched from https://matthewhammer.org/adapton/adapton-pldi2014.pdf (the author's own copy; the UMD URL failed TLS verification and the ACM DOI returned 403, so I did not use either). I read intro, overview (Sec 2), implementation/dirtying algorithm (Sec 5), evaluation (Sec 6), related work and conclusion. I did NOT work through the formal rules of Sec 3-4 line by line; I read their prose and theorem statements only.
- Acar, "Self-Adjusting Computation", CMU-CS-05-129 (May 2005): https://www.cs.cmu.edu/~rwh/students/acar.pdf. Text extracted in full, but I READ only the abstract, Chapter 1 contributions, and the change-propagation cost theorem statements. This is a 2005 thesis, so it is the background, not the 1990s-2002 originals (Acar-Blelloch-Harper POPL 2002 was not read).
- Adapton homepage https://adapton.org/ (fetched 2026-11-03) confirms the lineage and says the PLDI 2014 paper is "the machinery" and the OOPSLA 2015 "Incremental Computation with Names" paper "is what makes it addressable". I did not read the OOPSLA paper beyond the arXiv abstract page (arXiv:1503.07792).

## Mechanism (Adapton)
- Two node kinds in the demanded computation graph (DCG): mutable `ref` cells (inputs, written only by the "outer" layer) and memoised `thunk`s (computations, "inner" layer, may read refs but not write them). Edges record "this thunk used that ref/thunk" and are LABELLED with the value observed at the time.
- Dirtying (eager, on `set`): "A DAPTON traverses the graph from the mutated node downwards, dirtying the nodes and edges that (transitively) depend on the changed reference cell". Algorithm 1: for each `set`, traverse backward over incoming edges marking edges dirty, stopping at already dirty edges.
- Propagation (lazy, on `force`): "selectively traversing dirty nodes and edges from the bottom upwards and left to right, repairing dirty graph components by reevaluating dirty thunk nodes". For each dirty outgoing edge of the forced thunk, clear the flag, recurse into the target if it is a thunk, then compare the target's current value to the edge label; if inconsistent, drop all outgoing edges and re-evaluate the thunk. This is the early-cutoff: a recomputed thunk whose output is unchanged does not force its dependents to re-run.
- Invariant they maintain: "if an edge is dirty at the end of a dirtying or propagation phase, then all edges transitively reachable by traversing incoming edges ... will also be dirty; dually, if an edge is clean, then all edges transitively reachable by traversing outgoing edges ... will also be clean." This amortises dirtying across consecutive `set`s and propagation across consecutive `force`s.
- Demand-driven: "recomputation is delayed until thunks accessing cells' dependents are forced". Undemanded results stay dirty and are never repaired.
- Reuse beyond traditional IC: sharing, swapping, switching (their names). Traditional IC imposes a total order on a trace (Dietz-Sleator order-maintenance), so reordering defeats reuse; the DCG is a partial order.
- Soundness: "patched results will match what (re)computation from scratch would have produced" (consistency theorem; the "from-scratch consistency" property).

## Numbers, with exact scope and baseline
- Micro-benchmarks (map, filter, sort, fold, exptree, etc.) on OCaml 4.00.1, 8-core 2.26 GHz Mac Pro, 16 GB. Baselines: `LazyNonInc` (plain lazy, no reuse) and `EagerTotalOrder` (traditional Acar-style IC).
- Quote: "where traditional IC gets 2x to 20x speedups over naive recomputation, ADAPTON gets 7x to 2000x" for lazy interactions (partial demand). "For one program (mergesort), traditional IC actually incurs a 6.5x slowdown, whereas ADAPTON provides a 300x speedup."
- "ADAPTON does not perform as well as traditional IC when all output is demanded - it can be 1.5x to 3.5x slower". Batch pattern: "only about half the speedup of EagerTotalOrder, while using 103-120% the memory". For lazy/swap/switch it uses "3-98% the memory" of EagerTotalOrder.
- Spreadsheet AS2: "speedups of up to 20x compared to naive recomputation"; classic IC "always resulting in a slowdown (up to 100x)".
- All numbers are about relative speedup over non-incremental recomputation of a functional program on synthetic inputs with random edits. None concern web pages, diffs, or provenance.

## Cost model
- Adapton PLDI'14 has NO asymptotic cost theorem. Its claims are (i) from-scratch consistency and (ii) empirical speedups. The cost statements live in Acar's line of work.
- Acar thesis: dependence tracking has "O(1)" overhead; change propagation time is bounded in terms of the work of the new execution and deleted execution; and the higher-level analysis "trace stability": "if the trace distance between two computations is O(f(n)) ..., then change propagation can transform one computation into the other in O(f(n) log f(n)) time, in general, and in O(f(n)) time in certain cases." So the cost is parametrised by a DISTANCE BETWEEN TRACES (an edit distance over executions), and the bound is only good when the program is "stable" (small input change gives small trace change). Sorting/hulls/tree contraction get expected O(log n) per-update bounds only because the algorithms were designed to be stable.

## Stated limitations
- Total-order IC limitation (their motivation). Adapton: slower when all output is demanded; memory overhead; requires the inner/outer discipline (inner code is pure, only outer code mutates); correctness relies on identity of thunks by structural memo match. The OOPSLA 2015 follow-up exists precisely because structural matching makes reuse unreliable: names are needed so "a second run [does not have] to infer which node is which" (adapton.org wording).
- Dirtying cost grows with demand size: "the dirtying cost increases with demand size" as more edges are cleaned by propagation and re-dirtied.

## Lesson for a provenance DAG with ContentId / OccurrenceId / VersionId
1. A DCG edge is labelled with the value observed. Early cutoff = compare ContentId of the re-derived value to the label. That is exactly "changed HTML does not imply changed extracted knowledge": a derived record whose ContentId did not change must not dirty its dependents.
2. Dirtying and repair are separate. Our `dependency invalidation` row should be eager-mark/lazy-repair: marking is cheap and recorded; recomputation only when a consumer demands. Provenance edges ARE the DCG.
3. Adapton had to add NAMES (OOPSLA 2015) because inferring "same node across runs" from structure is fragile. That is the OccurrenceId problem verbatim. Names must be supplied by something that knows identity; where none exists the correspondence is inferred and must be labelled as such.
4. Trace distance is the cost parameter, not input size. Our delta (historical, optimal, presented) is a trace-distance measure; the cost model should be stated as a function of how many dirty edges actually flip, not of page size.
5. The Adapton consistency theorem is the contract we want: incremental result equals from-scratch result. For the web this is unprovable (the source is not a pure function of our inputs); we can only claim consistency relative to the OBSERVATIONS held.
