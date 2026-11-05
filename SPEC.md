# difffold contracts

Each contract is a statement the code enforces or the tests check against an independent oracle
(`tests/contracts.rs`: naive recursion, full alignment DP, no memo, strip, threshold or pruning).
Status is stated per contract. The "status" column below describes the Rust tests only. Lean work
exists in `proof/` (a model of the top-down objective in `proof/Difffold/`, and proofs over the
Aeneas translation of `src/kernel.rs`); it is about a model or a part of the code, not about the Rust
`diff` end to end, and `proof/README.md` gives the per-theorem status. The statements are written to be
portable to the apeiron corpus.

This file states the contracts of the **top-down `diff` engine** (`src/diff.rs`, `src/intern.rs`). The
general tree-edit-distance engine `src/ted.rs` has a different objective and is covered by
`tests/ted.rs`; see the README "Choose an engine" table.

Objective of `diff`: top-down (Selkow) ordered-tree edit distance, unit cost per node. `dist(x,y) = 0` if
`x = y`; otherwise `[label x != label y] + align(kids x, kids y)`, where `align` is the cheapest
ordered pairing of two child lists with delete = subtree size, insert = subtree size, pair =
`dist`. Roots always pair.

| id | statement | how it is enforced | status |
|---|---|---|---|
| I1 | For nodes of one arena, `x = y` as ids iff labels are equal and child id lists are equal. Hence id equality is deep structural equality, for any bucket function. | `Arena::mk` confirms every bucket candidate against the stored label and children before reusing an id; the 64-bit fold only selects the bucket. | tested against a plain-struct model, and with an injected constant bucket function (`Arena::with_fold`) that forces every node into one chain. That test found a defect (swapped merge arguments) in the first version; see README. |
| C1 | Pairing equal first or last children at cost 0 loses no optimality. | stripped before the DP | covered by C4 |
| C2 | A cell is kept iff `F(i,j) + h(i,j) <= tau`, `h(i,j) = abs(R_a(i) - R_b(j))`, `R` the reversed size accumulation. A pruned cell lies on no path of cost `<= tau`; a result of cost `<= tau` is optimal. `tau` doubles from `h(0,0)` until a result fits. | `Differ::fill` / `align_mid`; sub-cost recursion is skipped when `F_diag + abs(size_a - size_b) + h > tau` | covered by C4, including a test that forces several threshold rounds |
| C3 | `apply(before, script) = after` id for id, and `cost(script) = dist`. | `diff_checked` asserts both; `apply` refuses a script that does not fit the tree it is given | asserted on every random pair in the tests and on every benchmark fixture |
| C4 | `dist` equals the oracle, in every `Config` (full DP with structural or id equality, memo on or off, threshold on with any first threshold and growth). | none needed; this is the check | 1,500 mutated pairs, 600 unrelated pairs, 200 wide repetitive lists, every tree of at most 5 nodes over 2 labels against every other (over 100,000 pairs, all configs), plus the crossing case below |
| C5 | `dist(x,y) = dist(y,x)` | | 400 triples |
| C6 | `dist(x,y) = 0` iff `x = y` | follows from I1 | tested |
| C7 | `dist(x,y) >= abs(size x - size y)` | used as pruning, so a violation would break C4 | tested through C4 |
| C8 | triangle inequality | | 400 triples |

## Why identical-first anchoring is not used

Matching identical children first and filling the gaps is not optimal. `[big, small]` against
`[small, big']`, where `big'` differs from `big` by one leaf: identical-first keeps `small` and
pays `size(big) + size(big')`; pairing the two big children pays about 3. The test
`identical_first_anchoring_would_be_wrong_here` pins this. The measured 12.6x window effect from
the earlier OmniDiff experiment is realised here without anchors: pruning by `F + h` discards the
same regions, and the result is certified instead of assumed.

## Proof targets for the apeiron Lean corpus

1. `mk_exact`: `mk l ks = mk l' ks'` iff `l = l'` and `ks = ks'` (I1).
2. `prune_sound`: for admissible `h`, every path of cost `<= tau` stays inside kept cells (C2).
3. `h_admissible`: `abs(size X - size Y) <= cost(any alignment of forests X, Y)`.
4. `strip_safe`: C1, by the usual exchange argument.
5. `replay_sound`: `apply` rebuilds the after-tree whenever it returns `Ok` and the script is the
   one `edit` produced (C3).

## Threshold boundary contract

`align_within(a, b, tau)` returns `None` iff the optimum exceeds `tau`, and otherwise the exact
optimum, for any `tau >= optimum`. `tests/boundaries.rs` checks `tau = d - 1`, `d`, `d + 1`, `d + 3`,
`d + 40` against the oracle, and checks `h(i, j) <= true remaining cost` at every cell on small
lists. Costs are unit costs only; custom costs are not supported and the bounds are untested under
them.
