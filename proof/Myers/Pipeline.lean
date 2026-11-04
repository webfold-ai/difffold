import Good
/-! The whole id-level pipeline of `diff_ids` as a Lean model: cut the common prefix and suffix of the ids,
drop the ids that occur on one side of the middle only, run the bidirectional Myers search on what is
left, and scatter the flags back. The theorem says the resulting script is a minimal edit script. -/
open scoped List
namespace Myers

/-- Flags of `diff_ids`, given the flags `ra`, `rb` that `solve` produced on the compacted lists. -/
def pipelineFlags (p s am bm : List Nat) (ra rb : List Bool) : List Bool × List Bool :=
  (List.replicate p.length false ++ expand (fun x => decide (x ∈ bm)) am ra ++ List.replicate s.length false,
   List.replicate p.length false ++ expand (fun x => decide (x ∈ am)) bm rb ++ List.replicate s.length false)

/-- The compacted middle lists, `ca` and `cb` of `diff_ids`. -/
def compact (am bm : List Nat) : List Nat × List Nat :=
  (am.filter (fun x => decide (x ∈ bm)), bm.filter (fun x => decide (x ∈ am)))

/-- Model-level correctness of the line search: the search never gets stuck, and the flags it yields are
a minimal edit script (kept lines equal, and the cost is `|a| + |b| - 2 * lcs a b`). -/
theorem line_search_optimal (a b p am bm s : List Nat) (ha : a = p ++ am ++ s) (hb : b = p ++ bm ++ s) :
    ∃ ra rb, Solve mid (compact am bm).1 (compact am bm).2 ra rb ∧
      Optimal a b (pipelineFlags p s am bm ra rb).1 (pipelineFlags p s am bm ra rb).2 := by
  obtain ⟨ra, rb, hs⟩ := solve_total mid_spec _ (compact am bm).1 (compact am bm).2 (Nat.le_refl _)
  refine ⟨ra, rb, hs, ?_⟩
  subst ha; subst hb
  exact opt_trim (filter_optimal (solve_optimal mid_spec hs))

theorem line_search_cost (a b p am bm s : List Nat) (ha : a = p ++ am ++ s) (hb : b = p ++ bm ++ s) :
    ∃ ra rb, Valid a b (pipelineFlags p s am bm ra rb).1 (pipelineFlags p s am bm ra rb).2 ∧
      cost (pipelineFlags p s am bm ra rb).1 (pipelineFlags p s am bm ra rb).2 + 2 * lcs a b =
        a.length + b.length := by
  obtain ⟨ra, rb, _, ho⟩ := line_search_optimal a b p am bm s ha hb
  exact ⟨ra, rb, ho.1, optimal_cost ho⟩

end Myers
