import TraceMap
import KidsWf
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! End to end: two trees built by `from_kids` from valid child lists get a mapping that is legal and optimal. -/

theorem real_trees_mapping (la : alloc.vec.Vec Std.U32) (ka : Slice (alloc.vec.Vec Std.U32))
    (lb : alloc.vec.Vec Std.U32) (kb : Slice (alloc.vec.Vec Std.U32))
    (hna : la.length < 2 ^ 14) (hpa : 1 ≤ la.length) (hKa : KidsValid la.length ka.val)
    (hnb : lb.length < 2 ^ 14) (hpb : 1 ≤ lb.length) (hKb : KidsValid lb.length kb.val)
    (hla : ∀ j < la.length, (la.val[j]!).val < 2 ^ 31) (hlb : ∀ j < lb.length, (lb.val[j]!).val < 2 ^ 31)
    (prefer_match : Bool) :
    (do
      let a ← ted.PostTree.from_kids la ka
      let b ← ted.PostTree.from_kids lb kb
      let r ← ted.ted_mapping_with a b prefer_match
      ok (a, b, r)) ⦃ res =>
      PT.Wf res.1 ∧ PT.Wf res.2.1 ∧ res.2.2.cost.val = TED res.1 res.2.1 ∧
        Valid (laOf res.1) (laOf res.2.1) (Mp res.2.2.pairs.val) ∧
        InRange 1 res.1.label.length 1 res.2.1.label.length (Mp res.2.2.pairs.val) ∧
        Cost (rcost res.1 res.2.1) 1 res.1.label.length 1 res.2.1.label.length (Mp res.2.2.pairs.val) =
          TED res.1 res.2.1 ⦄ := by
  refine WP.spec_bind (from_kids_wf la ka hna hpa hKa) ?_
  rintro a ⟨hA, hal⟩
  refine WP.spec_bind (from_kids_wf lb kb hnb hpb hKb) ?_
  rintro b ⟨hB, hbl⟩
  have hna' : a.label.length < 2 ^ 14 := by rw [hal]; exact hna
  have hnb' : b.label.length < 2 ^ 14 := by rw [hbl]; exact hnb
  refine WP.spec_bind (ted_mapping_with_spec a b hA hB hna' hnb' (by rw [hal]; exact hla)
    (by rw [hbl]; exact hlb) prefer_match) ?_
  intro r hr
  simp only [WP.spec_ok]
  exact ⟨hA, hB, hr⟩

end difffold_lines_extract
