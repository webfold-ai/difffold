import Solve
/-! The specs of `common_prefix` and `common_suffix` (as the extraction proves them) give a `Trim`. -/
open scoped List
namespace Myers

theorem trim_of_specs (A B : List Nat) (s e : Nat) (hs : s ≤ min A.length B.length)
    (hpre : A.take s = B.take s)
    (hmax : s = min A.length B.length ∨ ∃ x y, A[s]? = some x ∧ B[s]? = some y ∧ x ≠ y)
    (he : e ≤ min (A.length - s) (B.length - s))
    (hsuf : A.drop (A.length - e) = B.drop (B.length - e))
    (hemax : e = min (A.length - s) (B.length - s) ∨ (e < min (A.length - s) (B.length - s) ∧
      ∃ x y, A[A.length - 1 - e]? = some x ∧ B[B.length - 1 - e]? = some y ∧ x ≠ y)) :
    Trim A B (A.take s) ((A.drop s).take (A.length - s - e)) ((B.drop s).take (B.length - s - e))
      (A.drop (A.length - e)) := by
  have hA : A = A.take s ++ (A.drop s).take (A.length - s - e) ++ A.drop (A.length - e) := by
    rw [List.append_assoc, ← List.drop_drop.symm.trans rfl]
    sorry
  sorry

end Myers
