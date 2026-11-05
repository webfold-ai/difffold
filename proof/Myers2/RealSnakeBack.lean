import RealDefs
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem rev_vals (l : List U32) : (vals l).reverse = vals l.reverse := by simp [vals, List.map_reverse]

theorem cpre_suffix (A' B' : List U32) (l : Nat) (hl : l ≤ min A'.length B'.length)
    (h2 : A'.drop (A'.length - l) = B'.drop (B'.length - l))
    (h3 : l = min A'.length B'.length ∨
      (l < min A'.length B'.length ∧ ∃ p q, A'[A'.length - 1 - l]? = some p ∧ B'[B'.length - 1 - l]? = some q ∧ p ≠ q)) :
    Myers.cpre (vals A').reverse (vals B').reverse = l := by
  apply Myers.cpre_char
  · simpa [vals] using hl
  · rw [List.take_reverse, List.take_reverse]
    have e1 : (vals A').length = A'.length := by simp [vals]
    have e2 : (vals B').length = B'.length := by simp [vals]
    rw [e1, e2]
    have := congrArg (fun t => (vals t).reverse) h2
    simp only [vals, List.map_drop] at this ⊢
    simpa using this
  · rcases h3 with h3 | ⟨hlt, p, q, hp, hq, hpq⟩
    · left; simpa [vals] using h3
    · right
      refine ⟨p.val, q.val, ?_, ?_, ?_⟩
      · rw [List.getElem?_reverse (by simp [vals]; omega)]; simp [vals, List.getElem?_map, hp]
      · rw [List.getElem?_reverse (by simp [vals]; omega)]; simp [vals, List.getElem?_map, hq]
      · intro e; exact hpq (UScalar.eq_of_val_eq e)

theorem snake_back_spec (a b : Slice U32) (x y : I32) (hx : 0 ≤ x.val) (hy : 0 ≤ y.val)
    (ha : a.val.length ≤ I32.max) (hb : b.val.length ≤ I32.max) :
    lines.snake_back a b x y ⦃ r => 0 ≤ r.val ∧ x.val + r.val ≤ max x.val a.val.length ∧
      y.val + r.val ≤ max y.val b.val.length ∧
      r.val = Myers.snake (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val ⦄ := by
  have hn := hlen a ha
  have hm := hlen b hb
  have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
  have h1 := Myers.snake_le (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val
  have h2 := Myers.snake_le_y (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val
  simp only [List.length_reverse, vals, List.length_map] at h1 h2
  have hxn : (x.val.toNat : Int) = x.val := Int.toNat_of_nonneg hx
  unfold lines.snake_back
  step*
  all_goals (trace_state; sorry)

end difffold_myers_extract
