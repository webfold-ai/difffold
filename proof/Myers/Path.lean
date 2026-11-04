import Reach
import Script
/-! On the way from `(0,0)` to `(n,m)` an optimal path passes a point at every cost `i` between 0 and
the distance `D`: `∃ (x,y)` with `Split a b x y` and `x + y = i + 2 * lcs (take x a) (take y b)`. -/
open scoped List
namespace Myers

theorem lcs_take_diag {a b : List Nat} {x y p : Nat} (ha : a[x]? = some p) (hb : b[y]? = some p) :
    lcs (a.take (x + 1)) (b.take (y + 1)) = lcs (a.take x) (b.take y) + 1 := by
  rw [take_snoc, take_snoc, ha, hb]; simp only [Option.toList_some]; rw [lcs_suffix]; simp

theorem drop_cons_of_get {a : List Nat} {x p : Nat} (ha : a[x]? = some p) : a.drop x = p :: a.drop (x + 1) := by
  have hx := (List.getElem?_eq_some_iff.mp ha)
  obtain ⟨hlt, hv⟩ := hx
  rw [List.drop_eq_getElem_cons hlt, hv]

/-- One more step along an optimal path. -/
theorem step_aux (a b : List Nat) (i : Nat) (hi : i + 2 * lcs a b < a.length + b.length) :
    ∀ (r x y : Nat), (a.length - x) + (b.length - y) = r → x ≤ a.length → y ≤ b.length →
    Split a b x y → x + y = i + 2 * lcs (a.take x) (b.take y) →
    ∃ x' y', x' ≤ a.length ∧ y' ≤ b.length ∧ Split a b x' y' ∧
      x' + y' = (i + 1) + 2 * lcs (a.take x') (b.take y') := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro x y hr hx hy hs hf
  unfold Split at hs
  -- a move to a later point that does not lower the remaining lcs keeps the point on an optimal path
  have move : ∀ x' y', x ≤ x' → y ≤ y' → x' ≤ a.length → y' ≤ b.length → x' + y' = x + y + 1 →
      lcs (a.drop x) (b.drop y) ≤ lcs (a.drop x') (b.drop y') →
      ∃ x' y', x' ≤ a.length ∧ y' ≤ b.length ∧ Split a b x' y' ∧
        x' + y' = (i + 1) + 2 * lcs (a.take x') (b.take y') := by
    intro x' y' h1 h2 h3 h4 h5 h6
    have m1 := lcs_mono (a.take x) (b.take y) (a.take x') (b.take y')
      (List.take_sublist_take_left h1) (List.take_sublist_take_left h2)
    have sg := split_ge a b x' y'
    refine ⟨x', y', h3, h4, ?_, ?_⟩
    · unfold Split; omega
    · omega
  by_cases hxn : x = a.length
  · -- on the right edge: the only move is down
    have hym : y < b.length := by
      rcases Nat.lt_or_ge y b.length with h | h
      · exact h
      · have hy' : y = b.length := by omega
        subst hxn; subst hy'
        rw [List.take_length, List.take_length] at hf
        omega
    apply move x (y + 1) (Nat.le_refl _) (Nat.le_succ _) hx hym (by omega)
    subst hxn
    rw [List.drop_length]; simp [lcs_nil_left]
  by_cases hym : y = b.length
  · have hxm : x < a.length := by omega
    apply move (x + 1) y (Nat.le_succ _) (Nat.le_refl _) hxm hy (by omega)
    subst hym
    rw [List.drop_length]; simp [lcs_nil_right]
  have hxlt : x < a.length := by omega
  have hylt : y < b.length := by omega
  obtain ⟨p, hp⟩ : ∃ p, a[x]? = some p := ⟨a[x], List.getElem?_eq_getElem hxlt⟩
  obtain ⟨q, hq⟩ : ∃ q, b[y]? = some q := ⟨b[y], List.getElem?_eq_getElem hylt⟩
  by_cases hpq : p = q
  · subst hpq
    -- a matching pair: take the free diagonal step and continue
    have e1 := lcs_take_diag hp hq
    have da := drop_cons_of_get hp
    have db := drop_cons_of_get hq
    have e2 : lcs (a.drop x) (b.drop y) = lcs (a.drop (x + 1)) (b.drop (y + 1)) + 1 := by
      rw [da, db, lcs_cons_eq]
    exact ih ((a.length - (x + 1)) + (b.length - (y + 1))) (by omega) (x + 1) (y + 1) rfl
      (by omega) (by omega)
      (by unfold Split; omega) (by omega)
  · have da := drop_cons_of_get hp
    have db := drop_cons_of_get hq
    have e2 : lcs (a.drop x) (b.drop y) =
        max (lcs (a.drop (x + 1)) (b.drop y)) (lcs (a.drop x) (b.drop (y + 1))) := by
      have := lcs_cons_ne hpq (a.drop (x + 1)) (b.drop (y + 1))
      rw [← da, ← db] at this
      exact this
    rcases Nat.le_total (lcs (a.drop x) (b.drop (y + 1))) (lcs (a.drop (x + 1)) (b.drop y)) with hl | hl
    · exact move (x + 1) y (Nat.le_succ _) (Nat.le_refl _) hxlt hy (by omega) (by omega)
    · exact move x (y + 1) (Nat.le_refl _) (Nat.le_succ _) hx hylt (by omega) (by omega)

theorem path_point (a b : List Nat) : ∀ i, i + 2 * lcs a b ≤ a.length + b.length →
    ∃ x y, x ≤ a.length ∧ y ≤ b.length ∧ Split a b x y ∧ x + y = i + 2 * lcs (a.take x) (b.take y) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨0, 0, Nat.zero_le _, Nat.zero_le _, by unfold Split; simp [lcs_nil_left], by simp [lcs_nil_left]⟩
  | succ i ih =>
    intro h
    obtain ⟨x, y, hx, hy, hs, hf⟩ := ih (by omega)
    exact step_aux a b i (by omega) _ x y rfl hx hy hs hf

end Myers
