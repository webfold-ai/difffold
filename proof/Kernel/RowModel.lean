import CellValue
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

/-- A model cell encoded as `INF` is pruned. -/
theorem enc_inf_none (g : Grid) (h : Nat → Nat → Nat) (tau i j : Nat) (htau : tau < INFn)
    (he : enc (g.P h tau i j) = INFn) : g.P h tau i j = none := by
  cases hp : g.P h tau i j with
  | none => rfl
  | some x =>
    have := P_le_tau g h tau i j x hp
    rw [hp] at he; simp only [enc] at he; omega

/-- A model cell whose encoding is at least `INF` is pruned. -/
theorem enc_ge_none (g : Grid) (h : Nat → Nat → Nat) (tau i j : Nat) (htau : tau < INFn)
    (he : INFn ≤ enc (g.P h tau i j)) : g.P h tau i j = none := by
  cases hp : g.P h tau i j with
  | none => rfl
  | some x =>
    have := P_le_tau g h tau i j x hp
    rw [hp] at he; simp only [enc] at he; omega

/-- If the three neighbours of a cell are pruned, so is the cell. -/
theorem P_cell_none (g : Grid) (h : Nat → Nat → Nat) (tau i j : Nat) (hi : 1 ≤ i)
    (hup : g.P h tau (i - 1) j = none)
    (hlf : j = 0 ∨ g.P h tau i (j - 1) = none)
    (hdg : j = 0 ∨ g.P h tau (i - 1) (j - 1) = none) : g.P h tau i j = none := by
  rw [P_cell g h tau i j hi, hup]
  rcases hlf with hz | hl <;> rcases hdg with hz' | hd
  · simp [hz, oadd, omin, keep]
  · simp [hz, hd, oadd, omin, keep]
  · simp [hl, hz', oadd, omin, keep]
  · by_cases hj : j = 0 <;> simp [hj, hl, hd, oadd, omin, keep]

/-- Below the previous row's span, every cell of the next row is pruned. -/
theorem P_below_none (g : Grid) (h : Nat → Nat → Nat) (tau i plo : Nat) (hi : 1 ≤ i)
    (hprev : ∀ j', j' < plo → g.P h tau (i - 1) j' = none) :
    ∀ j', j' < plo → g.P h tau i j' = none := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact P_cell_none g h tau i 0 hi (hprev 0 hj) (Or.inl rfl) (Or.inl rfl)
  | succ k ih =>
    intro hj
    exact P_cell_none g h tau i (k + 1) hi (hprev _ hj) (Or.inr (by simpa using ih (by omega)))
      (Or.inr (by simpa using hprev k (by omega)))

/-- Past a pruned cell, with the row above also pruned from there, the rest of the row is pruned. -/
theorem P_tail_none (g : Grid) (h : Nat → Nat → Nat) (tau i J m : Nat) (hi : 1 ≤ i) (hJ : 1 ≤ J)
    (hprev : ∀ j', J - 1 ≤ j' → j' ≤ m → g.P h tau (i - 1) j' = none)
    (hJ1 : g.P h tau i (J - 1) = none) :
    ∀ j', J ≤ j' → j' ≤ m → g.P h tau i j' = none := by
  intro j hj hjm
  induction j, hj using Nat.le_induction with
  | base =>
    exact P_cell_none g h tau i J hi (hprev J (by omega) hjm) (Or.inr hJ1)
      (Or.inr (hprev (J - 1) le_rfl (by omega)))
  | succ k hk ih =>
    have ih' := ih (by omega)
    exact P_cell_none g h tau i (k + 1) hi (hprev _ (by omega) hjm) (Or.inr (by simpa using ih'))
      (Or.inr (hprev k (by omega) (by omega)))

end difffold_kernel_extract
