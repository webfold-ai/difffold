import Difffold.Prune
/-!
# Threshold decision, minimum-cost result, widening, and the sub-cost skip
-/
namespace Difffold
namespace Grid
variable {g : Grid} {h : Nat → Nat → Nat} {tau : Nat}

/-- Every kept value fits under the threshold. -/
theorem P_fits : ∀ i j v, g.P h tau i j = some v → v + h i j ≤ tau := by
  intro i j v hv
  cases i <;> cases j <;> simp only [P] at hv <;> exact (keep_some hv).2

/-- **threshold decision + minimum result.** With `h` admissible, the final cell holds a result
iff the true minimum `F*(n,m)` is `<= tau`; and then the result IS the true minimum. -/
theorem decision (hadm : ∀ i j, i ≤ g.n → j ≤ g.m → h i j ≤ g.B i j) :
    (g.P h tau g.n g.m).isSome ↔ g.F g.n g.m ≤ tau := by
  constructor
  · intro hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    have h1 := P_fits _ _ _ hv
    have h2 := P_ge _ _ _ hv
    omega
  · intro hle
    exact path_cells_kept hadm (Nat.le_refl _) (Nat.le_refl _) (by rw [B_end]; omega)

theorem result_is_min (hadm : ∀ i j, i ≤ g.n → j ≤ g.m → h i j ≤ g.B i j) {v}
    (hv : g.P h tau g.n g.m = some v) : v = g.F g.n g.m ∧ v ≤ tau := by
  have h1 := P_fits _ _ _ hv
  have h2 := P_ge _ _ _ hv
  have h3 := prune_sound (tau := tau) hadm g.n g.m (Nat.le_refl _) (Nat.le_refl _) (by rw [B_end]; omega)
  rw [hv] at h3
  have := Option.some.inj h3
  omega

/-- No result means every path costs more than `tau`. -/
theorem none_gt (hadm : ∀ i j, i ≤ g.n → j ≤ g.m → h i j ≤ g.B i j)
    (hn : g.P h tau g.n g.m = none) : tau < g.F g.n g.m := by
  refine Nat.lt_of_not_le ?_
  intro hc
  have := (decision (tau := tau) hadm).2 (by omega)
  rw [hn] at this; simp at this

/-! ### Threshold widening -/

/-- `Differ::align_mid` loop: try `tau`, on failure widen to `max (2 tau) (tau + 1)`. Fuel models
the unbounded `loop`. -/
def search (g : Grid) (h : Nat → Nat → Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, tau =>
      match g.P h tau g.n g.m with
      | some v => some v
      | none => search g h k (max (2 * tau) (tau + 1))

theorem search_min (hadm : ∀ i j, i ≤ g.n → j ≤ g.m → h i j ≤ g.B i j) :
    ∀ k tau v, search g h k tau = some v → v = g.F g.n g.m := by
  intro k
  induction k with
  | zero => intro tau v hv; simp [search] at hv
  | succ k ih =>
    intro tau v hv
    simp only [search] at hv
    split at hv
    · rename_i w hw
      cases hv
      exact (result_is_min hadm hw).1
    · exact ih _ _ hv

/-- **termination of widening.** If `F*(n,m) <= tau + k`, the loop returns within `k + 1` rounds. -/
theorem search_total (hadm : ∀ i j, i ≤ g.n → j ≤ g.m → h i j ≤ g.B i j) :
    ∀ k tau, g.F g.n g.m ≤ tau + k → (search g h (k + 1) tau).isSome := by
  intro k
  induction k with
  | zero =>
    intro tau hle
    have := (decision (tau := tau) hadm).2 (by omega)
    simp only [search]
    cases hp : g.P h tau g.n g.m with
    | none => rw [hp] at this; simp at this
    | some v => rfl
  | succ k ih =>
    intro tau hle
    simp only [search]
    cases hp : g.P h tau g.n g.m with
    | some v => rfl
    | none =>
      have := none_gt hadm hp
      exact ih _ (by omega)

/-! ### The sub-cost skip -/

def adiff (a b : Nat) : Nat := (a - b) + (b - a)

def skipDiag (h : Nat → Nat → Nat) (tau i j : Nat) (sa sb dd : Nat) : Option Nat → Option Nat
  | none => none
  | some dg => if dg + adiff sa sb + h i j ≤ tau then some (dg + dd) else none

/-- `P` with the sub-cost skip: the diagonal candidate (the recursive `dist`) is not evaluated
when `F_diag + |sa - sb| + h > tau`. -/
def P2 (g : Grid) (h : Nat → Nat → Nat) (tau : Nat) : Nat → Nat → Option Nat
  | 0, 0 => keep h tau 0 0 (some 0)
  | i + 1, 0 => keep h tau (i + 1) 0 (oadd (P2 g h tau i 0) (g.sa i))
  | 0, j + 1 => keep h tau 0 (j + 1) (oadd (P2 g h tau 0 j) (g.sb j))
  | i + 1, j + 1 =>
      keep h tau (i + 1) (j + 1)
        (omin (omin (oadd (P2 g h tau i (j + 1)) (g.sa i)) (oadd (P2 g h tau (i + 1) j) (g.sb j)))
          (skipDiag h tau (i + 1) (j + 1) (g.sa i) (g.sb j) (g.dd i j) (P2 g h tau i j)))

theorem keep_omin_skip (x : Option Nat) (c i j : Nat) (hc : tau < c + h i j) :
    keep h tau i j (omin x (some c)) = keep h tau i j x := by
  cases x with
  | none => simp [omin, keep]; omega
  | some w =>
    simp only [omin, keep]
    by_cases hw : w ≤ c
    · simp [Nat.min_eq_left hw]
    · have : min w c = c := Nat.min_eq_right (by omega)
      rw [this]
      have h1 : ¬ (c + h i j ≤ tau) := by omega
      have h2 : ¬ (w + h i j ≤ tau) := by omega
      simp [h1, h2]

/-- **skip_sound.** Because `dd >= |sa - sb|` (the size lower bound), skipping the recursive
sub-cost never changes a cell's value or its keep/prune status. -/
theorem skip_sound (hdd : ∀ i j, g.sa i ≤ g.sb j + g.dd i j ∧ g.sb j ≤ g.sa i + g.dd i j) :
    ∀ i j, P2 g h tau i j = g.P h tau i j := by
  intro i
  induction i with
  | zero =>
    intro j
    induction j with
    | zero => simp [P2, P]
    | succ j ih => simp only [P2, P, ih]
  | succ i ihi =>
    intro j
    induction j with
    | zero => simp only [P2, P, ihi]
    | succ j ihj =>
      simp only [P2, P, ihi, ihj]
      cases hp : g.P h tau i j with
      | none => simp [skipDiag, oadd, omin]
      | some dg =>
        simp only [skipDiag, oadd, Option.map_some]
        by_cases hc : dg + adiff (g.sa i) (g.sb j) + h (i + 1) (j + 1) ≤ tau
        · simp [hc]
        · have hd := hdd i j
          simp only [hc, if_false]
          have hx : ∀ X : Option Nat, omin X none = X := by intro X; cases X <;> rfl
          rw [hx]
          rw [keep_omin_skip _ (dg + g.dd i j) (i + 1) (j + 1) (by unfold adiff at hc; omega)]

end Grid
end Difffold
