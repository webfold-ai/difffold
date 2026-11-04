/-!
# Threshold-pruned alignment DP over an abstract grid

Cells `(i,j)`, `0 <= i <= n`, `0 <= j <= m`. Steps: delete `a_i` (cost `sa i`), insert `b_j`
(cost `sb j`), pair (cost `dd i j`).

* `F`  : TRUE prefix minimum `F*(i,j)` over all paths from `(0,0)`.
* `B`  : TRUE minimum remaining cost `R*(i,j)` over all paths to `(n,m)`.
* `P`  : the threshold DP of `Differ::fill`. A cell's value is computed from KEPT predecessors only
         (a pruned predecessor is `none`), so it may overestimate `F*`. A cell is kept iff
         `value + h i j <= tau`.
* `P'` : `P` with the sub-cost skip of the Rust code: the diagonal candidate (which needs the
         recursive `dist`) is not evaluated when `F_diag + |sa - sb| + h > tau`.

Nothing here assumes `F` is a lower bound for `P`; the theorem states the corrected form:
with `h <= R*`, a cell is kept whenever `F* + R* <= tau`.
-/
namespace Difffold

structure Grid where
  n : Nat
  m : Nat
  sa : Nat → Nat
  sb : Nat → Nat
  dd : Nat → Nat → Nat

namespace Grid
variable (g : Grid)

/-- True prefix minimum `F*`. -/
def F : Nat → Nat → Nat
  | 0, 0 => 0
  | i + 1, 0 => F i 0 + g.sa i
  | 0, j + 1 => F 0 j + g.sb j
  | i + 1, j + 1 =>
      min (min (F i (j + 1) + g.sa i) (F (i + 1) j + g.sb j)) (F i j + g.dd i j)

/-- True minimum remaining cost `R*`. -/
def B (i j : Nat) : Nat :=
  if hi : i < g.n then
    if hj : j < g.m then
      min (min (g.sa i + B (i + 1) j) (g.sb j + B i (j + 1))) (g.dd i j + B (i + 1) (j + 1))
    else g.sa i + B (i + 1) j
  else if hj : j < g.m then g.sb j + B i (j + 1) else 0
termination_by (g.n - i) + (g.m - j)

theorem B_end : g.B g.n g.m = 0 := by
  rw [B]; simp

theorem B_del {i j : Nat} (hi : i < g.n) (hj : j ≤ g.m) : g.B i j ≤ g.sa i + g.B (i + 1) j := by
  rw [B]; simp only [hi, dite_true]
  by_cases h : j < g.m
  · simp only [h, dite_true]; omega
  · simp only [h, dite_false]; omega

theorem B_ins {i j : Nat} (hi : i ≤ g.n) (hj : j < g.m) : g.B i j ≤ g.sb j + g.B i (j + 1) := by
  rw [B]; simp only [hj, dite_true]
  by_cases h : i < g.n
  · simp only [h, dite_true]; omega
  · simp only [h, dite_false, hj, dite_true]; omega

theorem B_pair {i j : Nat} (hi : i < g.n) (hj : j < g.m) :
    g.B i j ≤ g.dd i j + g.B (i + 1) (j + 1) := by
  rw [B]; simp only [hi, hj, dite_true]; omega

theorem F_del (i j : Nat) : g.F (i + 1) j ≤ g.F i j + g.sa i := by
  cases j <;> simp [F] <;> omega

theorem F_ins (i j : Nat) : g.F i (j + 1) ≤ g.F i j + g.sb j := by
  cases i <;> simp [F] <;> omega

theorem F_pair (i j : Nat) : g.F (i + 1) (j + 1) ≤ g.F i j + g.dd i j := by
  simp [F]; omega

/-! ### The pruned DP -/

end Grid

def omin : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

def oadd (o : Option Nat) (c : Nat) : Option Nat := o.map (· + c)

/-- Keep a cell iff its value plus the heuristic fits under the threshold. -/
def keep (h : Nat → Nat → Nat) (tau i j : Nat) : Option Nat → Option Nat
  | none => none
  | some v => if v + h i j ≤ tau then some v else none

namespace Grid
variable (g : Grid) (h : Nat → Nat → Nat) (tau : Nat)

def P : Nat → Nat → Option Nat
  | 0, 0 => keep h tau 0 0 (some 0)
  | i + 1, 0 => keep h tau (i + 1) 0 (oadd (P i 0) (g.sa i))
  | 0, j + 1 => keep h tau 0 (j + 1) (oadd (P 0 j) (g.sb j))
  | i + 1, j + 1 =>
      keep h tau (i + 1) (j + 1)
        (omin (omin (oadd (P i (j + 1)) (g.sa i)) (oadd (P (i + 1) j) (g.sb j)))
          (oadd (P i j) (g.dd i j)))

end Grid

theorem keep_some {h tau i j o v} (hk : keep h tau i j o = some v) : o = some v ∧ v + h i j ≤ tau := by
  cases o with
  | none => simp [keep] at hk
  | some w =>
    simp only [keep] at hk
    split at hk
    · cases hk; exact ⟨rfl, by assumption⟩
    · cases hk

theorem keep_of {h tau i j v} (hv : v + h i j ≤ tau) : keep h tau i j (some v) = some v := by
  simp [keep, hv]

def Ge (m : Nat) (o : Option Nat) : Prop := ∀ v, o = some v → m ≤ v

theorem omin_ge {m a b} (ha : Ge m a) (hb : Ge m b) : Ge m (omin a b) := by
  intro v hv
  cases a <;> cases b <;> simp [omin] at hv
  · exact hb _ (by simp [hv])
  · exact ha _ (by simp [hv])
  · subst hv; have := ha _ rfl; have := hb _ rfl; omega

theorem omin_eq_left {m a b} (ha : a = some m) (hb : Ge m b) : omin a b = some m := by
  subst ha; cases b with
  | none => rfl
  | some w => have := hb w rfl; simp [omin]; omega

theorem omin_eq_right {m a b} (ha : Ge m a) (hb : b = some m) : omin a b = some m := by
  subst hb; cases a with
  | none => rfl
  | some w => have := ha w rfl; simp [omin]; omega

theorem oadd_ge {m c o F'} (ho : ∀ v, o = some v → F' ≤ v) (hc : m ≤ F' + c) : Ge m (oadd o c) := by
  intro v hv
  cases o with
  | none => simp [oadd] at hv
  | some w => have := ho w rfl; simp [oadd] at hv; omega

theorem oadd_eq {m c o F'} (ho : o = some F') (hc : F' + c = m) : oadd o c = some m := by
  subst ho; simp [oadd, hc]

namespace Grid
variable {g : Grid} {h : Nat → Nat → Nat} {tau : Nat}

/-- A kept value is the cost of a real path, hence at least `F*`. -/
theorem P_ge : ∀ i j v, g.P h tau i j = some v → g.F i j ≤ v := by
  intro i
  induction i with
  | zero =>
    intro j
    induction j with
    | zero => intro v hv; simp [P] at hv; have := keep_some hv; simp [F] at * <;> omega
    | succ j ih =>
      intro v hv
      simp only [P] at hv
      obtain ⟨h1, -⟩ := keep_some hv
      cases hp : g.P h tau 0 j with
      | none => simp [hp, oadd] at h1
      | some w => have := ih w hp; simp [hp, oadd] at h1; simp [F]; omega
  | succ i ihi =>
    intro j
    induction j with
    | zero =>
      intro v hv
      simp only [P] at hv
      obtain ⟨h1, -⟩ := keep_some hv
      cases hp : g.P h tau i 0 with
      | none => simp [hp, oadd] at h1
      | some w => have := ihi 0 w hp; simp [hp, oadd] at h1; simp [F]; omega
    | succ j ihj =>
      intro v hv
      simp only [P] at hv
      obtain ⟨h1, -⟩ := keep_some hv
      simp only [F]
      cases h2 : g.P h tau i (j + 1) <;> cases h3 : g.P h tau (i + 1) j <;>
        cases h4 : g.P h tau i j <;> simp [h2, h3, h4, oadd, omin] at h1 <;>
        (try have := ihi (j + 1) _ h2) <;> (try have := ihj _ h3) <;> (try have := ihi j _ h4) <;> omega


/-- **prune_sound (cell form).** Let `h <= R*` (admissible). If `F*(i,j) + R*(i,j) <= tau`, i.e. the
cell lies on some path of total cost `<= tau`, then the pruned DP KEEPS the cell and its value is
exactly the true prefix minimum `F*(i,j)`. (The value is computed from kept predecessors only; the
proof shows the optimal predecessor is itself on a path of cost `<= tau`, so it is kept.) -/
theorem prune_sound (hadm : ∀ i j, i ≤ g.n → j ≤ g.m → h i j ≤ g.B i j) :
    ∀ i j, i ≤ g.n → j ≤ g.m → g.F i j + g.B i j ≤ tau → g.P h tau i j = some (g.F i j) := by
  intro i
  induction i with
  | zero =>
    intro j
    induction j with
    | zero =>
      intro _ _ ht
      have := hadm 0 0 (by omega) (by omega)
      simp only [P, F] at *; exact keep_of (by omega)
    | succ j ih =>
      intro hi hj ht
      have hb := g.B_ins (i := 0) hi (by omega : j < g.m)
      have ih' := ih hi (by omega) (by simp only [F] at *; omega)
      have := hadm 0 (j + 1) hi hj
      have e : g.F 0 (j + 1) = g.F 0 j + g.sb j := by rw [F]
      simp only [P]
      rw [ih']
      show keep h tau 0 (j + 1) (some (g.F 0 j + g.sb j)) = _
      rw [e]; exact keep_of (by omega)
  | succ i ihi =>
    intro j
    induction j with
    | zero =>
      intro hi hj ht
      have hb := g.B_del (i := i) (j := 0) (by omega) hj
      have ih' := ihi 0 (by omega) hj (by simp only [F] at *; omega)
      have := hadm (i + 1) 0 hi hj
      have e : g.F (i + 1) 0 = g.F i 0 + g.sa i := by rw [F]
      simp only [P]
      rw [ih']
      show keep h tau (i + 1) 0 (some (g.F i 0 + g.sa i)) = _
      rw [e]; exact keep_of (by omega)
    | succ j ihj =>
      intro hi hj ht
      have hA := g.B_del (i := i) (j := j + 1) (by omega) hj
      have hB := g.B_ins (i := i + 1) (j := j) hi (by omega)
      have hC := g.B_pair (i := i) (j := j) (by omega) (by omega)
      have hh := hadm (i + 1) (j + 1) hi hj
      have fA := g.F_del i (j + 1)
      have fB := g.F_ins (i + 1) j
      have fC := g.F_pair i j
      have hmin : g.F (i + 1) (j + 1) = min (min (g.F i (j + 1) + g.sa i) (g.F (i + 1) j + g.sb j)) (g.F i j + g.dd i j) := by
        rw [F]
      have gA : Ge (g.F (i + 1) (j + 1)) (oadd (g.P h tau i (j + 1)) (g.sa i)) :=
        oadd_ge (P_ge _ _) (by omega)
      have gB : Ge (g.F (i + 1) (j + 1)) (oadd (g.P h tau (i + 1) j) (g.sb j)) :=
        oadd_ge (P_ge _ _) (by omega)
      have gC : Ge (g.F (i + 1) (j + 1)) (oadd (g.P h tau i j) (g.dd i j)) :=
        oadd_ge (P_ge _ _) (by omega)
      have inner : omin (omin (oadd (g.P h tau i (j + 1)) (g.sa i)) (oadd (g.P h tau (i + 1) j) (g.sb j)))
          (oadd (g.P h tau i j) (g.dd i j)) = some (g.F (i + 1) (j + 1)) := by
        by_cases e1 : g.F (i + 1) (j + 1) = g.F i (j + 1) + g.sa i
        · have p := ihi (j + 1) (by omega) hj (by omega)
          exact omin_eq_left (omin_eq_left (oadd_eq p e1.symm) gB) gC
        · by_cases e2 : g.F (i + 1) (j + 1) = g.F (i + 1) j + g.sb j
          · have p := ihj hi (by omega) (by omega)
            exact omin_eq_left (omin_eq_right gA (oadd_eq p e2.symm)) gC |> fun _ =>
              omin_eq_left (omin_eq_right gA (oadd_eq p e2.symm)) gC
          · have e3 : g.F (i + 1) (j + 1) = g.F i j + g.dd i j := by omega
            have p := ihi j (by omega) (by omega) (by omega)
            exact omin_eq_right (omin_ge gA gB) (oadd_eq p e3.symm)
      simp only [P]
      rw [inner]
      exact keep_of (by omega)

/-- A cell on some path of cost `<= tau` is kept. -/
theorem path_cells_kept (hadm : ∀ i j, i ≤ g.n → j ≤ g.m → h i j ≤ g.B i j)
    {i j} (hi : i ≤ g.n) (hj : j ≤ g.m) (ht : g.F i j + g.B i j ≤ tau) :
    (g.P h tau i j).isSome := by
  rw [prune_sound hadm i j hi hj ht]; rfl

end Grid
end Difffold
