import Mono
/-! What the banded forest-distance table must hold, as a statement about the true distance `Ted.D`.

A window starts at the left ends `li` of the first tree and `lj` of the second. Its cell `(p, q)` is the true
distance `Dw p q` between the forests of the first `p` and `q` nodes of the window. With `δ = |li - lj|` and
threshold `t`, a stored value `v` for a cell is *ok* (`FOK`) when it never undercuts `min (Dw p q) (t + 1)`,
never exceeds `t + 1`, and is exact whenever `Dw p q + δ <= t`. The offset `δ` is the budget the context has
already spent on the position difference of the two window starts. -/
namespace Ted
variable {la lb : Nat → Nat} {ren : Nat → Nat → Nat}

def Dw (la lb : Nat → Nat) (ren : Nat → Nat → Nat) (li lj p q : Nat) : Nat :=
  D la lb ren li (li + p - 1) lj (lj + q - 1)

/-- The distance of the two subtrees rooted at `x` and `y`. -/
def TD (la lb : Nat → Nat) (ren : Nat → Nat → Nat) (x y : Nat) : Nat := D la lb ren (la x) x (lb y) y

def FOK (t δ D v : Nat) : Prop := min D (t + 1) ≤ v ∧ v ≤ t + 1 ∧ (D + δ ≤ t → v = D)

theorem Dw_size {li lj : Nat} (hli : 1 ≤ li) (hlj : 1 ≤ lj) (p q : Nat) :
    p ≤ q + Dw la lb ren li lj p q ∧ q ≤ p + Dw la lb ren li lj p q ∧
      Dw la lb ren li lj p q ≤ p + q := by
  have := D_size la lb ren _ li (li + p - 1) lj (lj + q - 1) hli hlj rfl
  unfold Dw
  omega

/-- A cell outside the band holds `t + 1` and that is ok. -/
theorem fok_out {t δ li lj p q : Nat} (hli : 1 ≤ li) (hlj : 1 ≤ lj) (h : ¬ (p ≤ q + t ∧ q ≤ p + t)) :
    FOK t δ (Dw la lb ren li lj p q) (t + 1) := by
  have := Dw_size (la := la) (lb := lb) (ren := ren) hli hlj p q
  unfold FOK; omega

theorem leaf_arith {t δ D1 D2 D3 r v1 v2 v3 : Nat} (h1 : FOK t δ D1 v1) (h2 : FOK t δ D2 v2)
    (h3 : FOK t δ D3 v3) :
    FOK t δ (min (min (D1 + 1) (D2 + 1)) (D3 + r)) (min (min (min (v1 + 1) (v2 + 1)) (v3 + r)) (t + 1)) := by
  unfold FOK at *
  omega

theorem nonleaf_arith {t δ δ' D1 D2 D3 T v1 v2 v3 tv : Nat} (h1 : FOK t δ D1 v1) (h2 : FOK t δ D2 v2)
    (h3 : FOK t δ D3 v3) (hT : min T (t + 1) ≤ tv ∧ tv ≤ t + 1 ∧ (T + δ' ≤ t → tv = T))
    (hbud : δ' ≤ D3 + δ) :
    FOK t δ (min (min (D1 + 1) (D2 + 1)) (D3 + T)) (min (min (min (v1 + 1) (v2 + 1)) (v3 + tv)) (t + 1)) := by
  unfold FOK at *
  omega

/-- The cell recurrence on a cell of the left path of both windows (`lml x = li`, `lml y = lj`). -/
theorem cell_truth_leaf (hA : WfL la) (hB : WfL lb) {t δ li lj p q : Nat} (hli : 1 ≤ li) (hlj : 1 ≤ lj)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hlx : la (li + p - 1) = li) (hly : lb (lj + q - 1) = lj)
    {vdel vins vdg : Nat}
    (h1 : FOK t δ (Dw la lb ren li lj (p - 1) q) vdel)
    (h2 : FOK t δ (Dw la lb ren li lj p (q - 1)) vins)
    (h3 : FOK t δ (Dw la lb ren li lj (p - 1) (q - 1)) vdg) :
    FOK t δ (Dw la lb ren li lj p q)
      (min (min (min (vdel + 1) (vins + 1)) (vdg + ren (li + p - 1) (lj + q - 1))) (t + 1)) := by
  have hx : ¬ (li + p - 1 < li ∨ li + p - 1 = 0) := by omega
  have hy : ¬ (lj + q - 1 < lj ∨ lj + q - 1 = 0) := by omega
  have hc : clampL li (li + p - 1) (la (li + p - 1)) = li ∧ clampL lj (lj + q - 1) (lb (lj + q - 1)) = lj := by
    unfold clampL; omega
  have hD := D_leaf la lb ren li (li + p - 1) lj (lj + q - 1) hx hy hc
  have e1 : li + p - 1 - 1 = li + (p - 1) - 1 := by omega
  have e2 : lj + q - 1 - 1 = lj + (q - 1) - 1 := by omega
  have key := leaf_arith (r := ren (li + p - 1) (lj + q - 1)) h1 h2 h3
  unfold Dw at key ⊢
  rw [e1, e2] at hD
  rw [hD]
  exact key

def adf (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- The cell recurrence on a cell whose last trees do not both start at the window starts. -/
theorem cell_truth_nonleaf (hA : WfL la) (hB : WfL lb) {t li lj p q : Nat} (hli : 1 ≤ li) (hlj : 1 ≤ lj)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcA : Closed la li (li + p - 1)) (hcB : Closed lb lj (lj + q - 1))
    (hn : ¬ (la (li + p - 1) = li ∧ lb (lj + q - 1) = lj))
    {vdel vins vs tv : Nat}
    (h1 : FOK t (adf li lj) (Dw la lb ren li lj (p - 1) q) vdel)
    (h2 : FOK t (adf li lj) (Dw la lb ren li lj p (q - 1)) vins)
    (h3 : FOK t (adf li lj) (Dw la lb ren li lj (la (li + p - 1) - li) (lb (lj + q - 1) - lj)) vs)
    (hT : min (TD la lb ren (li + p - 1) (lj + q - 1)) (t + 1) ≤ tv ∧ tv ≤ t + 1 ∧
      (TD la lb ren (li + p - 1) (lj + q - 1) + adf (la (li + p - 1)) (lb (lj + q - 1)) ≤ t →
        tv = TD la lb ren (li + p - 1) (lj + q - 1))) :
    FOK t (adf li lj) (Dw la lb ren li lj p q)
      (min (min (min (vdel + 1) (vins + 1)) (vs + tv)) (t + 1)) := by
  have hx : ¬ (li + p - 1 < li ∨ li + p - 1 = 0) := by omega
  have hy : ¬ (lj + q - 1 < lj ∨ lj + q - 1 = 0) := by omega
  have hlx1 : li ≤ la (li + p - 1) := hcA _ (by omega) (Nat.le_refl _)
  have hlx2 : la (li + p - 1) ≤ li + p - 1 := (hA.1 _ (by omega)).2
  have hly1 : lj ≤ lb (lj + q - 1) := hcB _ (by omega) (Nat.le_refl _)
  have hly2 : lb (lj + q - 1) ≤ lj + q - 1 := (hB.1 _ (by omega)).2
  have hcl : clampL li (li + p - 1) (la (li + p - 1)) = la (li + p - 1) := by unfold clampL; omega
  have hcl' : clampL lj (lj + q - 1) (lb (lj + q - 1)) = lb (lj + q - 1) := by unfold clampL; omega
  have hc : ¬ (clampL li (li + p - 1) (la (li + p - 1)) = li ∧ clampL lj (lj + q - 1) (lb (lj + q - 1)) = lj) := by
    rw [hcl, hcl']; exact hn
  have hD := D_nonleaf la lb ren li (li + p - 1) lj (lj + q - 1) hx hy hc
  rw [hcl, hcl'] at hD
  have e1 : li + p - 1 - 1 = li + (p - 1) - 1 := by omega
  have e2 : lj + q - 1 - 1 = lj + (q - 1) - 1 := by omega
  have e3 : la (li + p - 1) - 1 = li + (la (li + p - 1) - li) - 1 := by omega
  have e4 : lb (lj + q - 1) - 1 = lj + (lb (lj + q - 1) - lj) - 1 := by omega
  have hsz := Dw_size (la := la) (lb := lb) (ren := ren) hli hlj (la (li + p - 1) - li) (lb (lj + q - 1) - lj)
  have hbud : adf (la (li + p - 1)) (lb (lj + q - 1)) ≤
      Dw la lb ren li lj (la (li + p - 1) - li) (lb (lj + q - 1) - lj) + adf li lj := by
    unfold adf; split <;> split <;> omega
  have key := nonleaf_arith (δ' := adf (la (li + p - 1)) (lb (lj + q - 1))) h1 h2 h3 hT hbud
  unfold Dw at key ⊢
  rw [e1, e2, e3, e4] at hD
  rw [hD]
  unfold Dw at hbud
  exact key

end Ted
