import Mapping
/-! Preorder index and depth of a node, from the leftmost-leaf map alone.

For a well formed `la` on `1 .. n`, the ancestors of `u` are the `w > u` with `la w <= u`. `dep` counts them,
`pre u = la u + dep u` is the preorder index of `u`, and `Q u = u + dep u` is the preorder index of the last
node of the subtree of `u`. Two nodes are related by `Anc` exactly when the preorder and postorder
comparisons disagree; this is what lets the mirror image (which reverses the preorder into a postorder)
preserve tree edit mappings. -/
namespace Ted

def cn (p : Nat → Bool) (lo : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => cn p lo k + (if p (lo + k) then 1 else 0)

theorem cn_le (p : Nat → Bool) (lo k : Nat) : cn p lo k ≤ k := by
  induction k with
  | zero => simp [cn]
  | succ k ih => simp only [cn]; split <;> omega

theorem cn_add (p : Nat → Bool) (lo k1 k2 : Nat) : cn p lo (k1 + k2) = cn p lo k1 + cn p (lo + k1) k2 := by
  induction k2 with
  | zero => simp [cn]
  | succ k2 ih =>
    rw [← Nat.add_assoc]
    simp only [cn]
    rw [ih, Nat.add_assoc, Nat.add_assoc]

theorem cn_mono (p q : Nat → Bool) (lo k : Nat)
    (h : ∀ w, lo ≤ w → w < lo + k → p w = true → q w = true) : cn p lo k ≤ cn q lo k := by
  induction k with
  | zero => simp [cn]
  | succ k ih =>
    have ih' := ih (fun w h1 h2 h3 => h w h1 (by omega) h3)
    have hk := h (lo + k) (by omega) (by omega)
    simp only [cn]
    by_cases hp : p (lo + k) = true
    · have := hk hp; simp [hp, this]; omega
    · simp [hp]; split <;> omega

theorem cn_congr (p q : Nat → Bool) (lo k : Nat)
    (h : ∀ w, lo ≤ w → w < lo + k → p w = q w) : cn p lo k = cn q lo k := by
  apply Nat.le_antisymm
  · exact cn_mono p q lo k (fun w h1 h2 h3 => by rw [← h w h1 h2]; exact h3)
  · exact cn_mono q p lo k (fun w h1 h2 h3 => by rw [h w h1 h2]; exact h3)

theorem cn_zero (p : Nat → Bool) (lo k : Nat) (h : ∀ w, lo ≤ w → w < lo + k → p w = false) :
    cn p lo k = 0 := by
  induction k with
  | zero => simp [cn]
  | succ k ih =>
    have := ih (fun w h1 h2 => h w h1 (by omega))
    simp only [cn, this, h (lo + k) (by omega) (by omega)]; simp

def dep (la : Nat → Nat) (n u : Nat) : Nat := cn (fun w => decide (la w ≤ u)) (u + 1) (n - u)
def pre (la : Nat → Nat) (n u : Nat) : Nat := la u + dep la n u
def Qp (la : Nat → Nat) (n u : Nat) : Nat := u + dep la n u

section
variable {la : Nat → Nat} {n : Nat}

theorem dep_le (u : Nat) : dep la n u ≤ n - u := cn_le _ _ _

theorem Qp_le (hu : u ≤ n) : Qp la n u ≤ n := by
  have := dep_le (la := la) (n := n) u; unfold Qp; omega

theorem L_anc (hA : WfL la) {u v : Nat} (huv : u < v) (hvn : v ≤ n) (hanc : la v ≤ u) :
    dep la n v + 1 ≤ dep la n u ∧ dep la n u ≤ dep la n v + (v - u) := by
  have e : n - u = (v - u) + (n - v) := by omega
  have h1 : dep la n u = cn (fun w => decide (la w ≤ u)) (u + 1) (v - u) +
      cn (fun w => decide (la w ≤ u)) (v + 1) (n - v) := by
    unfold dep; rw [e, cn_add]
    have : u + 1 + (v - u) = v + 1 := by omega
    rw [this]
  have h2 : cn (fun w => decide (la w ≤ u)) (v + 1) (n - v) = dep la n v := by
    unfold dep
    apply cn_congr
    intro w hw1 hw2
    have := hA.2 w v
    by_cases hc : la w ≤ v
    · have := this hc (by omega)
      simp only [decide_eq_true_eq, hc, decide_true]
      simp; omega
    · simp only [decide_eq_true_eq, hc, decide_false]
      have : ¬ la w ≤ u := fun h => hc (by omega)
      simp [this]
  have h3 : cn (fun w => decide (la w ≤ u)) (u + 1) (v - u) =
      cn (fun w => decide (la w ≤ u)) (u + 1) (v - u - 1) + 1 := by
    have : v - u = (v - u - 1) + 1 := by omega
    rw [this]; simp only [cn]
    have : u + 1 + (v - u - 1) = v := by omega
    simp [this, hanc]
  have h4 := cn_le (fun w => decide (la w ≤ u)) (u + 1) (v - u - 1)
  rw [h2] at h1
  omega

theorem L_un (hA : WfL la) {u v : Nat} (hu : 1 ≤ u) (huv : u < v) (hvn : v ≤ n) (hun : u < la v) :
    u + dep la n u + 1 ≤ la v + dep la n v := by
  have hlv := (hA.1 v (by omega)).2
  have e : n - u = (la v - 1 - u) + ((v - la v + 1) + (n - v)) := by omega
  have h1 : dep la n u = cn (fun w => decide (la w ≤ u)) (u + 1) (la v - 1 - u) +
      (cn (fun w => decide (la w ≤ u)) (la v) (v - la v + 1) +
        cn (fun w => decide (la w ≤ u)) (v + 1) (n - v)) := by
    unfold dep; rw [e, cn_add, cn_add]
    have e1 : u + 1 + (la v - 1 - u) = la v := by omega
    have e2 : la v + (v - la v + 1) = v + 1 := by omega
    rw [e1, e2]
  have h2 : cn (fun w => decide (la w ≤ u)) (la v) (v - la v + 1) = 0 := by
    apply cn_zero
    intro w hw1 hw2
    have := hA.2 v w (by omega) (by omega)
    simp only [decide_eq_false_iff_not]; omega
  have h3 : cn (fun w => decide (la w ≤ u)) (v + 1) (n - v) ≤ dep la n v := by
    unfold dep
    apply cn_mono
    intro w hw1 hw2 hw3
    simp only [decide_eq_true_eq] at hw3 ⊢; omega
  have h4 := cn_le (fun w => decide (la w ≤ u)) (u + 1) (la v - 1 - u)
  omega

theorem pre_le_Qp (hA : WfL la) {u : Nat} (hu : 1 ≤ u) : pre la n u ≤ Qp la n u := by
  have := (hA.1 u hu).2; unfold pre Qp; omega

theorem pre_pos (hA : WfL la) {u : Nat} (hu : 1 ≤ u) : 1 ≤ pre la n u := by
  have := (hA.1 u hu).1; unfold pre; omega

/-- Ancestor: the preorder index drops and the last preorder index of the subtree grows. -/
theorem P_anc (hA : WfL la) {u v : Nat} (hu : 1 ≤ u) (huv : u < v) (hvn : v ≤ n) (hanc : la v ≤ u) :
    pre la n v < pre la n u ∧ Qp la n u ≤ Qp la n v := by
  have h := L_anc hA huv hvn hanc
  have h2 := hA.2 v u hanc (by omega)
  unfold pre Qp; omega

theorem P_un (hA : WfL la) {u v : Nat} (hu : 1 ≤ u) (huv : u < v) (hvn : v ≤ n) (hun : u < la v) :
    Qp la n u < pre la n v := by
  have := L_un hA hu huv hvn hun
  unfold pre Qp; omega

/-- The descendant relation, read off the preorder: `u` is below `v` iff `u` is in the preorder interval of `v`. -/
theorem anc_iff_pre (hA : WfL la) {u v : Nat} (hu : 1 ≤ u) (hun : u ≤ n) (hv : 1 ≤ v) (hvn : v ≤ n) :
    Anc la u v ↔ pre la n v < pre la n u ∧ pre la n u ≤ Qp la n v := by
  constructor
  · rintro ⟨h1, h2⟩
    have := P_anc hA hu h1 hvn h2
    have := pre_le_Qp hA hu (n := n)
    omega
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_trichotomy u v with h | h | h
    · by_cases hc : la v ≤ u
      · exact ⟨h, hc⟩
      · have := P_un hA hu h hvn (by omega)
        have := pre_le_Qp hA hu (n := n)
        omega
    · subst h; omega
    · by_cases hc : la u ≤ v
      · have := P_anc hA hv h hun hc
        omega
      · have := P_un hA hv h hun (by omega)
        omega

theorem pre_inj (hA : WfL la) {u v : Nat} (hu : 1 ≤ u) (hun : u ≤ n) (hv : 1 ≤ v) (hvn : v ≤ n)
    (h : pre la n u = pre la n v) : u = v := by
  rcases Nat.lt_trichotomy u v with h' | h' | h'
  · by_cases hc : la v ≤ u
    · have := P_anc hA hu h' hvn hc; omega
    · have := P_un hA hu h' hvn (by omega)
      have := pre_le_Qp hA hu (n := n); omega
  · exact h'
  · by_cases hc : la u ≤ v
    · have := P_anc hA hv h' hun hc; omega
    · have := P_un hA hv h' hun (by omega)
      have := pre_le_Qp hA hv (n := n); omega

theorem pre_le_n (hA : WfL la) {u : Nat} (hu : 1 ≤ u) (hun : u ≤ n) : pre la n u ≤ n := by
  have := pre_le_Qp hA hu (n := n); have := Qp_le (la := la) hun; omega

end
end Ted
