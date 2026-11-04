import Reach
/-! Completeness of the furthest-reaching recurrence: every point within `d` edits on diagonal `k` has
`x ≤ F a b d k`. -/
open scoped List
namespace Myers

theorem snake_max_int (a b : List Nat) (x : Nat) (z : Int) (y : Nat)
    (hy : (y : Int) = z + (snake a b x z : Int)) (p : Nat)
    (h1 : a[x + snake a b x z]? = some p) (h2 : b[y]? = some p) : False := by
  by_cases hz : z < 0
  · have : snake a b x z = 0 := by unfold snake; rw [if_pos (Or.inl hz)]
    rw [this] at hy; omega
  · obtain ⟨z0, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ z)
    have hy' : y = z0 + snake a b x z0 := by omega
    subst hy'
    exact snake_max a b x z0 p h1 h2

/-- The point `F` reaches is the end of a maximal run: no further matching pair. -/
theorem F_max (a b : List Nat) (d : Nat) (k : Int) (y : Nat) (hy : (y : Int) = (F a b d k : Int) - k)
    (p : Nat) (h1 : a[F a b d k]? = some p) (h2 : b[y]? = some p) : False := by
  cases d with
  | zero =>
    rw [F_zero] at hy h1
    exact snake_max_int a b 0 (-k) y (by omega) p (by simpa using h1) h2
  | succ d =>
    rw [F_succ] at hy h1
    exact snake_max_int a b (X0 a b d k) ((X0 a b d k : Nat) - k) y (by omega) p h1 h2

def Compl (a b : List Nat) (d : Nat) : Prop :=
  ∀ (x y : Nat) (k : Int), Dom d k → (x : Int) - y = k → Reach a b x y d → x ≤ F a b d k

theorem compl_gen (a b : List Nat) (d : Nat) (hprev : ∀ d', d = d' + 1 → Compl a b d') : Compl a b d := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
  intro y k hk hxy hr
  cases x with
  | zero => exact Nat.zero_le _
  | succ x' =>
  cases y with
  | zero => have := F_ge a b d k hk; push_cast at hxy; omega
  | succ y' =>
  by_cases hd : ∃ p, a[x']? = some p ∧ b[y']? = some p
  · obtain ⟨p, ha, hb⟩ := hd
    have hr' := reach_drop_diag hr ha hb
    have h1 := ih x' (Nat.lt_succ_self _) y' k hk (by push_cast at hxy; omega) hr'
    rcases Nat.lt_or_ge x' (F a b d k) with hlt | hge
    · omega
    · have heq : x' = F a b d k := by omega
      exfalso
      apply F_max a b d k y' (by push_cast at hxy; omega) p
      · rw [← heq]; exact ha
      · exact hb
  · cases d with
    | zero =>
      exfalso
      obtain ⟨h1, h2, h3⟩ := hk
      push_cast at hxy h1 h2
      rcases reach_drop_step hr hd with h | h
      · have := lcs_take_le_left a b x' (y' + 1); omega
      · have := lcs_take_le_right a b (x' + 1) y'; omega
    | succ d' =>
      have hF : X0 a b d' k ≤ F a b (d' + 1) k := by rw [F_succ]; omega
      rcases reach_drop_step hr hd with h | h
      · have hr2 : Reach a b x' (y' + 1) d' := by unfold Reach; omega
        have hb2 := reach_bound hr2
        have hdom : Dom d' (k - 1) := by
          obtain ⟨h1, h2, h3⟩ := hk
          unfold Dom; push_cast at hxy h1 h2 h3 ⊢; omega
        have := hprev d' rfl x' (y' + 1) (k - 1) hdom (by push_cast at hxy ⊢; omega) hr2
        have h3 := X0_ge_rt (a := a) (b := b) hk hdom
        omega
      · have hr2 : Reach a b (x' + 1) y' d' := by unfold Reach; omega
        have hb2 := reach_bound hr2
        have hdom : Dom d' (k + 1) := by
          obtain ⟨h1, h2, h3⟩ := hk
          unfold Dom; push_cast at hxy h1 h2 h3 ⊢; omega
        have := hprev d' rfl (x' + 1) y' (k + 1) hdom (by push_cast at hxy ⊢; omega) hr2
        have h3 := X0_ge_dn (a := a) (b := b) hk hdom
        omega

theorem compl_all (a b : List Nat) : ∀ d, Compl a b d := by
  intro d
  induction d with
  | zero => exact compl_gen a b 0 (fun d' h => by omega)
  | succ d ih =>
    exact compl_gen a b (d + 1) (fun d' h => by
      have : d' = d := by omega
      subst this; exact ih)

end Myers
