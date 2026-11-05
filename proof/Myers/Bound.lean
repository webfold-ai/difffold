import Snake
/-! Size bound of the furthest-reaching values: `F a b d k <= |a| + d`. Used for the `i32` no-overflow side
conditions of the refinement proof. -/
open scoped List
namespace Myers

theorem snake_le (a b : List Nat) (x : Nat) (y : Int) : x + snake a b x y ≤ max x a.length := by
  unfold snake
  split
  · omega
  · have := cpre_le_left (a.drop x) (b.drop y.toNat); simp at this; omega

theorem cpre_le_right : ∀ a b : List Nat, cpre a b ≤ b.length := by
  intro a; induction a with
  | nil => intro b; cases b <;> simp [cpre]
  | cons x a ih => intro b; cases b with
    | nil => simp [cpre]
    | cons y b => unfold cpre; split
                  · have := ih b; simp; omega
                  · simp

theorem snake_le_y (a b : List Nat) (x : Nat) (y : Int) : y + (snake a b x y : Int) ≤ max y b.length := by
  unfold snake
  split
  · omega
  · have := cpre_le_right (a.drop x) (b.drop y.toNat); simp at this; omega

theorem F_le (a b : List Nat) : ∀ (d : Nat) (k : Int), F a b d k ≤ a.length + d := by
  intro d
  induction d with
  | zero => intro k; rw [F_zero]; have := snake_le a b 0 (-k); omega
  | succ d ih =>
    intro k
    rw [F_succ]
    have h1 := snake_le a b (X0 a b d k) ((X0 a b d k : Nat) - k)
    have h2 : X0 a b d k ≤ a.length + d + 1 := by
      unfold X0; split
      · have := ih (k + 1); omega
      · have := ih (k - 1); omega
    omega

theorem X0_ge_k (a b : List Nat) (d : Nat) (k : Int) (hk : Dom (d + 1) k) : k ≤ (X0 a b d k : Int) := by
  unfold X0
  split
  · rename_i c
    have := F_ge a b d _ (dom_dn hk c); omega
  · rename_i c
    have := F_ge a b d _ (dom_rt hk c); push_cast; omega

end Myers
