import Lcs
/-! Myers' furthest-reaching diagonal recurrence as a pure function, and its basic shape lemmas.
`F a b d k` is the furthest `x` on diagonal `k = x - y` reached by the forward search in round `d`
(the content of `vf[k]` after round `d` in `src/lines.rs`; the identification of the in-place array with
this function is not proved). The backward search is the forward search on the reversed lists. -/
open scoped List
namespace Myers

/-- Length of the common prefix. -/
def cpre : List Nat → List Nat → Nat
  | x :: a, y :: b => if x = y then cpre a b + 1 else 0
  | [], _ => 0
  | _ :: _, [] => 0

theorem cpre_le_left : ∀ a b : List Nat, cpre a b ≤ a.length := by
  intro a; induction a with
  | nil => intro b; cases b <;> simp [cpre]
  | cons x a ih => intro b; cases b with
    | nil => simp [cpre]
    | cons y b => unfold cpre; split
                  · have := ih b; simp; omega
                  · simp

theorem cpre_get : ∀ (a b : List Nat) (i : Nat), i < cpre a b → ∃ p, a[i]? = some p ∧ b[i]? = some p := by
  intro a; induction a with
  | nil => intro b i h; cases b <;> simp [cpre] at h
  | cons x a ih => intro b i h; cases b with
    | nil => simp [cpre] at h
    | cons y b =>
      unfold cpre at h
      split at h
      · rename_i hxy; subst hxy
        cases i with
        | zero => exact ⟨x, by simp, by simp⟩
        | succ i => obtain ⟨p, h1, h2⟩ := ih b i (by omega); exact ⟨p, by simpa using h1, by simpa using h2⟩
      · simp at h

theorem cpre_max : ∀ (a b : List Nat) (p : Nat), a[cpre a b]? = some p → b[cpre a b]? = some p → False := by
  intro a; induction a with
  | nil => intro b p h; cases b <;> simp [cpre] at h
  | cons x a ih => intro b p h1 h2; cases b with
    | nil => simp [cpre] at h2
    | cons y b =>
      by_cases hxy : x = y
      · subst hxy
        simp only [cpre, if_true] at h1 h2
        exact ih b p (by simpa using h1) (by simpa using h2)
      · simp [cpre, hxy] at h1 h2; exact hxy (h1.trans h2.symm)

/-- Length of the run of equal ids from `(x, y)`; zero outside the lists (`snake` in `src/lines.rs`). -/
def snake (a b : List Nat) (x : Nat) (y : Int) : Nat :=
  if y < 0 ∨ a.length ≤ x ∨ (b.length : Int) ≤ y then 0 else cpre (a.drop x) (b.drop y.toNat)

theorem snake_eq (a b : List Nat) (x y i : Nat) (h : i < snake a b x y) :
    ∃ p, a[x + i]? = some p ∧ b[y + i]? = some p := by
  unfold snake at h
  split at h
  · omega
  · obtain ⟨p, h1, h2⟩ := cpre_get _ _ _ h
    simp at h1 h2
    exact ⟨p, by simpa [List.getElem?_drop] using h1, by simpa [List.getElem?_drop] using h2⟩

theorem snake_max (a b : List Nat) (x y p : Nat) (h1 : a[x + snake a b x y]? = some p)
    (h2 : b[y + snake a b x y]? = some p) : False := by
  by_cases hc : ((y : Int) < 0 ∨ a.length ≤ x ∨ (b.length : Int) ≤ y)
  · have r0 : snake a b x y = 0 := by unfold snake; rw [if_pos hc]
    rw [r0] at h1 h2
    simp only [Nat.add_zero] at h1 h2
    rcases hc with hc | hc | hc
    · omega
    · rw [List.getElem?_eq_none hc] at h1; simp at h1
    · rw [List.getElem?_eq_none (by omega : b.length ≤ y)] at h2; simp at h2
  · have r1 : snake a b x y = cpre (a.drop x) (b.drop y) := by unfold snake; rw [if_neg hc]; simp
    rw [r1] at h1 h2
    exact cpre_max (a.drop x) (b.drop y) p (by simpa [List.getElem?_drop] using h1)
      (by simpa [List.getElem?_drop] using h2)

/-- The domain of round `d`: diagonals `-d, -d+2, ..., d`. -/
def Dom (d : Nat) (k : Int) : Prop := -(d : Int) ≤ k ∧ k ≤ d ∧ (k + d) % 2 = 0

/-- Furthest-reaching `x` on diagonal `k` after `d` edits (forward search, in-grid or not). -/
def F (a b : List Nat) : Nat → Int → Nat
  | 0, k => snake a b 0 (-k)
  | d + 1, k =>
    (if k = -((d : Int) + 1) ∨ (k ≠ (d : Int) + 1 ∧ F a b d (k - 1) < F a b d (k + 1))
      then F a b d (k + 1) else F a b d (k - 1) + 1) +
    snake a b (if k = -((d : Int) + 1) ∨ (k ≠ (d : Int) + 1 ∧ F a b d (k - 1) < F a b d (k + 1))
      then F a b d (k + 1) else F a b d (k - 1) + 1)
      (((if k = -((d : Int) + 1) ∨ (k ≠ (d : Int) + 1 ∧ F a b d (k - 1) < F a b d (k + 1))
      then F a b d (k + 1) else F a b d (k - 1) + 1 : Nat) : Int) - k)

/-- The value before the snake, `x0` in `forward_one`. -/
def X0 (a b : List Nat) (d : Nat) (k : Int) : Nat :=
  if k = -((d : Int) + 1) ∨ (k ≠ (d : Int) + 1 ∧ F a b d (k - 1) < F a b d (k + 1))
    then F a b d (k + 1) else F a b d (k - 1) + 1

theorem F_succ (a b : List Nat) (d : Nat) (k : Int) :
    F a b (d + 1) k = X0 a b d k + snake a b (X0 a b d k) ((X0 a b d k : Nat) - k) := by
  simp only [F, X0]

theorem F_zero (a b : List Nat) (k : Int) : F a b 0 k = snake a b 0 (-k) := by simp [F]

theorem dom_dn {d : Nat} {k : Int} (hk : Dom (d + 1) k)
    (c : k = -((d : Int) + 1) ∨ (k ≠ (d : Int) + 1 ∧ P)) : Dom d (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := hk
  unfold Dom; push_cast at *
  rcases c with c | ⟨c, _⟩ <;> omega

theorem dom_rt {d : Nat} {k : Int} (hk : Dom (d + 1) k)
    (c : ¬(k = -((d : Int) + 1) ∨ (k ≠ (d : Int) + 1 ∧ P))) : Dom d (k - 1) := by
  obtain ⟨h1, h2, h3⟩ := hk
  unfold Dom; push_cast at *
  omega

theorem F_ge : ∀ (a b : List Nat) (d : Nat) (k : Int), Dom d k → k ≤ (F a b d k : Int) := by
  intro a b d
  induction d with
  | zero => intro k hk; obtain ⟨h1, h2, _⟩ := hk; simp at h1 h2; omega
  | succ d ih =>
    intro k hk
    rw [F_succ]
    have : k ≤ (X0 a b d k : Int) := by
      unfold X0
      split
      · rename_i c
        have := ih _ (dom_dn hk c); omega
      · rename_i c
        have := ih _ (dom_rt hk c); push_cast; omega
    omega

theorem X0_ge_rt {a b : List Nat} {d : Nat} {k : Int} (hk : Dom (d + 1) k) (h : Dom d (k - 1)) :
    F a b d (k - 1) + 1 ≤ X0 a b d k := by
  unfold X0; split
  · rename_i c
    rcases c with c | ⟨c, c'⟩
    · obtain ⟨h1, _, _⟩ := h; omega
    · omega
  · exact Nat.le_refl _

theorem X0_ge_dn {a b : List Nat} {d : Nat} {k : Int} (hk : Dom (d + 1) k) (h : Dom d (k + 1)) :
    F a b d (k + 1) ≤ X0 a b d k := by
  unfold X0; split
  · exact Nat.le_refl _
  · rename_i c
    have : ¬ F a b d (k - 1) < F a b d (k + 1) := by
      intro hlt; apply c; right
      refine ⟨?_, hlt⟩
      obtain ⟨_, h2, _⟩ := h; omega
    omega

end Myers
