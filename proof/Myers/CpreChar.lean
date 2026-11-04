import Snake
/-! `cpre` is characterised by the three facts the extracted `common_prefix` is proved to satisfy. Used to
connect the extraction (`Myers2/SnakeSpec.lean`) to the Lean model. -/
namespace Myers

theorem cpre_char : ∀ (a b : List Nat) (l : Nat), l ≤ min a.length b.length → a.take l = b.take l →
    (l = min a.length b.length ∨ ∃ x y, a[l]? = some x ∧ b[l]? = some y ∧ x ≠ y) → cpre a b = l := by
  intro a
  induction a with
  | nil => intro b l h1 _ _; have : l = 0 := by simp at h1; omega
           subst this; cases b <;> simp [cpre]
  | cons x a ih =>
    intro b l h1 h2 h3
    cases b with
    | nil => simp at h1; simp [cpre, h1]
    | cons y b =>
      cases l with
      | zero =>
        rcases h3 with h3 | ⟨p, q, hp, hq, hpq⟩
        · simp at h3
        · simp at hp hq; rw [← hp, ← hq] at hpq; simp [cpre, hpq]
      | succ l =>
        simp at h2
        obtain ⟨hxy, h2⟩ := h2
        subst hxy
        have := ih b l (by simp at h1; omega) h2 (by
          rcases h3 with h3 | ⟨p, q, hp, hq, hpq⟩
          · left; simp at h3; omega
          · right; exact ⟨p, q, by simpa using hp, by simpa using hq, hpq⟩)
        simp [cpre, this]

end Myers
