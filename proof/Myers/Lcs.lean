/-! Longest common subsequence of two lists of natural numbers (the interned line ids), by recursion,
with the two facts every later file uses: a common subsequence is no longer than `lcs`, and some
common subsequence attains it. Plain Lean, core only. -/
open scoped List
namespace Myers

/-- Length of a longest common subsequence. -/
def lcs : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: a, y :: b => if x = y then lcs a b + 1 else max (lcs a (y :: b)) (lcs (x :: a) b)
termination_by xs ys => xs.length + ys.length

theorem lcs_nil_left (b : List Nat) : lcs [] b = 0 := by simp [lcs]
theorem lcs_nil_right (a : List Nat) : lcs a [] = 0 := by cases a <;> simp [lcs]
theorem lcs_cons_eq (x : Nat) (a b : List Nat) : lcs (x :: a) (x :: b) = lcs a b + 1 := by
  rw [lcs]; simp
theorem lcs_cons_ne {x y : Nat} (h : x ≠ y) (a b : List Nat) :
    lcs (x :: a) (y :: b) = max (lcs a (y :: b)) (lcs (x :: a) b) := by
  rw [lcs]; simp [h]

/-- Any common subsequence is at most as long as `lcs`. -/
theorem lcs_le : ∀ (a b c : List Nat), c <+ a → c <+ b → c.length ≤ lcs a b := by
  intro a
  induction a with
  | nil => intro b c h1 _; rw [List.sublist_nil.mp h1]; simp
  | cons x a ih =>
    intro b
    induction b with
    | nil => intro c _ h2; rw [List.sublist_nil.mp h2]; simp
    | cons y b ihb =>
      intro c h1 h2
      by_cases hxy : x = y
      · subst hxy
        rw [lcs_cons_eq]
        rcases List.sublist_cons_iff.mp h1 with h1 | ⟨r, rfl, hr⟩
        · rcases List.sublist_cons_iff.mp h2 with h2 | ⟨r, rfl, hr⟩
          · have := ih b c h1 h2; omega
          · have := ih b r (List.Sublist.trans (List.sublist_cons_self _ _) h1) hr
            simp; omega
        · rcases List.sublist_cons_iff.mp h2 with h2 | ⟨r', hr'', hr'⟩
          · have := ih b r hr (List.Sublist.trans (List.sublist_cons_self _ _) h2)
            simp; omega
          · have := ih b r hr (by simp at hr''; rw [hr'']; exact hr')
            simp; omega
      · rw [lcs_cons_ne hxy]
        rcases List.sublist_cons_iff.mp h1 with h1' | ⟨r, rfl, hr⟩
        · have := ih (y :: b) c h1' h2
          exact Nat.le_trans this (Nat.le_max_left _ _)
        · rcases List.sublist_cons_iff.mp h2 with h2' | ⟨r', hr'', hr'⟩
          · have := ihb (x :: r) h1 h2'
            exact Nat.le_trans this (Nat.le_max_right _ _)
          · simp at hr''; exact absurd hr''.1 hxy

/-- Some common subsequence attains `lcs`. -/
theorem lcs_ex : ∀ (a b : List Nat), ∃ c, c <+ a ∧ c <+ b ∧ c.length = lcs a b := by
  intro a
  induction a with
  | nil => intro b; exact ⟨[], List.Sublist.slnil, List.nil_sublist _, by simp [lcs_nil_left]⟩
  | cons x a ih =>
    intro b
    induction b with
    | nil => exact ⟨[], List.nil_sublist _, List.Sublist.slnil, by simp [lcs_nil_right]⟩
    | cons y b ihb =>
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨c, h1, h2, h3⟩ := ih b
        exact ⟨x :: c, h1.cons_cons x, h2.cons_cons x, by simp [lcs_cons_eq, h3]⟩
      · rw [lcs_cons_ne hxy]
        obtain ⟨c1, h1, h2, h3⟩ := ih (y :: b)
        obtain ⟨c2, g1, g2, g3⟩ := ihb
        rcases Nat.le_total (lcs a (y :: b)) (lcs (x :: a) b) with h | h
        · exact ⟨c2, g1, g2.cons y, by rw [g3]; omega⟩
        · exact ⟨c1, h1.cons x, h2, by rw [h3]; omega⟩

theorem lcs_le_left (a b : List Nat) : lcs a b ≤ a.length := by
  obtain ⟨c, h1, _, h3⟩ := lcs_ex a b; rw [← h3]; exact h1.length_le
theorem lcs_le_right (a b : List Nat) : lcs a b ≤ b.length := by
  obtain ⟨c, _, h2, h3⟩ := lcs_ex a b; rw [← h3]; exact h2.length_le

theorem lcs_reverse (a b : List Nat) : lcs a.reverse b.reverse = lcs a b := by
  apply Nat.le_antisymm
  · obtain ⟨c, h1, h2, h3⟩ := lcs_ex a.reverse b.reverse
    have := lcs_le a b c.reverse (List.reverse_sublist.mp (by simpa using h1))
      (List.reverse_sublist.mp (by simpa using h2))
    simpa [h3] using this
  · obtain ⟨c, h1, h2, h3⟩ := lcs_ex a b
    have := lcs_le a.reverse b.reverse c.reverse (List.reverse_sublist.mpr h1) (List.reverse_sublist.mpr h2)
    simpa [h3] using this

/-- Equal first elements: the greedy step. -/
theorem lcs_prefix (p a b : List Nat) : lcs (p ++ a) (p ++ b) = p.length + lcs a b := by
  induction p with
  | nil => simp
  | cons x p ih => simp [lcs_cons_eq, ih]; omega

/-- Equal last elements. -/
theorem lcs_suffix (a b s : List Nat) : lcs (a ++ s) (b ++ s) = lcs a b + s.length := by
  rw [← lcs_reverse, List.reverse_append, List.reverse_append, lcs_prefix, lcs_reverse]; simp; omega

theorem lcs_trim (p a b s : List Nat) :
    lcs (p ++ a ++ s) (p ++ b ++ s) = p.length + lcs a b + s.length := by
  rw [List.append_assoc, List.append_assoc, lcs_prefix, lcs_suffix]; omega

/-- A longer pair never has a shorter lcs. -/
theorem lcs_mono (a b a' b' : List Nat) (ha : a <+ a') (hb : b <+ b') : lcs a b ≤ lcs a' b' := by
  obtain ⟨c, h1, h2, h3⟩ := lcs_ex a b
  rw [← h3]; exact lcs_le a' b' c (h1.trans ha) (h2.trans hb)

/-- Concatenation: lcs of the whole is at least the sum of the lcs of the parts. -/
theorem lcs_append_ge (a1 a2 b1 b2 : List Nat) : lcs a1 b1 + lcs a2 b2 ≤ lcs (a1 ++ a2) (b1 ++ b2) := by
  obtain ⟨c, h1, h2, h3⟩ := lcs_ex a1 b1
  obtain ⟨d, g1, g2, g3⟩ := lcs_ex a2 b2
  have := lcs_le (a1 ++ a2) (b1 ++ b2) (c ++ d) (h1.append g1) (h2.append g2)
  simp at this; omega

/-- One extra element on one side adds at most one. -/
theorem lcs_cons_right_le (q : Nat) (a b : List Nat) : lcs a (q :: b) ≤ lcs a b + 1 := by
  obtain ⟨c, h1, h2, h3⟩ := lcs_ex a (q :: b)
  rw [← h3]
  rcases List.sublist_cons_iff.mp h2 with h2 | ⟨r, rfl, hr⟩
  · have := lcs_le a b c h1 h2; omega
  · have := lcs_le a b r (List.Sublist.trans (List.sublist_cons_self _ _) h1) hr
    simp; omega

theorem lcs_cons_left_le (p : Nat) (a b : List Nat) : lcs (p :: a) b ≤ lcs a b + 1 := by
  obtain ⟨c, h1, h2, h3⟩ := lcs_ex (p :: a) b
  rw [← h3]
  rcases List.sublist_cons_iff.mp h1 with h1 | ⟨r, rfl, hr⟩
  · have := lcs_le a b c h1 h2; omega
  · have := lcs_le a b r hr (List.Sublist.trans (List.sublist_cons_self _ _) h2)
    simp; omega

/-- Extending both sides by one element each adds at most one. -/
theorem lcs_cons_both_le (p q : Nat) (a b : List Nat) : lcs (p :: a) (q :: b) ≤ lcs a b + 1 := by
  by_cases h : p = q
  · subst h; rw [lcs_cons_eq]; exact Nat.le_refl _
  · rw [lcs_cons_ne h]
    have h1 := lcs_cons_right_le q a b
    have h2 := lcs_cons_left_le p a b
    omega

theorem lcs_snoc_right_le (q : Nat) (a b : List Nat) : lcs a (b ++ [q]) ≤ lcs a b + 1 := by
  rw [← lcs_reverse a (b ++ [q]), ← lcs_reverse a b]; simpa using lcs_cons_right_le q a.reverse b.reverse
theorem lcs_snoc_left_le (p : Nat) (a b : List Nat) : lcs (a ++ [p]) b ≤ lcs a b + 1 := by
  rw [← lcs_reverse (a ++ [p]) b, ← lcs_reverse a b]; simpa using lcs_cons_left_le p a.reverse b.reverse
theorem lcs_snoc_both_le (p q : Nat) (a b : List Nat) : lcs (a ++ [p]) (b ++ [q]) ≤ lcs a b + 1 := by
  rw [← lcs_reverse (a ++ [p]) (b ++ [q]), ← lcs_reverse a b]; simpa using lcs_cons_both_le p q a.reverse b.reverse

end Myers
