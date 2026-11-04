/-! The multiset overlap of two lists, in plain Lean (no Aeneas, no Mathlib).

`interM A B` is the multiset intersection as a list: scan `A`, and for each element still available in `B`
take it and remove one copy from `B`. `overlap A B` is its length. `count_interM` pins it down:
`count x (interM A B) = min (count x A) (count x B)`, i.e. the multiset intersection. -/
namespace Ted

def interM : List Nat → List Nat → List Nat
  | [], _ => []
  | x :: A, B => if x ∈ B then x :: interM A (B.erase x) else interM A B

/-- The size of the multiset overlap. -/
def overlap (A B : List Nat) : Nat := (interM A B).length

theorem count_interM : ∀ (A B : List Nat) (x : Nat),
    (interM A B).count x = min (A.count x) (B.count x)
  | [], B, x => by simp [interM]
  | y :: A, B, x => by
    have ih := count_interM A (B.erase y) x
    have ih2 := count_interM A B x
    by_cases hy : y ∈ B
    · have hc : 1 ≤ B.count y := List.count_pos_iff.mpr hy
      simp only [interM, hy, ↓reduceIte, List.count_cons, List.count_erase] at ih ⊢
      by_cases hyx : y = x
      · subst hyx; simp at ih ⊢; omega
      · simp [hyx] at ih ⊢; omega
    · simp only [interM, hy, ↓reduceIte, List.count_cons] at ih2 ⊢
      by_cases hyx : y = x
      · subst hyx
        have : B.count y = 0 := List.count_eq_zero.mpr hy
        rw [ih2, this]; simp
      · simp [hyx]; exact ih2

theorem interM_nil_right : ∀ A : List Nat, interM A [] = []
  | [] => rfl
  | y :: A => by simp [interM, interM_nil_right A]

theorem length_interM_le_left : ∀ (A B : List Nat), (interM A B).length ≤ A.length
  | [], B => by simp [interM]
  | y :: A, B => by
    have h1 := length_interM_le_left A (B.erase y)
    have h2 := length_interM_le_left A B
    simp only [interM]
    split
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

theorem length_interM_le_right : ∀ (A B : List Nat), (interM A B).length ≤ B.length
  | [], B => by simp [interM]
  | y :: A, B => by
    have h1 := length_interM_le_right A (B.erase y)
    have h2 := length_interM_le_right A B
    simp only [interM]
    split
    · rename_i hy
      have := List.length_erase_of_mem hy
      have := List.length_pos_of_mem hy
      simp only [List.length_cons]; omega
    · exact h2

/-- Lists with the same counts have the same overlap with anything. -/
theorem overlap_perm {A A' B B' : List Nat} (ha : A.Perm A') (hb : B.Perm B') :
    overlap A B = overlap A' B' := by
  unfold overlap
  apply List.Perm.length_eq
  rw [List.perm_iff_count]
  intro x
  rw [count_interM, count_interM, ha.count_eq, hb.count_eq]

theorem overlap_cons_eq (x : Nat) (A B : List Nat) : overlap (x :: A) (x :: B) = overlap A B + 1 := by
  simp [overlap, interM]

theorem overlap_cons_lt (x : Nat) (A B : List Nat) (h : ∀ y ∈ B, x < y) :
    overlap (x :: A) B = overlap A B := by
  have : x ∉ B := fun hx => by have := h x hx; omega
  simp [overlap, interM, this]

theorem overlap_cons_gt (y : Nat) (A B : List Nat) (h : ∀ a ∈ A, y < a) :
    overlap A (y :: B) = overlap A B := by
  unfold overlap
  apply List.Perm.length_eq
  rw [List.perm_iff_count]
  intro x
  rw [count_interM, count_interM]
  by_cases hyx : y = x
  · subst hyx
    have : A.count y = 0 := List.count_eq_zero.mpr (fun hy => by have := h y hy; omega)
    simp [this]
  · simp [hyx]

theorem overlap_nil_left (B : List Nat) : overlap [] B = 0 := by simp [overlap, interM]
theorem overlap_nil_right (A : List Nat) : overlap A [] = 0 := by simp [overlap, interM_nil_right]

theorem overlap_le_left (A B : List Nat) : overlap A B ≤ A.length := length_interM_le_left A B
theorem overlap_le_right (A B : List Nat) : overlap A B ≤ B.length := length_interM_le_right A B

/-- A list with the counts of the multiset intersection has the length of the overlap. -/
theorem length_of_counts {C A B : List Nat} (h : ∀ x, C.count x = min (A.count x) (B.count x)) :
    C.length = overlap A B := by
  unfold overlap
  apply List.Perm.length_eq
  rw [List.perm_iff_count]
  intro x
  rw [h, count_interM]

end Ted
