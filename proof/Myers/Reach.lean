import Snake
/-! `Reach a b x y d` says the edit-graph point `(x, y)` is at distance at most `d` from the origin
(the distance is `x + y - 2 * lcs (take x a) (take y b)`; `take` saturates, so points past the end of
either list are allowed: the lists are padded with ids that match nothing).
Soundness, completeness and diagonal monotonicity of the furthest-reaching recurrence `F`. -/
open scoped List
namespace Myers

def Reach (a b : List Nat) (x y d : Nat) : Prop := x + y ≤ d + 2 * lcs (a.take x) (b.take y)

theorem lcs_take_le_left (a b : List Nat) (x y : Nat) : lcs (a.take x) (b.take y) ≤ x := by
  have := lcs_le_left (a.take x) (b.take y); simp at this; omega
theorem lcs_take_le_right (a b : List Nat) (x y : Nat) : lcs (a.take x) (b.take y) ≤ y := by
  have := lcs_le_right (a.take x) (b.take y); simp at this; omega

theorem reach_bound {a b : List Nat} {x y d : Nat} (h : Reach a b x y d) : x ≤ y + d ∧ y ≤ x + d := by
  have := lcs_take_le_left a b x y; have := lcs_take_le_right a b x y; unfold Reach at h; omega

theorem take_snoc (a : List Nat) (x : Nat) : a.take (x + 1) = a.take x ++ (a[x]?).toList := List.take_add_one

theorem reach_diag {a b : List Nat} {x y d p : Nat} (h : Reach a b x y d)
    (ha : a[x]? = some p) (hb : b[y]? = some p) : Reach a b (x + 1) (y + 1) d := by
  unfold Reach at *
  rw [take_snoc, take_snoc, ha, hb]
  simp only [Option.toList_some]
  rw [lcs_suffix]; simp; omega

theorem reach_right {a b : List Nat} {x y d : Nat} (h : Reach a b x y d) : Reach a b (x + 1) y (d + 1) := by
  unfold Reach at *
  have := lcs_mono (a.take x) (b.take y) (a.take (x + 1)) (b.take y)
    (List.take_sublist_take_left (Nat.le_succ x)) (List.Sublist.refl _)
  omega

theorem reach_down {a b : List Nat} {x y d : Nat} (h : Reach a b x y d) : Reach a b x (y + 1) (d + 1) := by
  unfold Reach at *
  have := lcs_mono (a.take x) (b.take y) (a.take x) (b.take (y + 1))
    (List.Sublist.refl _) (List.take_sublist_take_left (Nat.le_succ y))
  omega

theorem reach_snake {a b : List Nat} {x y d : Nat} (t : Nat)
    (hs : ∀ i, i < t → ∃ p, a[x + i]? = some p ∧ b[y + i]? = some p) (h : Reach a b x y d) :
    Reach a b (x + t) (y + t) d := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    obtain ⟨p, h1, h2⟩ := hs t (Nat.lt_succ_self t)
    have := reach_diag (ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))) h1 h2
    simpa [Nat.add_assoc] using this

theorem snake_reach {a b : List Nat} {x y d : Nat} (h : Reach a b x y d) :
    Reach a b (x + snake a b x y) (y + snake a b x y) d :=
  reach_snake _ (fun i hi => snake_eq a b x y i hi) h

/-- Soundness: the point the recurrence reaches is within `d` edits. -/
theorem F_sound (a b : List Nat) : ∀ (d : Nat) (k : Int), Dom d k →
    ∃ y : Nat, (y : Int) = (F a b d k : Int) - k ∧ Reach a b (F a b d k) y d := by
  intro d
  induction d with
  | zero =>
    intro k hk
    obtain ⟨h1, h2, _⟩ := hk
    have hk0 : k = 0 := by simp at h1 h2; omega
    subst hk0
    have h := snake_reach (a := a) (b := b) (x := 0) (y := 0) (d := 0) (by simp [Reach])
    refine ⟨snake a b 0 0, ?_, ?_⟩
    · rw [F_zero]; simp
    · rw [F_zero]; simpa using h
  | succ d ih =>
    intro k hk
    have key : ∃ y0 : Nat, (y0 : Int) = (X0 a b d k : Int) - k ∧ Reach a b (X0 a b d k) y0 (d + 1) := by
      unfold X0
      split
      · rename_i c
        obtain ⟨y', h1, h2⟩ := ih (k + 1) (dom_dn hk c)
        exact ⟨y' + 1, by push_cast; omega, reach_down h2⟩
      · rename_i c
        obtain ⟨y', h1, h2⟩ := ih (k - 1) (dom_rt hk c)
        refine ⟨y', by push_cast; omega, ?_⟩
        have := reach_right h2
        simpa using this
    obtain ⟨y0, hy0, hr⟩ := key
    have := snake_reach hr
    refine ⟨y0 + snake a b (X0 a b d k) y0, ?_, ?_⟩
    · rw [F_succ, hy0]; push_cast; omega
    · rw [F_succ, ← hy0]; simpa using this

/-! ### monotonicity along a diagonal -/

theorem lcs_take_succ_le (a b : List Nat) (x y : Nat) :
    lcs (a.take (x + 1)) (b.take (y + 1)) ≤ lcs (a.take x) (b.take y) + 1 := by
  rw [take_snoc, take_snoc]
  cases ha : a[x]? <;> cases hb : b[y]? <;>
    simp only [Option.toList_none, Option.toList_some, List.append_nil]
  · omega
  · exact lcs_snoc_right_le _ _ _
  · exact lcs_snoc_left_le _ _ _
  · exact lcs_snoc_both_le _ _ _ _

/-- Moving back along a diagonal never raises the distance bound. -/
theorem reach_back {a b : List Nat} {x y d : Nat} (t : Nat) (h : Reach a b (x + t) (y + t) d) :
    Reach a b x y d := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    apply ih
    unfold Reach at *
    have := lcs_take_succ_le a b (x + t) (y + t)
    have e1 : x + (t + 1) = x + t + 1 := by omega
    have e2 : y + (t + 1) = y + t + 1 := by omega
    rw [e1, e2] at h
    omega

/-- The greedy backward step: a last pair of equal ids can be dropped for free. -/
theorem reach_drop_diag {a b : List Nat} {x y d p : Nat} (h : Reach a b (x + 1) (y + 1) d)
    (ha : a[x]? = some p) (hb : b[y]? = some p) : Reach a b x y d := by
  unfold Reach at *
  rw [take_snoc, take_snoc, ha, hb] at h
  simp only [Option.toList_some] at h
  rw [lcs_suffix] at h; simp at h; omega

theorem lcs_snoc_ne {p q : Nat} (h : p ≠ q) (A B : List Nat) :
    lcs (A ++ [p]) (B ++ [q]) = max (lcs A (B ++ [q])) (lcs (A ++ [p]) B) := by
  rw [← lcs_reverse, ← lcs_reverse A, ← lcs_reverse (A ++ [p])]
  simp [lcs_cons_ne h]

/-- A last step that is not a matching pair is a right or a down step. -/
theorem reach_drop_step {a b : List Nat} {x y d : Nat} (h : Reach a b (x + 1) (y + 1) d)
    (hne : ¬ ∃ p, a[x]? = some p ∧ b[y]? = some p) :
    (x + (y + 1) + 1 ≤ d + 2 * lcs (a.take x) (b.take (y + 1))) ∨
    ((x + 1) + y + 1 ≤ d + 2 * lcs (a.take (x + 1)) (b.take y)) := by
  unfold Reach at h
  have key : lcs (a.take (x + 1)) (b.take (y + 1)) ≤
      max (lcs (a.take x) (b.take (y + 1))) (lcs (a.take (x + 1)) (b.take y)) := by
    rw [take_snoc a x, take_snoc b y]
    cases ha : a[x]? with
    | none => simp only [Option.toList_none, List.append_nil]; exact Nat.le_max_left _ _
    | some p =>
      cases hb : b[y]? with
      | none => simp only [Option.toList_none, List.append_nil]; exact Nat.le_max_right _ _
      | some q =>
        have hpq : p ≠ q := fun e => hne ⟨p, ha, by rw [hb, e]⟩
        simp only [Option.toList_some]
        rw [lcs_snoc_ne hpq]
        exact Nat.le_refl _
  rcases Nat.le_total (lcs (a.take x) (b.take (y + 1))) (lcs (a.take (x + 1)) (b.take y)) with hl | hl
  · right; have := Nat.max_eq_right hl; omega
  · left; have := Nat.max_eq_left hl; omega

end Myers
