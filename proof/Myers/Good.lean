import Mid
import Solve
/-! The middle-snake lemma: the first overlap of the forward and backward searches, for both parities of
`delta`, is a point on an optimal path (`Split`), inside the rectangle, and not a corner. Hence the
Myers model meets `MidSpec`, the contract `solve_optimal` needs. -/
open scoped List
namespace Myers

theorem lcs_drop_le_left (a b : List Nat) (x y : Nat) : lcs (a.drop x) (b.drop y) ≤ a.length - x := by
  have := lcs_le_left (a.drop x) (b.drop y); simpa using this
theorem lcs_drop_le_right (a b : List Nat) (x y : Nat) : lcs (a.drop x) (b.drop y) ≤ b.length - y := by
  have := lcs_le_right (a.drop x) (b.drop y); simpa using this

theorem reach_L {a b : List Nat} {x y d : Nat} (h : Reach a b x y d) : x + y ≤ d + 2 * lcs a b := by
  have := lcs_mono (a.take x) (b.take y) a b (List.take_sublist _ _) (List.take_sublist _ _)
  unfold Reach at h; omega

/-- `d` is a round with no overlap in any earlier round. -/
def FirstHit (a b : List Nat) (d : Nat) : Prop :=
  ∀ d' k', d' < d → Dom d' k' → ¬ (fhit a b d' k' ∨ bhit a b d' k')

theorem first_le {a b : List Nat} {d : Nat} (hF : FirstHit a b d) : d ≤ d0 a b := by
  rcases Nat.lt_or_ge (d0 a b) d with h | h
  · obtain ⟨k, hk, hh⟩ := exists_hit a b
    exact absurd hh (hF _ k h hk)
  · exact h

theorem no_early {a b : List Nat} {d : Nat} (hF : FirstHit a b d)
    (h : a.length + b.length + 2 ≤ 2 * lcs a b + 2 * d) : False := by
  have := first_le hF
  have hL := lcs_two_le a b
  unfold d0 at this; omega

/-- Odd case, arithmetic core: forward point `(X, y)` of round `d + 1` and backward point `(Bx, y')` of
round `d` on the same diagonal, overlapping. -/
theorem core_odd {a b : List Nat} {d X y Bx y' : Nat}
    (hr : Reach a b X y (d + 1)) (hr' : Reach a.reverse b.reverse Bx y' d)
    (hdg : (X : Int) - y + ((Bx : Int) - y') = (a.length : Int) - b.length)
    (hov : a.length ≤ X + Bx) (gX : X ≤ a.length) (gY : y ≤ b.length)
    (hdl : d + 1 ≤ d0 a b) (hD2 : 2 * lcs a b + 2 ≤ a.length + b.length) :
    Split a b X y ∧ ¬(X = 0 ∧ y = 0) ∧ ¬(X = a.length ∧ y = b.length) := by
  have hL := lcs_two_le a b
  have e1 : (a.length - X) + (Bx - (a.length - X)) = Bx := by omega
  have e2 : (b.length - y) + (Bx - (a.length - X)) = y' := by omega
  have hback := reach_back (a := a.reverse) (b := b.reverse) (x := a.length - X) (y := b.length - y)
    (d := d) (Bx - (a.length - X)) (by rw [e1, e2]; exact hr')
  unfold Reach at hback hr
  rw [lcs_rev_take a b X y gX gY] at hback
  have sg := split_ge a b X y
  have b1 := lcs_take_le_left a b X y
  have b2 := lcs_drop_le_left a b X y
  unfold d0 at hdl
  refine ⟨?_, ?_, ?_⟩
  · unfold Split; omega
  · omega
  · omega

/-- Even case, arithmetic core: backward point `(Bx, y')` of round `d` and forward point `(Xf, yf)` of
round `d` on the same diagonal, overlapping; the returned point is `(n - Bx, m - y')`. -/
theorem core_even {a b : List Nat} {d Bx y' Xf yf : Nat}
    (hr' : Reach a.reverse b.reverse Bx y' d) (hrf : Reach a b Xf yf d)
    (hdg : (Bx : Int) - y' + ((Xf : Int) - yf) = (a.length : Int) - b.length)
    (hov : a.length ≤ Bx + Xf) (gX : Bx ≤ a.length) (gY : y' ≤ b.length)
    (hdl : d ≤ d0 a b) (hev : ¬ (((a.length : Int) - b.length) % 2 = 1))
    (hD2 : 2 * lcs a b + 2 ≤ a.length + b.length) :
    Split a b (a.length - Bx) (b.length - y') ∧ ¬(a.length - Bx = 0 ∧ b.length - y' = 0) ∧
      ¬(a.length - Bx = a.length ∧ b.length - y' = b.length) := by
  have hL := lcs_two_le a b
  have e1 : (a.length - Bx) + (Xf - (a.length - Bx)) = Xf := by omega
  have e2 : (b.length - y') + (Xf - (a.length - Bx)) = yf := by omega
  have hback := reach_back (a := a) (b := b) (x := a.length - Bx) (y := b.length - y')
    (d := d) (Xf - (a.length - Bx)) (by rw [e1, e2]; exact hrf)
  have hrev := lcs_rev_take a b (a.length - Bx) (b.length - y') (by omega) (by omega)
  have e3 : a.length - (a.length - Bx) = Bx := by omega
  have e4 : b.length - (b.length - y') = y' := by omega
  rw [e3, e4] at hrev
  unfold Reach at hback hr'
  rw [hrev] at hr'
  have sg := split_ge a b (a.length - Bx) (b.length - y')
  have b1 := lcs_take_le_left a b (a.length - Bx) (b.length - y')
  have b2 := lcs_drop_le_left a b (a.length - Bx) (b.length - y')
  unfold d0 at hdl
  refine ⟨?_, ?_, ?_⟩
  · unfold Split; omega
  · omega
  · omega

theorem fhit_good {a b : List Nat} {d : Nat} {k : Int} (hF : FirstHit a b d) (hdom : Dom d k)
    (hit : fhit a b d k) (hD2 : 2 * lcs a b + 2 ≤ a.length + b.length) :
    ∃ x y : Nat, fpt a b d k = ((x : Int), (y : Int)) ∧ x ≤ a.length ∧ y ≤ b.length ∧ Split a b x y ∧
      ¬(x = 0 ∧ y = 0) ∧ ¬(x = a.length ∧ y = b.length) := by
  obtain ⟨hodd, h1, h2, h3⟩ := hit
  unfold fpt
  cases d with
  | zero => omega
  | succ d' =>
    have hdl := first_le hF
    have hL := lcs_two_le a b
    have hdom' : Dom d' ((a.length : Int) - b.length - k) := by
      unfold Dom at *; omega
    obtain ⟨y, hy, hr⟩ := F_sound a b (d' + 1) k hdom
    obtain ⟨y', hy', hr'⟩ := F_sound a.reverse b.reverse d' _ hdom'
    have hX := reach_L hr
    have hB := reach_L hr'
    rw [lcs_reverse] at hB
    unfold Bk at h3
    rw [Nat.add_sub_cancel] at h3
    generalize F a b (d' + 1) k = X at *
    generalize F a.reverse b.reverse d' ((a.length : Int) - b.length - k) = Bx at *
    have gX : X ≤ a.length := by
      rcases Nat.lt_or_ge a.length X with h | h
      · exfalso; apply no_early hF; omega
      · exact h
    have gY : y ≤ b.length := by
      rcases Nat.lt_or_ge b.length y with h | h
      · exfalso; apply no_early hF; omega
      · exact h
    obtain ⟨c1, c2, c3⟩ := core_odd hr hr' (by omega) h3 gX gY hdl hD2
    exact ⟨X, y, by rw [hy], gX, gY, c1, c2, c3⟩

theorem bhit_good {a b : List Nat} {d : Nat} {k : Int} (hF : FirstHit a b d) (hdom : Dom d k)
    (hit : bhit a b d k) (hD2 : 2 * lcs a b + 2 ≤ a.length + b.length) :
    ∃ x y : Nat, bpt a b d k = ((x : Int), (y : Int)) ∧ x ≤ a.length ∧ y ≤ b.length ∧ Split a b x y ∧
      ¬(x = 0 ∧ y = 0) ∧ ¬(x = a.length ∧ y = b.length) := by
  obtain ⟨hev, h1, h2, h3⟩ := hit
  unfold bpt Bk
  have hdl := first_le hF
  have hL := lcs_two_le a b
  have hdomF : Dom d ((a.length : Int) - b.length - k) := by
    unfold Dom at *; omega
  obtain ⟨y', hy', hr'⟩ := F_sound a.reverse b.reverse d k hdom
  obtain ⟨yf, hyf, hrf⟩ := F_sound a b d _ hdomF
  have hB := reach_L hr'
  rw [lcs_reverse] at hB
  unfold Bk at h3
  generalize F a.reverse b.reverse d k = Bx at *
  generalize F a b d ((a.length : Int) - b.length - k) = Xf at *
  have gX : Bx ≤ a.length := by
    rcases Nat.lt_or_ge a.length Bx with h | h
    · exfalso; apply no_early hF; omega
    · exact h
  have gY : y' ≤ b.length := by
    rcases Nat.lt_or_ge b.length y' with h | h
    · exfalso; apply no_early hF; omega
    · exact h
  obtain ⟨c1, c2, c3⟩ := core_even hr' hrf (by omega) h3 gX gY hdl hev hD2
  refine ⟨a.length - Bx, b.length - y', ?_, by omega, by omega, c1, c2, c3⟩
  simp only [Prod.mk.injEq]; constructor <;> omega

/-! ### the pair is not close to equal -/

theorem HeadsDiff.symm {a b : List Nat} (h : HeadsDiff a b) : HeadsDiff b a :=
  fun x u y v h1 h2 e => h y v x u h2 h1 e.symm

theorem LastsDiff.symm {a b : List Nat} (h : LastsDiff a b) : LastsDiff b a := HeadsDiff.symm h

theorem sub_len {a b : List Nat} (hab : a <+ b) (hne : a ≠ []) (hl : b.length ≤ a.length + 1)
    (hh : HeadsDiff a b) (hl2 : LastsDiff a b) : False := by
  cases b with
  | nil => exact hne (List.sublist_nil.mp hab)
  | cons y b' =>
    rcases List.sublist_cons_iff.mp hab with h | ⟨r, hr, hr'⟩
    · have hlen : a.length = b'.length := by
        have := h.length_le; simp at hl; omega
      have := h.eq_of_length hlen
      subst this
      rcases List.eq_nil_or_concat a with e | ⟨l', z, e⟩
      · exact hne e
      · subst e
        exact hl2 z l'.reverse z (l'.reverse ++ [y]) (by simp) (by simp) rfl
    · exact hh y r y b' hr rfl rfl

theorem two_le (a b : List Nat) (ha : a ≠ []) (hb : b ≠ []) (hh : HeadsDiff a b) (hl : LastsDiff a b) :
    2 * lcs a b + 2 ≤ a.length + b.length := by
  have h1 := lcs_le_left a b
  have h2 := lcs_le_right a b
  obtain ⟨c, c1, c2, c3⟩ := lcs_ex a b
  rcases Nat.lt_or_ge (lcs a b) a.length with hn | hn
  · rcases Nat.lt_or_ge (lcs a b) b.length with hm | hm
    · omega
    · have : c = b := c2.eq_of_length (by omega)
      subst this
      by_cases hlen : a.length ≤ c.length + 1
      · exact (sub_len c1 hb hlen hh.symm hl.symm).elim
      · omega
  · have : c = a := c1.eq_of_length (by omega)
    subst this
    by_cases hlen : b.length ≤ c.length + 1
    · exact (sub_len c2 ha hlen hh hl).elim
    · omega

/-- The Myers model of `middle` as a pair of naturals. -/
def mid (a b : List Nat) : Nat × Nat :=
  match midPt a b with
  | some (x, y) => (x.toNat, y.toNat)
  | none => (0, 0)

/-- The middle-snake lemma at the level of the sweep result: `midPt` is a point of the rectangle on an
optimal path and not a corner. -/
theorem midPt_spec (a b : List Nat) (ha : a ≠ []) (hb : b ≠ []) (hh : HeadsDiff a b) (hl : LastsDiff a b) :
    ∃ x y : Nat, midPt a b = some ((x : Int), (y : Int)) ∧ x ≤ a.length ∧ y ≤ b.length ∧ Split a b x y ∧
      ¬(x = 0 ∧ y = 0) ∧ ¬(x = a.length ∧ y = b.length) := by
  have hD2 := two_le a b ha hb hh hl
  obtain ⟨k0, hk0, hh0⟩ := exists_hit a b
  have hLL := lcs_two_le a b
  obtain ⟨p, hp⟩ := sweep_some a b ((a.length + b.length + 1) / 2 + 1) 0 (d0 a b) k0 (Nat.zero_le _)
    (by unfold d0; omega) hk0 hh0
  obtain ⟨d', k, _, hdom, hcase, hfirst⟩ := sweep_sound a b _ _ p hp
  have hF : FirstHit a b d' := fun d'' k'' h1 h2 => hfirst d'' k'' (Nat.zero_le _) h1 h2
  have hmp : midPt a b = some p := hp
  rcases hcase with ⟨hh1, rfl⟩ | ⟨hh1, rfl⟩
  · obtain ⟨x, y, e, g1, g2, g3, g4, g5⟩ := fhit_good hF hdom hh1 hD2
    exact ⟨x, y, by rw [hmp, e], g1, g2, g3, g4, g5⟩
  · obtain ⟨x, y, e, g1, g2, g3, g4, g5⟩ := bhit_good hF hdom hh1 hD2
    exact ⟨x, y, by rw [hmp, e], g1, g2, g3, g4, g5⟩

/-- The middle-snake lemma, in the form `solve_optimal` consumes. -/
theorem mid_spec : MidSpec mid := by
  intro a b ha hb hh hl
  obtain ⟨x, y, e, g1, g2, g3, g4, g5⟩ := midPt_spec a b ha hb hh hl
  have : mid a b = (x, y) := by unfold mid; rw [e]; simp
  rw [this]; exact ⟨g1, g2, g3, g4, g5⟩

end Myers
