import Compl
import Path
/-! The middle-snake search of `src/lines.rs` (`middle`, `sweep`, `forward_one`, `backward_one`) as a pure
Lean model, and the existence of an overlap in round `⌈D/2⌉`.
Modelling choices, all stated here and none proved: the in-place arrays `vf`, `vb` hold `F a b d k` and
`F (reverse a) (reverse b) d k` for the diagonals of the current parity; the order in which the diagonals of
a round are visited (the halving in `forward`/`backward`) does not matter, because every theorem below holds
for any diagonal that overlaps in the first round that has an overlap; array indices stay in bounds. -/
open scoped List
namespace Myers

/-- The backward search is the forward search on the reversed lists. -/
def Bk (a b : List Nat) (d : Nat) (k : Int) : Nat := F a.reverse b.reverse d k

/-- Forward overlap test of `forward_one`: only for odd `delta`, against `vb` of round `d - 1`. -/
abbrev fhit (a b : List Nat) (d : Nat) (k : Int) : Prop :=
  ((a.length : Int) - b.length) % 2 = 1 ∧
  -((d : Int) - 1) ≤ (a.length : Int) - b.length - k ∧ (a.length : Int) - b.length - k ≤ (d : Int) - 1 ∧
  a.length ≤ F a b d k + Bk a b (d - 1) ((a.length : Int) - b.length - k)

/-- Backward overlap test of `backward_one`: only for even `delta`, against `vf` of round `d`. -/
abbrev bhit (a b : List Nat) (d : Nat) (k : Int) : Prop :=
  ¬ (((a.length : Int) - b.length) % 2 = 1) ∧
  -(d : Int) ≤ (a.length : Int) - b.length - k ∧ (a.length : Int) - b.length - k ≤ d ∧
  a.length ≤ Bk a b d k + F a b d ((a.length : Int) - b.length - k)

/-- The point `forward_one` returns, `(x, y)`. -/
def fpt (a b : List Nat) (d : Nat) (k : Int) : Int × Int := ((F a b d k : Nat), (F a b d k : Nat) - k)

/-- The point `backward_one` returns, `(n - x, m - y)`. -/
def bpt (a b : List Nat) (d : Nat) (k : Int) : Int × Int :=
  ((a.length : Int) - (Bk a b d k : Nat), (b.length : Int) - ((Bk a b d k : Nat) - k))

/-- The diagonals `-d, -d+2, ..., d` of round `d`. -/
def kl (d : Nat) : List Int := (List.range (d + 1)).map (fun (i : Nat) => 2 * (i : Int) - d)

theorem mem_kl {d : Nat} {k : Int} : k ∈ kl d ↔ Dom d k := by
  unfold kl Dom
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨((k + d) / 2).toNat, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · omega

def fwdFind (a b : List Nat) (d : Nat) : Option (Int × Int) :=
  (kl d).findSome? (fun k => if fhit a b d k then some (fpt a b d k) else none)

def bwdFind (a b : List Nat) (d : Nat) : Option (Int × Int) :=
  (kl d).findSome? (fun k => if bhit a b d k then some (bpt a b d k) else none)

/-- `sweep`: round `d`, forward half then backward half, then the next round; `fuel` rounds at most
(`none` stands for the `(0, 0)` that `sweep` returns past `max_d`). -/
def sweep (a b : List Nat) : Nat → Nat → Option (Int × Int)
  | 0, _ => none
  | f + 1, d =>
    match fwdFind a b d with
    | some p => some p
    | none =>
      match bwdFind a b d with
      | some p => some p
      | none => sweep a b f (d + 1)

/-- `middle`: start at round 0 with `(n + m + 1) / 2 + 1` rounds. -/
def midPt (a b : List Nat) : Option (Int × Int) := sweep a b ((a.length + b.length + 1) / 2 + 1) 0

theorem fwdFind_some {a b : List Nat} {d : Nat} {p : Int × Int} (h : fwdFind a b d = some p) :
    ∃ k, Dom d k ∧ fhit a b d k ∧ p = fpt a b d k := by
  obtain ⟨k, hk, hf⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨k, mem_kl.mp hk, ?_⟩
  by_cases hh : fhit a b d k
  · rw [if_pos hh] at hf; exact ⟨hh, (Option.some.inj hf).symm⟩
  · rw [if_neg hh] at hf; cases hf

theorem bwdFind_some {a b : List Nat} {d : Nat} {p : Int × Int} (h : bwdFind a b d = some p) :
    ∃ k, Dom d k ∧ bhit a b d k ∧ p = bpt a b d k := by
  obtain ⟨k, hk, hf⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨k, mem_kl.mp hk, ?_⟩
  by_cases hh : bhit a b d k
  · rw [if_pos hh] at hf; exact ⟨hh, (Option.some.inj hf).symm⟩
  · rw [if_neg hh] at hf; cases hf

theorem fwdFind_none {a b : List Nat} {d : Nat} (h : fwdFind a b d = none) :
    ∀ k, Dom d k → ¬ fhit a b d k := by
  intro k hk hh
  have := List.findSome?_eq_none_iff.mp h k (mem_kl.mpr hk)
  rw [if_pos hh] at this; cases this

theorem bwdFind_none {a b : List Nat} {d : Nat} (h : bwdFind a b d = none) :
    ∀ k, Dom d k → ¬ bhit a b d k := by
  intro k hk hh
  have := List.findSome?_eq_none_iff.mp h k (mem_kl.mpr hk)
  rw [if_pos hh] at this; cases this

/-- What a successful sweep returns: a hit of the first round that has one. -/
theorem sweep_sound (a b : List Nat) : ∀ (f d : Nat) (p : Int × Int), sweep a b f d = some p →
    ∃ d' k, d ≤ d' ∧ Dom d' k ∧ ((fhit a b d' k ∧ p = fpt a b d' k) ∨ (bhit a b d' k ∧ p = bpt a b d' k)) ∧
      ∀ d'' k'', d ≤ d'' → d'' < d' → Dom d'' k'' → ¬ (fhit a b d'' k'' ∨ bhit a b d'' k'') := by
  intro f
  induction f with
  | zero => intro d p h; simp [sweep] at h
  | succ f ih =>
    intro d p h
    unfold sweep at h
    rcases hfw : fwdFind a b d with _ | q
    · rw [hfw] at h
      rcases hbw : bwdFind a b d with _ | q'
      · rw [hbw] at h
        obtain ⟨d', k, h1, h2, h3, h4⟩ := ih (d + 1) p h
        refine ⟨d', k, by omega, h2, h3, ?_⟩
        intro d'' k'' hd1 hd2 hk
        rcases Nat.eq_or_lt_of_le hd1 with e | e
        · subst e
          rintro (hh | hh)
          · exact fwdFind_none hfw k'' hk hh
          · exact bwdFind_none hbw k'' hk hh
        · exact h4 d'' k'' e hd2 hk
      · rw [hbw] at h
        obtain ⟨k, hk, hh, hp⟩ := bwdFind_some hbw
        cases h
        exact ⟨d, k, Nat.le_refl _, hk, Or.inr ⟨hh, hp⟩, fun d'' k'' h1 h2 _ => by omega⟩
    · rw [hfw] at h
      obtain ⟨k, hk, hh, hp⟩ := fwdFind_some hfw
      cases h
      exact ⟨d, k, Nat.le_refl _, hk, Or.inl ⟨hh, hp⟩, fun d'' k'' h1 h2 _ => by omega⟩

/-- A hit at a round inside the fuel makes the sweep succeed. -/
theorem sweep_some (a b : List Nat) : ∀ (f d d1 : Nat) (k : Int), d ≤ d1 → d1 < d + f → Dom d1 k →
    (fhit a b d1 k ∨ bhit a b d1 k) → ∃ p, sweep a b f d = some p := by
  intro f
  induction f with
  | zero => intro d d1 k h1 h2; omega
  | succ f ih =>
    intro d d1 k h1 h2 hk hh
    unfold sweep
    rcases hfw : fwdFind a b d with _ | q
    · rcases hbw : bwdFind a b d with _ | q'
      · have hne : d1 ≠ d := by
          intro e; subst e
          rcases hh with hh | hh
          · exact fwdFind_none hfw k hk hh
          · exact bwdFind_none hbw k hk hh
        exact ih (d + 1) d1 k (by omega) (by omega) hk hh
      · exact ⟨q', rfl⟩
    · exact ⟨q, rfl⟩

/-! ### An overlap exists in round `⌈D / 2⌉` -/

theorem lcs_rev_take (a b : List Nat) (x y : Nat) (hx : x ≤ a.length) (hy : y ≤ b.length) :
    lcs (a.reverse.take (a.length - x)) (b.reverse.take (b.length - y)) = lcs (a.drop x) (b.drop y) := by
  rw [List.take_reverse, List.take_reverse, lcs_reverse]
  have e1 : a.length - (a.length - x) = x := by omega
  have e2 : b.length - (b.length - y) = y := by omega
  rw [e1, e2]

theorem lcs_two_le (a b : List Nat) : 2 * lcs a b ≤ a.length + b.length := by
  have := lcs_le_left a b; have := lcs_le_right a b; omega

/-- Round index of the first possible overlap, `⌈D / 2⌉`. -/
def d0 (a b : List Nat) : Nat := (a.length + b.length - 2 * lcs a b + 1) / 2

theorem exists_hit (a b : List Nat) : ∃ k, Dom (d0 a b) k ∧ (fhit a b (d0 a b) k ∨ bhit a b (d0 a b) k) := by
  have hL := lcs_two_le a b
  obtain ⟨x, y, hx, hy, hs, hf⟩ := path_point a b (d0 a b) (by unfold d0; omega)
  unfold Split at hs
  -- the point and its reverse image
  have hl2 : lcs (a.reverse.take (a.length - x)) (b.reverse.take (b.length - y)) =
      lcs (a.drop x) (b.drop y) := lcs_rev_take a b x y hx hy
  have rr : Reach a b x y (d0 a b) := by unfold Reach; omega
  have rb := reach_bound rr
  -- the remaining distance
  have rr2 : Reach a.reverse b.reverse (a.length - x) (b.length - y) (a.length + b.length - 2 * lcs a b - d0 a b) := by
    unfold Reach; rw [hl2]; unfold d0 at *; omega
  have rb2 := reach_bound rr2
  have hdomF : Dom (d0 a b) ((x : Int) - y) := by
    unfold Dom; push_cast at *; omega
  have hF := compl_all a b (d0 a b) x y ((x : Int) - y) hdomF rfl rr
  have hdomB : Dom (a.length + b.length - 2 * lcs a b - d0 a b)
      (((a.length - x : Nat) : Int) - ((b.length - y : Nat) : Int)) := by
    unfold Dom; unfold d0 at *; push_cast at *; omega
  have hB := compl_all a.reverse b.reverse (a.length + b.length - 2 * lcs a b - d0 a b) (a.length - x) (b.length - y) _
    hdomB rfl rr2
  by_cases hodd : ((a.length : Int) - b.length) % 2 = 1
  · -- odd: forward overlap in round d0 against round d0 - 1
    refine ⟨(x : Int) - y, hdomF, Or.inl ⟨hodd, ?_, ?_, ?_⟩⟩
    · unfold d0 at *; push_cast at *; omega
    · unfold d0 at *; push_cast at *; omega
    · have e : a.length + b.length - 2 * lcs a b - d0 a b = d0 a b - 1 := by unfold d0 at *; omega
      rw [e] at hB
      have e2 : (((a.length - x : Nat) : Int) - ((b.length - y : Nat) : Int)) =
          (a.length : Int) - b.length - ((x : Int) - y) := by push_cast; omega
      rw [e2] at hB
      unfold Bk; omega
  · -- even: backward overlap in round d0
    have e : a.length + b.length - 2 * lcs a b - d0 a b = d0 a b := by unfold d0 at *; omega
    rw [e] at hB hdomB
    refine ⟨(((a.length - x : Nat) : Int) - ((b.length - y : Nat) : Int)), hdomB, Or.inr ⟨hodd, ?_, ?_, ?_⟩⟩
    · unfold Dom at hdomF; push_cast at *; omega
    · unfold Dom at hdomF; push_cast at *; omega
    · have e2 : (a.length : Int) - b.length - (((a.length - x : Nat) : Int) - ((b.length - y : Nat) : Int)) =
          (x : Int) - y := by push_cast; omega
      rw [e2]
      unfold Bk; omega

end Myers
