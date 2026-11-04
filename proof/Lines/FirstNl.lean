import DifffoldLines
import SWAR
import Word
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_lines_extract

/-- Specification of the trailing-zero count model. `core.num.U64.trailing_zeros` is an opaque axiom in the
generated file (stock Aeneas has no model for it), so the theorems below take this property of it as a
hypothesis. It is the documented behaviour of Rust's `u64::trailing_zeros`. -/
def TzSpec : Prop := ∀ x : U64, core.num.U64.trailing_zeros x ⦃ r =>
    x.val ≠ 0 → x.bv.getLsbD r.val = true ∧ ∀ i < r.val, x.bv.getLsbD i = false ⦄

/-- `r` is the index of the first byte equal to `0x0A` at or after position `lo` of `t`, or `none` when there is
no such byte. -/
def FirstNl (t : List U8) (lo : Nat) : Option Nat → Prop
  | none => ∀ k x, lo ≤ k → t[k]? = some x → x.val ≠ 10
  | some i => lo ≤ i ∧ (∃ x, t[i]? = some x ∧ x.val = 10) ∧
      ∀ k x, lo ≤ k → k < i → t[k]? = some x → x.val ≠ 10

theorem byteAt_eq_ten (l : List U8) (k : Nat) :
    byteAt l k = 10#8 ↔ ∃ x, l[k]? = some x ∧ x.val = 10 := by
  unfold byteAt
  cases h : l[k]? with
  | none => simp
  | some x =>
    simp only [Option.map_some, Option.getD_some, Option.some.injEq, exists_eq_left']
    rw [← UScalar.bv_toNat]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simpa using this
    · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem mask_first (l : List U8) (W : BitVec 64)
    (hw : ∀ k, k < 8 → W.extractLsb' (8 * k) 8 = byteAt l k)
    (j : Nat) (hj : (nlBV W).getLsbD j = true) (hmin : ∀ i, i < j → (nlBV W).getLsbD i = false) :
    ∃ k0, j = 8 * k0 + 7 ∧ k0 < 8 ∧ byteAt l k0 = 10#8 ∧ ∀ k, k < k0 → byteAt l k ≠ 10#8 := by
  have hj64 : j < 64 := by
    by_contra h
    rw [BitVec.getLsbD_of_ge _ _ (by omega)] at hj
    simp at hj
  have hmod : j % 8 = 7 := by
    by_contra h
    have h2 := congrArg (fun v => BitVec.getLsbD v j) (nlBV_low W)
    have hL : ∀ j, j < 64 → j % 8 ≠ 7 → (0x7F7F7F7F7F7F7F7F#64).getLsbD j = true := by decide
    simp [BitVec.getLsbD_and, hj, hL j hj64 h] at h2
  have hk0 : j / 8 < 8 := by omega
  have hjk : j = 8 * (j / 8) + 7 := by omega
  refine ⟨j / 8, hjk, hk0, ?_, ?_⟩
  · have := nlBV_bit W (j / 8) hk0
    rw [← hjk, hj] at this
    have := (of_decide_eq_true this.symm)
    rw [← hw _ hk0]; exact this
  · intro k hk
    have := nlBV_bit W k (by omega)
    rw [hmin (8 * k + 7) (by omega)] at this
    rw [← hw _ (by omega)]
    exact of_decide_eq_false this.symm

theorem mask_ne_zero_iff (l : List U8) (W : BitVec 64)
    (hw : ∀ k, k < 8 → W.extractLsb' (8 * k) 8 = byteAt l k) :
    nlBV W ≠ 0#64 ↔ ∃ k, k < 8 ∧ byteAt l k = 10#8 := by
  constructor
  · intro hne
    by_contra hno
    apply hne
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_zero]
    by_cases hm : i % 8 = 7
    · have hk : i / 8 < 8 := by omega
      have hik : i = 8 * (i / 8) + 7 := by omega
      have := nlBV_bit W (i / 8) hk
      rw [← hik] at this
      rw [this]
      apply decide_eq_false
      rw [hw _ hk]
      intro h; exact hno ⟨_, hk, h⟩
    · have h2 := congrArg (fun v => BitVec.getLsbD v i) (nlBV_low W)
      have hL : ∀ j, j < 64 → j % 8 ≠ 7 → (0x7F7F7F7F7F7F7F7F#64).getLsbD j = true := by decide
      simpa [BitVec.getLsbD_and, hL i hi hm] using h2
  · rintro ⟨k, hk, hb⟩ h0
    have := nlBV_bit W k hk
    rw [h0, hw _ hk, hb] at this
    simp at this

theorem firstnl_skip (t : List U8) (lo : Nat) (r : Option Nat) (h : FirstNl t (lo + 8) r)
    (hno : ∀ k x, lo ≤ k → k < lo + 8 → t[k]? = some x → x.val ≠ 10) : FirstNl t lo r := by
  cases r with
  | none =>
    intro k x hk hx
    by_cases h8 : k < lo + 8
    · exact hno k x hk h8 hx
    · exact h k x (by omega) hx
  | some i =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, h2, ?_⟩
    intro k x hk hki hx
    by_cases h8 : k < lo + 8
    · exact hno k x hk h8 hx
    · exact h3 k x (by omega) hki hx

theorem first_in_block_spec (htz : TzSpec) :
    ∀ N : Nat, ∀ (t : Slice U8) (at' : Usize), t.val.length - at'.val = N →
    t.val.length + 8 ≤ Usize.max →
    lines_core.first_in_block t at' ⦃ r => FirstNl t.val at'.val (r.map (·.val)) ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t at' hN hlen
  rw [lines_core.first_in_block.eq_1]
  split
  · rename_i hge
    have : t.len.val ≤ at'.val := by scalar_tac
    simp only [Slice.len] at this
    simp [WP.spec_ok, FirstNl]
    intro k x hk hx
    rw [List.getElem?_eq_none (by simp at this; omega)] at hx
    simp at hx
  · rename_i hge
    have hlt : at'.val < t.val.length := by
      have : ¬ t.len.val ≤ at'.val := by scalar_tac
      simp [Slice.len] at this; omega
    step as ⟨s, s_post, s_post1⟩
    step with word_spec s as ⟨w, hw⟩
    step with nl_mask_bv w as ⟨m, hm⟩
    have hbytes : ∀ k, k < 8 → w.bv.extractLsb' (8 * k) 8 = byteAt s.val k := hw
    have hnz := mask_ne_zero_iff s.val w.bv hbytes
    split
    · rename_i hm0
      have hmv : m.val ≠ 0 := by
        intro h0
        have : m = 0#u64 := by scalar_tac
        subst this; simp at hm0
      have hmne : nlBV w.bv ≠ 0#64 := by
        intro h0
        apply hmv
        have : m.bv = 0#64 := by rw [hm, h0]
        have := congrArg BitVec.toNat this
        simpa [UScalar.bv_toNat] using this
      step with htz m as ⟨j, hj⟩
      obtain ⟨hj1, hj2⟩ := hj hmv
      rw [hm] at hj1 hj2
      obtain ⟨k0, hjk, hk0, hb0, hbl⟩ := mask_first s.val w.bv hbytes j.val hj1 hj2
      step*
      have hi4 : i4.val = k0 := by rw [i4_post]; scalar_tac
      have hi5 : i5.val = at'.val + k0 := by omega
      have hsget : ∀ k, s.val[k]? = t.val[at'.val + k]? := by
        intro k; rw [s_post, List.getElem?_drop]
      simp only [Option.map_some, FirstNl]
      rw [hi5]
      refine ⟨by omega, ?_, ?_⟩
      · rw [byteAt_eq_ten] at hb0
        obtain ⟨x, hx, hx10⟩ := hb0
        exact ⟨x, by rw [← hsget]; exact hx, hx10⟩
      · intro k x hk hkk hx
        have h1 := hbl (k - at'.val) (by omega)
        intro hx10
        apply h1
        rw [byteAt_eq_ten]
        refine ⟨x, ?_, hx10⟩
        rw [hsget, show at'.val + (k - at'.val) = k by omega]; exact hx
    · rename_i hm0
      have hmz : nlBV w.bv = 0#64 := by
        have : m = 0#u64 := by
          by_contra hne
          apply hm0
          simp [bne_iff_ne, hne]
        rw [← hm, this]; rfl
      have hnone : ∀ k, k < 8 → byteAt s.val k ≠ 10#8 := by
        intro k hk hk10
        exact (hnz.mpr ⟨k, hk, hk10⟩) hmz
      have hsget : ∀ k, s.val[k]? = t.val[at'.val + k]? := by
        intro k; rw [s_post, List.getElem?_drop]
      step as ⟨i2, i2_post⟩
      have h8 : i2.val = at'.val + 8 := by scalar_tac
      have key : ∀ L A : Nat, A < L → L - (A + 8) < L - A := by intro L A h; omega
      have hN' : t.val.length - i2.val < N := by rw [h8, ← hN]; exact key _ _ hlt
      step with (ih _ hN' t i2 rfl hlen) as ⟨r, hr⟩
      apply firstnl_skip _ _ _ (by rw [← h8]; exact hr)
      intro k x hk hk8 hx
      have h1 := hnone (k - at'.val) (by omega)
      intro hx10
      apply h1
      rw [byteAt_eq_ten]
      refine ⟨x, ?_, hx10⟩
      rw [hsget, show at'.val + (k - at'.val) = k by omega]; exact hx

theorem firstnl_some_lt {t : List U8} {lo i : Nat} (h : FirstNl t lo (some i)) : i < t.length := by
  obtain ⟨_, ⟨x, hx, _⟩, _⟩ := h
  exact (List.getElem?_eq_some_iff.mp hx).1

theorem firstnl_left_some (t : List U8) (h : Nat) (i : Nat) (hf : FirstNl (t.take h) 0 (some i)) :
    FirstNl t 0 (some i) := by
  have hi : i < h := by
    obtain ⟨_, ⟨x, hx, _⟩, _⟩ := hf
    rw [List.getElem?_take] at hx
    by_contra hc; simp [hc] at hx
  obtain ⟨_, ⟨x, hx, hx10⟩, hrest⟩ := hf
  refine ⟨by omega, ⟨x, by rwa [List.getElem?_take_of_lt hi] at hx, hx10⟩, ?_⟩
  intro k y hk hki hy
  exact hrest k y hk hki (by rwa [List.getElem?_take_of_lt (by omega : k < h)])

theorem firstnl_both_none (t : List U8) (h : Nat) (h1 : FirstNl (t.take h) 0 none)
    (h2 : FirstNl (t.drop h) 0 none) : FirstNl t 0 none := by
  intro k x _ hx
  by_cases hk : k < h
  · exact h1 k x (by omega) (by rwa [List.getElem?_take_of_lt hk])
  · exact h2 (k - h) x (by omega) (by rw [List.getElem?_drop, show h + (k - h) = k by omega]; exact hx)

theorem firstnl_right_some (t : List U8) (h : Nat) (i : Nat) (h1 : FirstNl (t.take h) 0 none)
    (h2 : FirstNl (t.drop h) 0 (some i)) : FirstNl t 0 (some (i + h)) := by
  obtain ⟨_, ⟨x, hx, hx10⟩, hrest⟩ := h2
  refine ⟨by omega, ⟨x, by rw [List.getElem?_drop] at hx; rwa [Nat.add_comm], hx10⟩, ?_⟩
  intro k y _ hki hy
  by_cases hk : k < h
  · exact h1 k y (by omega) (by rwa [List.getElem?_take_of_lt hk])
  · exact hrest (k - h) y (by omega) (by omega)
      (by rw [List.getElem?_drop, show h + (k - h) = k by omega]; exact hy)

/-- `first_nl t` is the index of the first `0x0A` byte of `t`, or `none` when there is none. Holds for
every slice length (the halving recursion bottoms out in blocks of at most 64 bytes). The only assumption
is the documented behaviour of `u64::trailing_zeros`. -/
theorem first_nl_spec (htz : TzSpec) :
    ∀ N : Nat, ∀ t : Slice U8, t.val.length = N →
    lines_core.first_nl t ⦃ r => FirstNl t.val 0 (r.map (·.val)) ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t hN
  rw [lines_core.first_nl.eq_1]
  have hlenv : t.len.val = N := by simp [Slice.len, hN]
  split
  · rename_i hle
    have hle' : N ≤ 64 := by scalar_tac
    have := first_in_block_spec htz _ t 0#usize rfl (by scalar_tac)
    exact this
  · rename_i hle
    have hgt : 64 < N := by scalar_tac
    step as ⟨i2, i2_post⟩
    step as ⟨s, s_post, s_post1⟩
    have s_eq : s.val = t.val.take i2.val := by simp [s_post, List.slice]
    have hsl : s.val.length = i2.val := by simp [s_eq]; omega
    have hi2 : i2.val = N / 2 := by scalar_tac
    step with (ih i2.val (by omega) s hsl) as ⟨o, ho⟩
    split
    · 
      step as ⟨i4, i4_post⟩
      step as ⟨s1, s1_post, s1_post1⟩
      have s1_eq : s1.val = t.val.drop i4.val := s1_post
      have hi4 : i4.val = i2.val := by scalar_tac
      have hsl1 : s1.val.length = N - i2.val := by simp [s1_eq]; omega
      step with (ih (N - i2.val) (by omega) s1 hsl1) as ⟨o1, ho1⟩
      split
      · 
        simp only [WP.spec_ok, Option.map_none]
        apply firstnl_both_none t.val i2.val
        · rw [← s_eq]; simpa using ho
        · rw [← hi4, ← s1_eq]; simpa using ho1
      · rename_i i5
        have hlt5 : i5.val < s1.val.length := firstnl_some_lt (by simpa using ho1)
        step as ⟨i7, i7_post⟩
        step as ⟨i8, i8_post⟩
        simp only [WP.spec_ok, Option.map_some]
        have : i8.val = i5.val + i2.val := by scalar_tac
        rw [this]
        apply firstnl_right_some t.val i2.val i5.val
        · rw [← s_eq]; simpa using ho
        · rw [← hi4, ← s1_eq]; simpa using ho1
    · rename_i i
      simp only [WP.spec_ok, Option.map_some]
      apply firstnl_left_some t.val i2.val
      rw [← s_eq]; simpa using ho

end difffold_lines_extract
