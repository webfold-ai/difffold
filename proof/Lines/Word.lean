import DifffoldLines
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_lines_extract

/-! `word` (the little-endian eight-byte load) of the extraction copy `lines_core`: byte `k` of the result is byte
`k` of the slice, or zero when the slice is shorter. -/

theorem fromLE_bit (x : Std.Array U8 8#usize) (j : Nat) (hj : j < 64) :
    (core.num.U64.from_le_bytes x).bv.getLsbD j = (x.val[j / 8]!).bv.getLsbD (j % 8) := by
  have h : (core.num.U64.from_le_bytes x).bv = (BitVec.fromLEBytes (x.val.map U8.bv)).cast (by simp) := rfl
  rw [h]
  have := BitVec.fromLEBytes_getElem! (x.val.map U8.bv) j
  have hl : x.val.length = 8 := by simp
  have hi : j / 8 < x.val.length := by omega
  rw [BitVec.getLsbD_cast]
  rw [BitVec.getLsbD_eq_getElem?_getD] at *
  simp [getElem!_pos, hi, hj] at this ⊢
  rw [List.getElem?_eq_getElem hi] at *
  simp only [Option.getD_some] at *
  simp only [Byte.testBit, BitVec.testBit_toNat]

def byteAt (l : List U8) (k : Nat) : BitVec 8 := (l[k]?.map U8.bv).getD 0#8

theorem word_aux : ∀ n : Nat, ∀ t : Slice U8, t.val.length = n →
    lines_core.word t ⦃ r => ∀ k, k < 8 → r.bv.extractLsb' (8 * k) 8 = byteAt t.val k ⦄ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t hn
  rw [lines_core.word.eq_1]
  have hlen : t.len.val = n := by simp [Slice.len, hn]
  split
  · rename_i h0
    have : t.val = [] := List.length_eq_zero_iff.mp (by omega)
    simp [WP.spec_ok, byteAt, this]
  · rename_i hne
    split
    · rename_i h8
      have h8' : 8 ≤ n := by scalar_tac
      step*
      intro k hk
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [BitVec.getLsbD_extractLsb']
      simp only [hj, decide_true, Bool.true_and]
      rw [fromLE_bit _ (8 * k + j) (by omega)]
      have e1 : (8 * k + j) / 8 = k := by omega
      have e2 : (8 * k + j) % 8 = j := by omega
      rw [e1, e2]
      have hk' : k < t.val.length := by omega
      simp only [byteAt, List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some]
      have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp [Array.make, i_post, i1_post, i2_post, i3_post, i4_post, i5_post, i6_post, i7_post]
    · rename_i h8
      have h8' : n < 8 := by scalar_tac
      step as ⟨i, i_post, i_post1⟩
      step as ⟨s, s_post, s_post1⟩
      have s_eq : s.val = t.val.take i.val := by simp [s_post, List.slice]
      have hsl : s.val.length = i.val := by simp [s_eq]; omega
      step with (ih i.val (by omega) s hsl) as ⟨i1, hi1⟩
      step*
      simp only [lift, bind_tc_ok]
      step*
      intro k hk
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      have hi1k := hi1 k hk
      have hi1b : i1.bv.getLsbD (8 * k + j) = (byteAt s.val k).getLsbD j := by
        rw [← hi1k, BitVec.getLsbD_extractLsb']; simp [hj]
      have hi : i.val + 1 = n := by omega
      have hi8 : i.val < 8 := by omega
      rw [BitVec.getLsbD_extractLsb']
      simp only [hj, decide_true, Bool.true_and, UScalar.bv_or, BitVec.getLsbD_or, hi1b, i5_post1,
        core.convert.num.FromU64U8.from_bv_eq, BitVec.getLsbD_shiftLeft]
      have hi4 : i4.val = 8 * i.val := i4_post
      rw [hi4]
      have hsk : ∀ m, i.val ≤ m → byteAt s.val m = 0#8 := by
        intro m hm
        simp [byteAt, List.getElem?_eq_none (show s.val.length ≤ m by omega)]
      have htk : ∀ m, n ≤ m → byteAt t.val m = 0#8 := by
        intro m hm
        simp [byteAt, List.getElem?_eq_none (show t.val.length ≤ m by omega)]
      rcases Nat.lt_trichotomy k i.val with hlt | heq | hgt
      · have h1 : byteAt s.val k = byteAt t.val k := by
          simp [byteAt, s_eq, List.getElem?_take_of_lt hlt]
        have h2 : 8 * k + j < 8 * i.val := by omega
        rw [h1]; simp [h2]
      · subst heq
        have h1 : byteAt t.val i.val = i2.bv := by
          have hk' : i.val < t.val.length := by omega
          simp [byteAt, List.getElem?_eq_getElem hk', i2_post]
        rw [h1, hsk i.val (le_refl _)]
        have h2 : ¬ 8 * i.val + j < 8 * i.val := by omega
        have h3 : 8 * i.val + j - 8 * i.val = j := by omega
        simp [h2, h3, BitVec.getLsbD_setWidth, hj, show 8 * i.val + j < 64 by omega]
        intro _; omega
      · rw [hsk k (by omega), htk k (by omega)]
        have h2 : ¬ 8 * k + j < 8 * i.val := by omega
        have h3 : 8 ≤ 8 * k + j - 8 * i.val := by omega
        simp [h2, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge _ _ h3]

/-- `word t` packs the first (at most) eight bytes of `t` little endian; missing high bytes are zero. -/
theorem word_spec (t : Slice U8) :
    lines_core.word t ⦃ r => ∀ k, k < 8 → r.bv.extractLsb' (8 * k) 8 = byteAt t.val k ⦄ :=
  word_aux _ t rfl

end difffold_lines_extract
