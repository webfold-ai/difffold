import DifffoldReal
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-! The SWAR newline mask on one 64-bit word, as arithmetic on lists of bytes. A word is the little-endian
number `Pl` of its eight bytes. -/

/-- Little-endian number of a list of digits. -/
def Pl : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * Pl bs

/-- The word whose `k` bytes all equal `c`. -/
def NC : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, c => c + 256 * NC k c

/-- The mark `nl_mask` puts in a byte. -/
def gmask (b : Nat) : Nat := if b = 10 then 128 else 0

theorem Pl_lt : ∀ bs : List Nat, (∀ b ∈ bs, b < 256) → Pl bs < 256 ^ bs.length
  | [], _ => by simp [Pl]
  | b :: bs, h => by
    have ih := Pl_lt bs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hb := h b (by simp)
    simp only [Pl, List.length_cons, pow_succ]
    omega

theorem NC_lt (c : Nat) (hc : c < 256) : ∀ k, NC k c < 256 ^ k
  | 0 => by simp [NC]
  | k + 1 => by
    have ih := NC_lt c hc k
    simp only [NC, pow_succ]
    omega

theorem NC_255 : ∀ k, NC k 255 + 1 = 256 ^ k
  | 0 => by simp [NC]
  | k + 1 => by
    have ih := NC_255 k
    simp only [NC, pow_succ]
    omega

theorem peel_and (a0 b0 : Nat) (ha : a0 < 256) (hb : b0 < 256) (a1 b1 : Nat) :
    (a0 + 256 * a1) &&& (b0 + 256 * b1) = (a0 &&& b0) + 256 * (a1 &&& b1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hab : a0 &&& b0 < 2 ^ 8 := Nat.and_lt_two_pow a0 (by simpa using hb)
  have e1 : a0 + 256 * a1 = 2 ^ 8 * a1 + a0 := by omega
  have e2 : b0 + 256 * b1 = 2 ^ 8 * b1 + b0 := by omega
  have e3 : (a0 &&& b0) + 256 * (a1 &&& b1) = 2 ^ 8 * (a1 &&& b1) + (a0 &&& b0) := by omega
  rw [e1, e2, e3, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (by simpa using ha),
    Nat.testBit_two_pow_mul_add _ (by simpa using hb), Nat.testBit_two_pow_mul_add _ hab]
  split <;> simp [Nat.testBit_and]

theorem peel_or (a0 b0 : Nat) (ha : a0 < 256) (hb : b0 < 256) (a1 b1 : Nat) :
    (a0 + 256 * a1) ||| (b0 + 256 * b1) = (a0 ||| b0) + 256 * (a1 ||| b1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hab : a0 ||| b0 < 2 ^ 8 := Nat.or_lt_two_pow (by simpa using ha) (by simpa using hb)
  have e1 : a0 + 256 * a1 = 2 ^ 8 * a1 + a0 := by omega
  have e2 : b0 + 256 * b1 = 2 ^ 8 * b1 + b0 := by omega
  have e3 : (a0 ||| b0) + 256 * (a1 ||| b1) = 2 ^ 8 * (a1 ||| b1) + (a0 ||| b0) := by omega
  rw [e1, e2, e3, Nat.testBit_or, Nat.testBit_two_pow_mul_add _ (by simpa using ha),
    Nat.testBit_two_pow_mul_add _ (by simpa using hb), Nat.testBit_two_pow_mul_add _ hab]
  split <;> simp [Nat.testBit_or]

theorem peel_xor (a0 b0 : Nat) (ha : a0 < 256) (hb : b0 < 256) (a1 b1 : Nat) :
    (a0 + 256 * a1) ^^^ (b0 + 256 * b1) = (a0 ^^^ b0) + 256 * (a1 ^^^ b1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hab : a0 ^^^ b0 < 2 ^ 8 := Nat.xor_lt_two_pow (by simpa using ha) (by simpa using hb)
  have e1 : a0 + 256 * a1 = 2 ^ 8 * a1 + a0 := by omega
  have e2 : b0 + 256 * b1 = 2 ^ 8 * b1 + b0 := by omega
  have e3 : (a0 ^^^ b0) + 256 * (a1 ^^^ b1) = 2 ^ 8 * (a1 ^^^ b1) + (a0 ^^^ b0) := by omega
  rw [e1, e2, e3, Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ (by simpa using ha),
    Nat.testBit_two_pow_mul_add _ (by simpa using hb), Nat.testBit_two_pow_mul_add _ hab]
  split <;> simp [Nat.testBit_xor]

/-- The byte-lane computation of `nl_mask`, before the final complement. -/
def swarA (k w : Nat) : Nat := ((w ^^^ NC k 10) &&& NC k 127) + NC k 127
def swar (k w : Nat) : Nat := (swarA k w ||| (w ^^^ NC k 10)) ||| NC k 127

set_option maxRecDepth 100000 in
theorem lane_ok : ∀ b : Nat, b < 256 →
    (((b ^^^ 10) &&& 127) + 127 < 256) ∧
    ((((((b ^^^ 10) &&& 127) + 127) ||| (b ^^^ 10)) ||| 127) < 256) ∧
    ((((((b ^^^ 10) &&& 127) + 127) ||| (b ^^^ 10)) ||| 127) + gmask b = 255) := by
  decide +revert

theorem swar_spec : ∀ bs : List Nat, (∀ b ∈ bs, b < 256) →
    swarA bs.length (Pl bs) < 256 ^ bs.length ∧ swar bs.length (Pl bs) < 256 ^ bs.length ∧
    swar bs.length (Pl bs) + Pl (bs.map gmask) = 256 ^ bs.length - 1
  | [], _ => by simp [swarA, swar, Pl, NC]
  | b :: bs, h => by
    have hb : b < 256 := h b (by simp)
    have hbs : ∀ x ∈ bs, x < 256 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨ih1, ih2, ih3⟩ := swar_spec bs hbs
    obtain ⟨l1, l2, l3⟩ := lane_ok b hb
    have hP := Pl_lt bs hbs
    have n10 := NC_lt 10 (by omega) bs.length
    have n127 := NC_lt 127 (by omega) bs.length
    set k := bs.length with hk
    have hx : (b ^^^ 10) < 256 := by
      have := Nat.xor_lt_two_pow (x := b) (y := 10) (n := 8) (by simpa using hb) (by decide)
      simpa using this
    have hu : ((b ^^^ 10) &&& 127) ≤ 127 := Nat.and_le_right
    have e1 : Pl (b :: bs) ^^^ NC (k + 1) 10 = (b ^^^ 10) + 256 * (Pl bs ^^^ NC k 10) := by
      simp only [Pl, NC]; exact peel_xor b 10 hb (by omega) _ _
    have e2 : (Pl (b :: bs) ^^^ NC (k + 1) 10) &&& NC (k + 1) 127 =
        ((b ^^^ 10) &&& 127) + 256 * ((Pl bs ^^^ NC k 10) &&& NC k 127) := by
      rw [e1]; simp only [NC]; exact peel_and _ _ hx (by omega) _ _
    have e3 : swarA (k + 1) (Pl (b :: bs)) =
        (((b ^^^ 10) &&& 127) + 127) + 256 * swarA k (Pl bs) := by
      unfold swarA; rw [e2]; simp only [NC]; omega
    have e4 : swar (k + 1) (Pl (b :: bs)) =
        ((((((b ^^^ 10) &&& 127) + 127) ||| (b ^^^ 10)) ||| 127)) + 256 * swar k (Pl bs) := by
      unfold swar; rw [e3, e1]; simp only [NC]
      rw [peel_or _ _ l1 hx, peel_or _ _ (by have := Nat.or_lt_two_pow (x := ((b ^^^ 10) &&& 127) + 127) (y := b ^^^ 10) (n := 8) (by simpa using l1) (by simpa using hx); simpa using this) (by omega)]
    have hlen : (b :: bs).length = k + 1 := by simp [hk]
    rw [hlen, e3, e4]
    simp only [List.map_cons, Pl, pow_succ]
    refine ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · have : 0 < 256 ^ k := Nat.pow_pos (by omega)
      omega

theorem u64_xor (a b : U64) : (a ^^^ b).val = a.val ^^^ b.val := by
  have h1 : (a ^^^ b).val = (a ^^^ b).bv.toNat := (UScalar.bv_toNat _).symm
  rw [h1, UScalar.bv_xor, BitVec.toNat_xor, UScalar.bv_toNat, UScalar.bv_toNat]
theorem u64_and (a b : U64) : (a &&& b).val = a.val &&& b.val := by
  have h1 : (a &&& b).val = (a &&& b).bv.toNat := (UScalar.bv_toNat _).symm
  rw [h1, UScalar.bv_and, BitVec.toNat_and, UScalar.bv_toNat, UScalar.bv_toNat]
theorem u64_or (a b : U64) : (a ||| b).val = a.val ||| b.val := by
  have h1 : (a ||| b).val = (a ||| b).bv.toNat := (UScalar.bv_toNat _).symm
  rw [h1, UScalar.bv_or, BitVec.toNat_or, UScalar.bv_toNat, UScalar.bv_toNat]
theorem u64_not (a : U64) : (~~~ a).val = 2 ^ 64 - 1 - a.val := by
  have h1 : (~~~ a).val = (~~~ a).bv.toNat := (UScalar.bv_toNat _).symm
  rw [h1]
  show (~~~ a.bv).toNat = _
  rw [BitVec.toNat_not, UScalar.bv_toNat]

theorem LOW7_val : lines.nl_mask.LOW7.val = NC 8 127 := by
  simp [lines.nl_mask.LOW7, NC]

theorem nl_mask_spec (w : U64) (bs : List Nat) (hl : bs.length = 8) (hb : ∀ b ∈ bs, b < 256)
    (hw : w.val = Pl bs) :
    lines.nl_mask w ⦃ r => r.val = Pl (bs.map gmask) ⦄ := by
  have hs := swar_spec bs hb
  rw [hl] at hs
  obtain ⟨s1, s2, s3⟩ := hs
  have c10 : (723401728380766730#u64).val = NC 8 10 := by simp [NC]
  unfold lines.nl_mask
  simp only [lift]
  step*
  · rw [u64_and, u64_xor, LOW7_val, c10, hw]
    have : swarA 8 (Pl bs) < 256 ^ 8 := s1
    simp only [swarA] at this
    have e : U64.max = 2 ^ 64 - 1 := by simp [U64.max, U64.numBits]
    rw [e]
    omega
  · rw [u64_not, u64_or, u64_or, i1_post, u64_and, u64_xor, LOW7_val, c10, hw]
    have : swar 8 (Pl bs) + Pl (bs.map gmask) = 256 ^ 8 - 1 := s3
    simp only [swar, swarA] at this
    simp
    omega


/-- The mark is `128` times the indicator of a newline. -/
def hmask (b : Nat) : Nat := if b = 10 then 1 else 0

theorem gmask_eq (b : Nat) : gmask b = 128 * hmask b := by
  unfold gmask hmask; split <;> simp

theorem Pl_gmask : ∀ bs : List Nat, Pl (bs.map gmask) = 128 * Pl (bs.map hmask)
  | [] => by simp [Pl]
  | b :: bs => by simp only [List.map_cons, Pl, gmask_eq, Pl_gmask bs]; omega

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mulsum : ∀ b0 < 2, ∀ b1 < 2, ∀ b2 < 2, ∀ b3 < 2, ∀ b4 < 2, ∀ b5 < 2, ∀ b6 < 2, ∀ b7 < 2,
    ((Pl [b0, b1, b2, b3, b4, b5, b6, b7] * NC 8 1) % 2 ^ 64) / 2 ^ 56 =
      b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 := by
  decide

theorem count_hmask : ∀ bs : List Nat, bs.count 10 = (bs.map hmask).sum
  | [] => by simp
  | b :: bs => by
    rw [List.count_cons, count_hmask bs]
    simp only [List.map_cons, List.sum_cons, hmask]
    split <;> simp_all <;> omega

theorem newline_count_spec (m : U64) (bs : List Nat) (hl : bs.length = 8)
    (hm : m.val = Pl (bs.map gmask)) :
    lines.newline_count m ⦃ r => r.val = bs.count 10 ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7, bs = [a0, a1, a2, a3, a4, a5, a6, a7] := by
    match bs, hl with
    | [a0, a1, a2, a3, a4, a5, a6, a7], _ => exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  have hm' : m.val = 128 * Pl ([a0, a1, a2, a3, a4, a5, a6, a7].map hmask) := by rw [hm, Pl_gmask]
  unfold lines.newline_count
  step*
  rw [UScalar.cast_val_eq]
  have c1 : (72340172838076673#u64).val = NC 8 1 := by simp [NC]
  have hi : i.val = Pl ([a0, a1, a2, a3, a4, a5, a6, a7].map hmask) := by
    rw [i_post, hm', Nat.shiftRight_eq_div_pow]; omega
  have hi1 : i1.val = (i.val * NC 8 1) % 2 ^ 64 := by
    have e : U64.size = 2 ^ 64 := by simp [U64.size, U64.numBits]
    rw [i1_post, core.num.U64.wrapping_mul_val_eq, c1]; simp [e]
  have hi2 : i2.val = i1.val / 2 ^ 56 := by rw [i2_post, Nat.shiftRight_eq_div_pow]
  have hb : ∀ x ∈ [a0, a1, a2, a3, a4, a5, a6, a7], x < 256 ∨ True := fun _ _ => Or.inr trivial
  have key := mulsum (hmask a0) (by unfold hmask; split <;> omega) (hmask a1) (by unfold hmask; split <;> omega)
    (hmask a2) (by unfold hmask; split <;> omega) (hmask a3) (by unfold hmask; split <;> omega)
    (hmask a4) (by unfold hmask; split <;> omega) (hmask a5) (by unfold hmask; split <;> omega)
    (hmask a6) (by unfold hmask; split <;> omega) (hmask a7) (by unfold hmask; split <;> omega)
  have hcnt : List.count 10 [a0, a1, a2, a3, a4, a5, a6, a7] =
      hmask a0 + hmask a1 + hmask a2 + hmask a3 + hmask a4 + hmask a5 + hmask a6 + hmask a7 := by
    rw [count_hmask]; simp [List.sum_cons]; omega
  have hfin : i2.val = List.count 10 [a0, a1, a2, a3, a4, a5, a6, a7] := by
    rw [hi2, hi1, hi, hcnt]
    simpa [List.map] using key
  have hlt : i2.val < 2 ^ UScalarTy.Usize.numBits := by
    rw [hfin, hcnt]
    have : ∀ b, hmask b ≤ 1 := fun b => by unfold hmask; split <;> omega
    have h0 := this a0; have h1 := this a1; have h2 := this a2; have h3 := this a3
    have h4 := this a4; have h5 := this a5; have h6 := this a6; have h7 := this a7
    have h32 : 32 ≤ UScalarTy.Usize.numBits := by
      cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]
    have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by omega) h32
    omega
  rw [Nat.mod_eq_of_lt hlt, hfin]

end difffold_myers_extract
