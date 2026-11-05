import DifffoldReal
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem bv_and_not1 (x : BitVec 32) : x &&& ~~~(1#32) = (x >>> 1) <<< 1 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp
  · have hi1 : i - 1 + 1 < 32 := by omega
    simp [show ¬ i = 0 by omega]
    rw [show 1 + (i - 1) = i by omega, BitVec.getLsbD_eq_getElem hi]

theorem and_not1 (i : I32) (h : 0 ≤ i.val) : (i &&& (~~~(1#i32))).val = i.val - i.val % 2 := by
  have hbv : (i &&& (~~~(1#i32))).bv = (i.bv >>> 1) <<< 1 := by
    rw [IScalar.bv_and, IScalar.bv_not]; exact bv_and_not1 i.bv
  have h1 : (i &&& (~~~(1#i32))).val = (i.bv >>> 1 <<< 1).toInt := by
    rw [← hbv]; rfl
  rw [h1]
  have hi : i.val = i.bv.toInt := rfl
  rw [hi] at h ⊢
  have hx := i.bv.isLt
  simp only [BitVec.toInt_eq_toNat_cond] at h ⊢
  have e : ((i.bv >>> 1) <<< 1).toNat = i.bv.toNat / 2 * 2 := by
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  rw [e]
  split at h <;> split <;> omega


theorem and_one (i : I32) : (i &&& (1#i32)).val = i.val % 2 := by
  have hbv : (i &&& (1#i32)).bv = i.bv &&& 1#32 := by rw [IScalar.bv_and]; rfl
  have h1 : (i &&& (1#i32)).val = (i.bv &&& 1#32).toInt := by rw [← hbv]; rfl
  rw [h1]
  have hi : i.val = i.bv.toInt := rfl
  rw [hi]
  have hx := i.bv.isLt
  have e : (i.bv &&& 1#32).toNat = i.bv.toNat % 2 := by
    rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]
  simp only [BitVec.toInt_eq_toNat_cond]
  rw [e]
  split <;> split <;> omega

end difffold_myers_extract
