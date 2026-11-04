import DifffoldLines
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_lines_extract

/-! The SWAR newline mask `nl_mask` (extraction copy `lines_core`; the body is identical to `lines.rs`). -/

theorem L7 : lines_core.nl_mask.LOW7.bv = 0x7F7F7F7F7F7F7F7F#64 := by
  simp [lines_core.nl_mask.LOW7]

theorem L7v : lines_core.nl_mask.LOW7.val = 9187201950435737471 := by
  simp [lines_core.nl_mask.LOW7]

def nlBV (w : BitVec 64) : BitVec 64 :=
  let x := w ^^^ 0x0A0A0A0A0A0A0A0A#64
  ~~~((((x &&& 0x7F7F7F7F7F7F7F7F#64) + 0x7F7F7F7F7F7F7F7F#64) ||| x) ||| 0x7F7F7F7F7F7F7F7F#64)

/-- `nl_mask` computes the pure bit-vector function `nlBV` (and its internal addition cannot overflow). -/
theorem nl_mask_bv (w : U64) : lines_core.nl_mask w ⦃ m => m.bv = nlBV w.bv ⦄ := by
  unfold lines_core.nl_mask
  step*
  · have h1 : i.val ≤ lines_core.nl_mask.LOW7.val := by
      rw [i_post]; simp [UScalar.val_and]; exact Nat.and_le_right
    rw [L7v] at h1 ⊢
    scalar_tac
  · have h1 : i.val ≤ lines_core.nl_mask.LOW7.val := by
      rw [i_post]; simp [UScalar.val_and]; exact Nat.and_le_right
    have hb : i1.bv = i.bv + lines_core.nl_mask.LOW7.bv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      simp only [UScalar.bv_toNat]
      rw [i1_post]
      rw [L7v] at h1 ⊢
      omega
    simp only [UScalar.bv_not, i3_post1, i2_post1, hb, i_post1, x_post1, L7, nlBV]
    rfl

/-- Only the high bit of each byte can be set. -/
theorem nlBV_low (w : BitVec 64) : nlBV w &&& 0x7F7F7F7F7F7F7F7F#64 = 0#64 := by
  unfold nlBV; bv_decide

/-- SWAR exactness: the high bit of byte `k` of the mask is set iff byte `k` of the word is `0x0A`. -/
theorem nlBV_bit (w : BitVec 64) (k : Nat) (hk : k < 8) :
    (nlBV w).getLsbD (8 * k + 7) = decide (w.extractLsb' (8 * k) 8 = 0x0A#8) := by
  unfold nlBV
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceMul, Nat.reduceAdd] <;> bv_decide
end difffold_lines_extract
