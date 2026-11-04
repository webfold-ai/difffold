import DifffoldMyers
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract
theorem hlen (a : Slice U32) (ha : a.val.length ≤ I32.max) : (UScalar.hcast IScalarTy.I32 a.len).val = (a.val.length : Int) := by
  rw [UScalar.hcast_val_eq]
  have h1 : (a.len.val : Int) = a.val.length := by simp [Slice.len]
  simp only [IScalarTy.numBits, h1] 
  have : (I32.max : Int) = 2147483647 := by scalar_tac
  rw [Int.bmod_eq_of_le] <;> omega
theorem hus (x : I32) (hx : 0 ≤ x.val) : (IScalar.hcast UScalarTy.Usize x).val = x.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have hb := x.hBounds
  have h32 : x.val < 2 ^ 31 := by scalar_tac
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> omega
end difffold_myers_extract
