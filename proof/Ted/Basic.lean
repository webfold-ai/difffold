import DifffoldTed
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_lines_extract

/-! Step specifications of the small arithmetic helpers of `ted_core` (`umax`, `umin`, `adiff`, `min32`). -/

@[step] theorem umax_spec (x y : Std.Usize) : ted.umax x y ⦃ r => r.val = max x.val y.val ⦄ := by
  unfold ted.umax
  split
  · rename_i h; simp only [WP.spec_ok]; scalar_tac
  · rename_i h; simp only [WP.spec_ok]; scalar_tac

@[step] theorem umin_spec (x y : Std.Usize) : ted.umin x y ⦃ r => r.val = min x.val y.val ⦄ := by
  unfold ted.umin
  split
  · rename_i h; simp only [WP.spec_ok]; scalar_tac
  · rename_i h; simp only [WP.spec_ok]; scalar_tac

/-- `adiff x y = |x - y|`, written with truncated subtraction. -/
@[step] theorem adiff_spec (x y : Std.Usize) :
    ted.adiff x y ⦃ r => r.val = x.val - y.val + (y.val - x.val) ⦄ := by
  unfold ted.adiff
  split
  · rename_i h; step*; omega
  · rename_i h; step*

@[step] theorem min32_spec (x y : Std.U32) : ted.min32 x y ⦃ r => r.val = min x.val y.val ⦄ := by
  unfold ted.min32
  split
  · rename_i h; simp only [WP.spec_ok]; scalar_tac
  · rename_i h; simp only [WP.spec_ok]; scalar_tac

theorem getU_eq (l : List Std.U32) (i : Nat) (h : i < l.length) : l[i]! = l[i]'h := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getU_set_eq (l : List Std.U32) (i : Nat) (x : Std.U32) (h : i < l.length) :
    (l.set i x)[i]! = x := by
  simp [h]

theorem getU_set_ne (l : List Std.U32) (i j : Nat) (x : Std.U32) (h : j ≠ i) :
    (l.set i x)[j]! = l[j]! := by
  simp [Ne.symm h]

theorem clone_u32 (v : alloc.vec.Vec Std.U32) :
    alloc.vec.CloneVec.clone core.clone.CloneU32 v ⦃ r => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  have h := Slice.clone_spec (clone := core.clone.CloneU32.clone) (s := v.slice) (by intro x _; rfl)
  obtain ⟨s', hs', hh⟩ := WP.spec_imp_exists h
  rw [hs']
  simp only [bind_tc_ok, WP.spec_ok]
  rw [← hh]

theorem clone_vec_u32 (v : alloc.vec.Vec Std.U32) :
    alloc.vec.CloneVec.clone core.clone.CloneU32 v = ok v := by
  obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (clone_u32 v)
  rw [hr, hh]

end difffold_lines_extract
