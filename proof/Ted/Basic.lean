import DifffoldTed
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_lines_extract

/-! Step specifications of the small arithmetic helpers of `ted_core` (`umax`, `umin`, `adiff`, `min32`). -/

@[step] theorem umax_spec (x y : Std.Usize) : ted_core.umax x y ⦃ r => r.val = max x.val y.val ⦄ := by
  unfold ted_core.umax
  split
  · rename_i h; simp only [WP.spec_ok]; scalar_tac
  · rename_i h; simp only [WP.spec_ok]; scalar_tac

@[step] theorem umin_spec (x y : Std.Usize) : ted_core.umin x y ⦃ r => r.val = min x.val y.val ⦄ := by
  unfold ted_core.umin
  split
  · rename_i h; simp only [WP.spec_ok]; scalar_tac
  · rename_i h; simp only [WP.spec_ok]; scalar_tac

/-- `adiff x y = |x - y|`, written with truncated subtraction. -/
@[step] theorem adiff_spec (x y : Std.Usize) :
    ted_core.adiff x y ⦃ r => r.val = x.val - y.val + (y.val - x.val) ⦄ := by
  unfold ted_core.adiff
  split
  · rename_i h; step*; omega
  · rename_i h; step*

@[step] theorem min32_spec (x y : Std.U32) : ted_core.min32 x y ⦃ r => r.val = min x.val y.val ⦄ := by
  unfold ted_core.min32
  split
  · rename_i h; simp only [WP.spec_ok]; scalar_tac
  · rename_i h; simp only [WP.spec_ok]; scalar_tac

end difffold_lines_extract
