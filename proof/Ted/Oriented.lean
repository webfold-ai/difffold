import DifffoldTed
import Basic
import Cell
import Truth
import Window
import LabelLB
import Kr
import Driver
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The doubling loop `ted_oriented`: it returns the exact distance. -/

/-- The context with another threshold. -/
def Ctx.withT (C : Ctx) (T : Nat) : Ctx := { C with t := T }

theorem Ctx.ted_withT (C : Ctx) (T : Nat) : (C.withT T).ted = C.ted := rfl

theorem ted_le_cap (C : Ctx) (hn : 1 ≤ C.n) (hm : 1 ≤ C.m) : C.ted ≤ C.n + C.m := by
  have := D_size C.la C.lb C.ren _ 1 C.n 1 C.m (by omega) (by omega) rfl
  unfold Ctx.ted; omega

end difffold_lines_extract
