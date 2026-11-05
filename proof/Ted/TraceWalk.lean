import Trace
import TraceDefs
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The walk through one window table. -/

/-- The trees and the threshold. -/
structure TT (a b : ted.PostTree) (T : Nat) : Prop where
  hA : PT.Wf a
  hB : PT.Wf b
  hna : a.label.length < 2 ^ 14
  hnb : b.label.length < 2 ^ 14
  hT : T ≤ a.label.length + b.label.length
  hted : TED a b ≤ T

/-- The context of the window of the subtree pair `(i, j)`. -/
abbrev Cw (a b : ted.PostTree) (T i j : Nat) : Ctx := (mkCtx a b T).win i j

/-- Facts about the tables at a window. -/
structure WinOk (a b : ted.PostTree) (T i j : Nat) (td fd : alloc.vec.Vec Std.U32) : Prop where
  hi : 1 ≤ i ∧ i ≤ a.label.length
  hj : 1 ≤ j ∧ j ≤ b.label.length
  tdlen : (a.label.length + 1) * (2 * T + 1) ≤ td.length
  fdlen : ((Cw a b T i j).si + 1) * (2 * T + 1) ≤ fd.length
  rows : (Cw a b T i j).RowsInv fd.val ((Cw a b T i j).si + 1) 1
  fdB : Ctx.FdB fd.val (T + 1)
  tdB : Ctx.FdB td.val (T + 1)
  tdinv : (mkCtx a b T).GInv td.val (fun _ _ => True)

/-- What the inner loop keeps true. -/
structure WInv (a b : ted.PostTree) (T i j Sb : Nat) (to_b stack_i stack_j : alloc.vec.Vec Std.Usize)
    (top p q : Nat) : Prop where
  tblen : to_b.length = a.label.length + 1
  stl : stack_i.length = stack_j.length
  topl : top ≤ stack_i.length
  stmax : stack_i.length ≤ a.label.length + b.label.length
  pq : p ≤ (Cw a b T i j).si ∧ q ≤ (Cw a b T i j).sj
  budget : Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p q + (Cw a b T i j).δ ≤ T
  tinv : TInv (laOf a) (laOf b) (rcost a b) a.label.length b.label.length (Pto a.label.length to_b.val)
    (stk stack_i.val stack_j.val top) (laOf a i) (laOf a i + p - 1) (laOf b j) (laOf b j + q - 1)
  stok : ∀ w ∈ stk stack_i.val stack_j.val top, 1 ≤ w.1 ∧ w.1 ≤ a.label.length ∧ 1 ≤ w.2 ∧ w.2 ≤ b.label.length ∧
    TD (laOf a) (laOf b) (rcost a b) w.1 w.2 + adf (laOf a w.1) (laOf b w.2) ≤ T
  ssum_le : ssum (laOf a) (laOf b) (stk stack_i.val stack_j.val top) + p + q ≤ Sb + (Cw a b T i j).si + (Cw a b T i j).sj
  ssum_lt : (p = (Cw a b T i j).si ∧ q = (Cw a b T i j).sj) ∨
    ssum (laOf a) (laOf b) (stk stack_i.val stack_j.val top) + p + q + 1 ≤ Sb + (Cw a b T i j).si + (Cw a b T i j).sj
  ssum_max : ssum (laOf a) (laOf b) (stk stack_i.val stack_j.val top) ≤ a.label.length + b.label.length

end difffold_lines_extract
