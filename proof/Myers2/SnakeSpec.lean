import DifffoldMyers
import CommonCopy
import CpreChar
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- The ids of a slice of `u32` as naturals, the lists the pure model `Myers.snake` works on. -/
def vals (l : List U32) : List Nat := l.map (fun u => u.val)

theorem snake_spec (a b : Slice U32) (x y : I32) (hx : 0 ≤ x.val) (hy : 0 ≤ y.val)
    (ha : a.val.length ≤ I32.max) (hb : b.val.length ≤ I32.max) :
    mcore.snake a b x y ⦃ r => r.val = Myers.snake (vals a.val) (vals b.val) x.val.toNat y.val ⦄ := by
  unfold mcore.snake
  step*
  all_goals (trace_state; sorry)

end difffold_myers_extract
