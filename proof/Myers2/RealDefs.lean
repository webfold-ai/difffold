import DifffoldReal
import RealCommon
import RealSnake
import Good
import Bound
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- Precondition on the sizes of the two lists: keeps every `i32` quantity of the search far from overflow. -/
def NMAX : Nat := 2 ^ 28

/-- The search state is a faithful image of the two id lists. -/
def SInv (s : lines.Search) (A B : List Nat) : Prop :=
  vals s.a.val = A ∧ vals s.b.val = B ∧ s.n.val = (A.length : Int) ∧ s.m.val = (B.length : Int) ∧
  s.delta.val = (A.length : Int) - B.length ∧ (s.odd = true ↔ ((A.length : Int) - B.length) % 2 = 1) ∧
  s.off.val = (A.length : Int) + B.length + 1 ∧
  s.vf.val.length = 2 * (A.length + B.length) + 3 ∧ s.vb.val.length = 2 * (A.length + B.length) + 3 ∧
  A.length + B.length ≤ NMAX

/-- Array `v` holds the values `G d' k` on the diagonals of round `d'`, where `d = d' + 1`; for `d = 0` it
holds the sentinel `0` at `off + 1`. This is what round `d` of the search reads. -/
def RdyArr (v : Slice I32) (off : Int) (G : Nat → Int → Nat) : Nat → Prop
  | 0 => ∃ e, v.val[(off + 1).toNat]? = some e ∧ e.val = 0
  | d' + 1 => ∀ k, Myers.Dom d' k → ∃ e, v.val[(off + k).toNat]? = some e ∧ e.val = (G d' k : Int)

/-- `v'` is `v` with position `idx` set to `x`. -/
def Upd (v v' : Slice I32) (idx : Nat) (x : Int) : Prop :=
  v'.val.length = v.val.length ∧ idx < v.val.length ∧ (∃ e, v'.val[idx]? = some e ∧ e.val = x) ∧
  ∀ j, j ≠ idx → v'.val[j]? = v.val[j]?

end difffold_myers_extract

namespace difffold_myers_extract
@[step]
theorem Search_ix_spec (s : lines.Search) (k : I32) (h0 : 0 ≤ s.off.val + k.val)
    (h1 : s.off.val + k.val ≤ I32.max) :
    lines.Search.ix s k ⦃ r => r.val = (s.off.val + k.val).toNat ⦄ := by
  unfold lines.Search.ix
  step*
  have := hus i (by scalar_tac)
  simp [*]
end difffold_myers_extract

namespace difffold_myers_extract
/-- Value that round `dn` starts from on diagonal `k`: the sentinel `0` in round 0, otherwise `X0`. -/
def X0v (A B : List Nat) : Nat → Int → Nat
  | 0, _ => 0
  | d' + 1, k => Myers.X0 A B d' k

theorem F_eq_X0v (A B : List Nat) (dn : Nat) (k : Int) :
    Myers.F A B dn k = X0v A B dn k + Myers.snake A B (X0v A B dn k) ((X0v A B dn k : Nat) - k) := by
  cases dn with
  | zero => simp [X0v, Myers.F_zero]
  | succ d => simp [X0v, Myers.F_succ]

theorem rd_val {v : Slice I32} {i : Usize} {e : I32} (h : v.val[i.val]? = some e) (hb : i.val < v.length) :
    v.val[i.val] = e := by
  have := List.getElem?_eq_getElem hb
  rw [this] at h; exact Option.some.inj h
end difffold_myers_extract
