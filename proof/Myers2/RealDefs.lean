import DifffoldReal
import RealCommon
import RealSnake
import Good
import Bound
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- A `back` function of the extraction only rewrites the two scratch arrays by the identity. -/
def BackId (b : lines.Search → lines.Search) : Prop := ∀ t, (b t).vf = t.vf ∧ (b t).vb = t.vb

/-- Precondition on the sizes of the two lists: keeps every `i32` quantity of the search far from overflow. -/
def NMAX : Nat := 2 ^ 28

/-- The search state is a faithful image of the two id lists. -/
def SInv (s : lines.Search) (A B : List Nat) : Prop :=
  vals s.a.val = A ∧ vals s.b.val = B ∧ s.n.val = (A.length : Int) ∧ s.m.val = (B.length : Int) ∧
  s.delta.val = (A.length : Int) - B.length ∧ (s.odd = true ↔ ((A.length : Int) - B.length) % 2 = 1) ∧
  s.off.val = (A.length : Int) + B.length + 1 ∧
  2 * (A.length + B.length) + 3 ≤ s.vf.val.length ∧ 2 * (A.length + B.length) + 3 ≤ s.vb.val.length ∧
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
/-- `snake_spec` with the size bounds the overflow checks need. -/
@[step]
theorem snake_step (a b : Slice U32) (x y : I32) (hx : 0 ≤ x.val) (hy : 0 ≤ y.val)
    (ha : a.val.length ≤ I32.max) (hb : b.val.length ≤ I32.max) :
    lines.snake a b x y ⦃ r => 0 ≤ r.val ∧ x.val + r.val ≤ max x.val a.val.length ∧
      y.val + r.val ≤ max y.val b.val.length ∧
      r.val = Myers.snake (vals a.val) (vals b.val) x.val.toNat y.val ⦄ := by
  have h := snake_spec a b x y hx hy ha hb
  have h1 := Myers.snake_le (vals a.val) (vals b.val) x.val.toNat y.val
  have h2 := Myers.snake_le_y (vals a.val) (vals b.val) x.val.toNat y.val
  simp only [vals, List.length_map] at h1 h2
  have hxn : (x.val.toNat : Int) = x.val := Int.toNat_of_nonneg hx
  exact Aeneas.Std.WP.spec_mono h (fun r hr => by
    simp only [vals] at hr
    refine ⟨by omega, by omega, by omega, hr⟩)
/-- Value that round `dn` starts from on diagonal `k`: the sentinel `0` in round 0, otherwise `X0`. -/
def X0v (A B : List Nat) : Nat → Int → Nat
  | 0, _ => 0
  | d' + 1, k => Myers.X0 A B d' k

theorem F_eq_X0v (A B : List Nat) (dn : Nat) (k : Int) :
    Myers.F A B dn k = X0v A B dn k + Myers.snake A B (X0v A B dn k) ((X0v A B dn k : Nat) - k) := by
  cases dn with
  | zero => simp [X0v, Myers.F_zero]
  | succ d => simp [X0v, Myers.F_succ]

theorem X0v_ge (A B : List Nat) (dn : Nat) (k : Int) (hk : Myers.Dom dn k) : k ≤ (X0v A B dn k : Int) := by
  cases dn with
  | zero => obtain ⟨h1, h2, _⟩ := hk; simp [X0v]; simp at h1 h2; omega
  | succ d => simpa [X0v] using Myers.X0_ge_k A B d k hk

theorem rd_val {v : Slice I32} {i : Usize} {e : I32} (h : v.val[i.val]? = some e) (hb : i.val < v.length) :
    v.val[i.val] = e := by
  have := List.getElem?_eq_getElem hb
  rw [this] at h; exact Option.some.inj h
end difffold_myers_extract

namespace difffold_myers_extract
theorem rdv {v : Slice I32} {off : Int} {G : Nat → Int → Nat} {d' : Nat}
    (hf : ∀ k, Myers.Dom d' k → ∃ e, v.val[(off + k).toNat]? = some e ∧ e.val = (G d' k : Int))
    (i : Usize) (k : Int) (hi : i.val = (off + k).toNat) (hk : Myers.Dom d' k) (hb : i.val < v.length) :
    (v.val[i.val]'hb).val = (G d' k : Int) := by
  obtain ⟨e, he, hv⟩ := hf k hk
  rw [← hi] at he
  have := rd_val he hb
  rw [this]; exact hv
end difffold_myers_extract
