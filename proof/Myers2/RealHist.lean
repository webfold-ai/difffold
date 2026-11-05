import RealDiffIds
import HistPure
import RealIntern
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-! Soundness of the histogram differ `diff_histogram_ids` of `src/lines.rs` over the Aeneas translation of the
real source: the flags it returns form a valid edit script (the lines kept on the two sides are equal lists).
Nothing is claimed about optimality. -/

/-- The index structure built by `index_a` over `a[alo..p)`: chain heads, links, and counts. -/
structure IdxOK (a : Slice U32) (alo p : Nat) (h : lines.Hist) : Prop where
  i1 : ∀ (k : Nat) x, h.head.val[k]? = some x → x = lines.NIL ∨
    (alo ≤ x.val ∧ x.val < p ∧ ∃ u, a.val[x.val]? = some u ∧ u.val = k)
  i2 : ∀ (j : Nat) y, alo ≤ j → j < p → h.nxt.val[j]? = some y → y = lines.NIL ∨
    (alo ≤ y.val ∧ y.val < j ∧ ∃ u, a.val[y.val]? = some u ∧ a.val[j]? = some u)
  i3 : ∀ (k : Nat) c, h.cnt.val[k]? = some c → c.val ≤ p - alo ∧
    (0 < c.val → ∃ j, alo ≤ j ∧ j < p ∧ ∃ u, a.val[j]? = some u ∧ u.val = k)

/-- Sizes of the arrays of the histogram state. -/
structure HSz (A B n : Nat) (h : lines.Hist) : Prop where
  cnt : h.cnt.val.length = n
  head : h.head.val.length = n
  nxt : h.nxt.val.length = A
  del : h.del.val.length = A
  ins : h.ins.val.length = B
  vf : 2 * (A + B) + 3 ≤ h.vf.val.length
  vb : 2 * (A + B) + 3 ≤ h.vb.val.length

/-- The state between two `hist` calls: no chain heads and no counts. -/
def HClean (h : lines.Hist) : Prop :=
  (∀ (k : Nat) x, h.head.val[k]? = some x → x = lines.NIL) ∧ (∀ (k : Nat) c, h.cnt.val[k]? = some c → c.val = 0)

theorem NIL_ne_of_lt (x : U32) (h : x.val < 4294967295) : x ≠ lines.NIL := by
  intro e; rw [e, NIL_val] at h; omega

theorem index_a_loop_spec (a : Slice U32) (n alo : Nat) (ahi : Usize)
    (hid : ∀ x ∈ a.val, x.val < n) (hahi : ahi.val ≤ a.val.length) (hN : a.val.length ≤ 2 ^ 28) :
    ∀ (h : lines.Hist) (i : Usize), alo ≤ i.val → i.val ≤ ahi.val → HSz a.val.length 0 n h →
    IdxOK a alo i.val h →
    lines.index_a_loop a h ahi i ⦃ h' => HSz a.val.length 0 n h' ∧ IdxOK a alo ahi.val h' ∧
      h'.del = h.del ∧ h'.ins = h.ins ∧ h'.vf = h.vf ∧ h'.vb = h.vb ⦄ := by
  intro h i hi1 hi2 hs hI
  unfold lines.index_a_loop
  apply loop.spec_decr_nat (fun (x : lines.Hist × Usize) => ahi.val - x.2.val)
    (fun (x : lines.Hist × Usize) => alo ≤ x.2.val ∧ x.2.val ≤ ahi.val ∧ HSz a.val.length 0 n x.1 ∧
      IdxOK a alo x.2.val x.1 ∧ x.1.del = h.del ∧ x.1.ins = h.ins ∧ x.1.vf = h.vf ∧ x.1.vb = h.vb) _ _ (h, i)
  · rintro ⟨h1, i1⟩ ⟨hi1, hi2, hs1, hI1, hd, hin, hvf, hvb⟩
    simp only at hi1 hi2 hs1 hI1 hd hin hvf hvb
    unfold lines.index_a_loop.body
    step*
    all_goals (trace_state; sorry)
  · exact ⟨hi1, hi2, hs, hI, rfl, rfl, rfl, rfl⟩

end difffold_myers_extract
