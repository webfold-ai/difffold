import Mirror2
import Stats
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! `check_core` accepts exactly the legal tree edit mappings. -/

theorem preorder_loop_spec (a : ted.PostTree) (hW : PT.Wf a) (n : Std.Usize) (depth pre : alloc.vec.Vec Std.Usize)
    (x : Std.Usize) (hn : n.val = a.label.length) (hx : x.val ≤ a.label.length)
    (hdl : depth.length = a.label.length) (hpl : pre.length = a.label.length)
    (hD : ∀ c, 1 ≤ c → c ≤ a.label.length → (depth.val[c - 1]!).val = dep (laOf a) a.label.length c)
    (hP : ∀ y < x.val, (pre.val[y]!).val = Ted.pre (laOf a) a.label.length (y + 1)) :
    ted.preorder_loop a.lml n depth pre x ⦃ r =>
      r.length = a.label.length ∧ ∀ y < a.label.length, (r.val[y]!).val = Ted.pre (laOf a) a.label.length (y + 1) ⦄ := by
  unfold ted.preorder_loop
  apply loop.spec_decr_nat
    (measure := fun s => a.label.length - s.2.val)
    (inv := fun s => s.2.val ≤ a.label.length ∧ s.1.length = a.label.length ∧
      ∀ y < s.2.val, (s.1.val[y]!).val = Ted.pre (laOf a) a.label.length (y + 1))
  · intro s hs
    obtain ⟨pre1, x1⟩ := s
    obtain ⟨hs1, hs2, hs3⟩ := hs
    dsimp only at hs1 hs2 hs3 ⊢
    unfold ted.preorder_loop.body
    by_cases hxn : x1 < n
    · rw [if_pos hxn]
      have hxn' : x1.val < a.label.length := by have : x1.val < n.val := hxn; omega
      have hlml : a.lml.val.length = a.label.length := hW.n2
      have hlml' : a.lml.length = a.label.length := hW.n2
      have hdl' : depth.val.length = a.label.length := hdl
      step as ⟨i, hi⟩
      have hi' : i.val = laOf a (x1.val + 1) := by
        rw [laOf_eq a _ hxn', hi, getG_eq _ _ (by omega)]
      step as ⟨l, hl⟩
      have hl' : l.val = laOf a (x1.val + 1) := by rw [hl, U32.cast_Usize_val_eq]; exact hi'
      step as ⟨d, hd⟩
      have hd' : d.val = dep (laOf a) a.label.length (x1.val + 1) := by
        rw [hd]
        have := hD (x1.val + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at this
        rw [← this, getG_eq _ _ (by omega)]
      have hpre := pre_le_n hW.wfl (n := a.label.length) (u := x1.val + 1) (by omega) (by omega)
      unfold Ted.pre at hpre
      step as ⟨v1, hv1⟩
      step as ⟨old, imb, ho, himb⟩
      have hset : (imb v1).val = pre1.val.set x1.val v1 := by
        rw [himb, alloc.vec.Vec.set_val_eq]
      step as ⟨x2, hx2⟩
      have hp1 : pre1.val.length = a.label.length := hs2
      refine ⟨by omega, ?_, ?_, by omega⟩
      · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hs2
      · intro y hy
        rw [hset]
        by_cases hyx : y = x1.val
        · subst hyx
          rw [getG_set_eq _ _ _ (by omega)]
          unfold Ted.pre; omega
        · rw [getG_set_ne _ _ _ _ hyx]
          exact hs3 y (by omega)
    · rw [if_neg hxn]
      simp only [WP.spec_ok]
      have : x1.val = a.label.length := by
        have : ¬ x1.val < n.val := hxn
        omega
      refine ⟨hs2, ?_⟩
      intro y hy
      exact hs3 y (by omega)
  · exact ⟨hx, hpl, hP⟩

theorem preorder_spec (a : ted.PostTree) (hW : PT.Wf a) :
    ted.preorder a ⦃ r => r.length = a.label.length ∧
      ∀ x, 1 ≤ x → x ≤ a.label.length → (r.val[x - 1]!).val = Ted.pre (laOf a) a.label.length x ⦄ := by
  unfold ted.preorder
  have hlenv := alloc.vec.Vec.len_val a.label
  refine WP.spec_bind (depths_spec a hW) ?_
  rintro depth ⟨hdl, hD⟩
  step as ⟨pre, hpre, hpl⟩
  refine WP.spec_mono (preorder_loop_spec a hW a.label.len depth pre 0#usize hlenv (by simp) hdl
    (by rw [hpl]; exact hlenv) hD (by simp)) ?_
  rintro r ⟨h1, h2⟩
  refine ⟨h1, fun x hx1 hx2 => ?_⟩
  have := h2 (x - 1) (by omega)
  have e : x - 1 + 1 = x := by omega
  rw [e] at this; exact this

end difffold_lines_extract
