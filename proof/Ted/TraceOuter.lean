import TraceWalk
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The outer loop of the traceback: pop a window, rebuild its table, walk it. -/

theorem stk_snoc_self (si sj : List Std.Usize) (k : Nat) :
    stk si sj (k + 1) = stk si sj k ++ [((si[k]!).val, (sj[k]!).val)] :=
  stk_push (fun _ _ => ⟨rfl, rfl⟩) rfl rfl

theorem stk_zero (si sj : List Std.Usize) : stk si sj 0 = [] := rfl

namespace Ctx

/-- Rebuilding the table of a window keeps every entry of the subtree-distance table exact. -/
theorem ginv_true_step (C : Ctx) (hA : WfL C.la) (hB : WfL C.lb) {i0 j0 : Nat}
    {td0 td : List Std.U32} (hG0 : C.GInv td0 (fun _ _ => True))
    (hF : (C.win i0 j0).Frame td0 td) (hT : (C.win i0 j0).TdInv td ((C.win i0 j0).si + 1) 1) :
    C.GInv td (fun _ _ => True) := by
  intro x y hx1 hxn hy1 hym
  have hTx := hT x y hx1 hxn hy1 hym
  refine ⟨hTx.1, fun _ hb => ?_⟩
  by_cases hl : (C.win i0 j0).LeafPair x y ∧ x ≤ (C.win i0 j0).i0 ∧ y ≤ (C.win i0 j0).j0
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hl
    have h1' : C.la x = C.la i0 := h1
    have h2' : C.lb y = C.lb j0 := h2
    have h3' : x ≤ i0 := h3
    have h4' : y ≤ j0 := h4
    have hlex := (hA.1 x hx1).2
    have hley := (hB.1 y hy1).2
    refine hTx.2 ?_ hb
    refine ⟨?_, ?_, h3, h4, Or.inr ⟨⟨h1, h2⟩, Or.inl ?_⟩⟩
    · show C.la i0 ≤ x
      omega
    · show C.lb j0 ≤ y
      omega
    · show x < C.la i0 + (i0 - C.la i0 + 1 + 1) - 1
      omega
  · exact (hF x y hl).trans ((hG0 x y hx1 hxn hy1 hym).2 trivial hb)

theorem tdinv_of_ginv (C : Ctx) {td : List Std.U32} (h : C.GInv td (fun _ _ => True)) (p q : Nat) :
    C.TdInv td p q :=
  fun x y a b c d => ⟨(h x y a b c d).1, fun _ hb => (h x y a b c d).2 trivial hb⟩

end Ctx

/-- What the outer loop keeps true between two windows. -/
structure OS (a b : ted.PostTree) (T : Nat) (td to_b stack_i stack_j : alloc.vec.Vec _) (top : Nat) : Prop where
  tdlen : (a.label.length + 1) * (2 * T + 1) ≤ td.length
  tdB : Ctx.FdB td.val (T + 1)
  tdinv : (mkCtx a b T).GInv td.val (fun _ _ => True)
  tblen : to_b.length = a.label.length + 1
  stl : stack_i.length = stack_j.length
  topl : top ≤ stack_i.length
  stmax : stack_i.length ≤ a.label.length + b.label.length
  stok : ∀ w ∈ stk stack_i.val stack_j.val top, 1 ≤ w.1 ∧ w.1 ≤ a.label.length ∧ 1 ≤ w.2 ∧ w.2 ≤ b.label.length ∧
    TD (laOf a) (laOf b) (rcost a b) w.1 w.2 + adf (laOf a w.1) (laOf b w.2) ≤ T
  ssum_max : ssum (laOf a) (laOf b) (stk stack_i.val stack_j.val top) ≤ a.label.length + b.label.length
  oinv : OInv (laOf a) (laOf b) (rcost a b) a.label.length b.label.length (Pto a.label.length to_b.val)
    (stk stack_i.val stack_j.val top)

set_option maxHeartbeats 1600000 in
theorem outer_spec (a b : ted.PostTree) (prefer_match : Bool) {T : Nat} (tt : TT a b T) (cost : Std.U32)
    (hc : cost.val = T) (t w : Std.Usize) (inf : Std.U32) (ht : t.val = T) (hw : w.val = 2 * T + 1)
    (hinf : inf.val = T + 1) (st : ted.Stats) (td : alloc.vec.Vec Std.U32)
    (to_b stack_i stack_j : alloc.vec.Vec Std.Usize) (top : Std.Usize)
    (hS : OS a b T td to_b stack_i stack_j top.val) :
    ted.traceback_loop0 a.label a.lml a.keyroots a.kids a.kind b.label b.lml b.keyroots b.kids b.kind cost
      prefer_match st td t inf w to_b stack_i stack_j top ⦃ r =>
      r.length = a.label.length + 1 ∧
        Sol (laOf a) (laOf b) (rcost a b) 1 a.label.length 1 b.label.length (Pto a.label.length r.val) ⦄ := by
  unfold ted.traceback_loop0
  have hUM : 2 ^ 32 ≤ Std.Usize.max + 1 := by scalar_tac
  have hA := tt.hA
  have hB := tt.hB
  have hna := tt.hna
  have hnb := tt.hnb
  have hTn := tt.hT
  apply loop.spec_decr_nat
    (measure := fun s => ssum (laOf a) (laOf b) (stk s.2.2.2.1.val s.2.2.2.2.1.val s.2.2.2.2.2.val))
    (inv := fun s => OS a b T s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.val)
  · intro s hs
    obtain ⟨st1, td1, to_b1, stack_i1, stack_j1, top1⟩ := s
    dsimp only at hs ⊢
    unfold ted.traceback_loop0.body
    by_cases hz : top1 > 0#usize
    · rw [if_pos hz]
      have hz' : 0 < top1.val := hz
      have htl := hs.topl
      have hstl := hs.stl
      have hstm := hs.stmax
      have htl' : top1.val ≤ stack_i1.val.length := htl
      have hstl' : stack_i1.val.length = stack_j1.val.length := hstl
      step as ⟨topm, htopm⟩
      step as ⟨i, hi⟩
      step as ⟨j, hj⟩
      have hiv : i.val = (stack_i1.val[topm.val]!).val := by rw [hi, getG_eq _ _ (by omega)]
      have hjv : j.val = (stack_j1.val[topm.val]!).val := by rw [hj, getG_eq _ _ (by omega)]
      have hstk : stk stack_i1.val stack_j1.val top1.val =
          stk stack_i1.val stack_j1.val topm.val ++ [(i.val, j.val)] := by
        have e : top1.val = topm.val + 1 := by omega
        rw [e, stk_snoc_self, hiv, hjv]
      have hmem : (i.val, j.val) ∈ stk stack_i1.val stack_j1.val top1.val := by
        rw [hstk]; exact List.mem_append_right _ (List.mem_singleton_self _)
      have hi1 : 1 ≤ i.val := (hs.stok _ hmem).1
      have hin : i.val ≤ a.label.length := (hs.stok _ hmem).2.1
      have hj1 : 1 ≤ j.val := (hs.stok _ hmem).2.2.1
      have hjm : j.val ≤ b.label.length := (hs.stok _ hmem).2.2.2.1
      have hbud : TD (laOf a) (laOf b) (rcost a b) i.val j.val + adf (laOf a i.val) (laOf b j.val) ≤ T :=
        (hs.stok _ hmem).2.2.2.2
      have hlml : a.lml.val.length = a.label.length := hA.n2
      have hlmlb : b.lml.val.length = b.label.length := hB.n2
      step as ⟨i1, hi1'⟩
      step as ⟨i2, hi2⟩
      step as ⟨li, hli⟩
      have hliv : li.val = laOf a i.val := by
        rw [laOf_eq1 a _ hi1 hin, hli, U32.cast_Usize_val_eq, hi2, getG_eq _ _ (by omega)]
        simp only [hi1']
      step as ⟨i3, hj1'⟩
      step as ⟨i4, hi4⟩
      step as ⟨lj, hlj⟩
      have hljv : lj.val = laOf b j.val := by
        rw [laOf_eq1 b _ hj1 hjm, hlj, U32.cast_Usize_val_eq, hi4, getG_eq _ _ (by omega)]
        simp only [hj1']
      have hliP : 1 ≤ laOf a i.val := (hA.wfl.1 i.val hi1).1
      have hleP : laOf a i.val ≤ i.val := (hA.wfl.1 i.val hi1).2
      have hljP : 1 ≤ laOf b j.val := (hB.wfl.1 j.val hj1).1
      have hlejP : laOf b j.val ≤ j.val := (hB.wfl.1 j.val hj1).2
      step as ⟨i5, hi5⟩
      step as ⟨si, hsi⟩
      step as ⟨i6, hi6⟩
      step as ⟨sj, hsj⟩
      step as ⟨i7, hi7⟩
      have hwb : w.val ≤ 2 ^ 16 := by rw [hw]; omega
      have hbig8 : i7.val * w.val ≤ Std.Usize.max := by
        have h1 : i7.val * w.val ≤ 2 ^ 14 * 2 ^ 16 := Nat.mul_le_mul (by omega) hwb
        omega
      step as ⟨i8, hi8⟩
      step as ⟨fd, hfd1, hfd2⟩
      simp only [lift, bind_tc_ok, alloc.vec.Vec.deref_mut]
      have hsiv : si.val = i.val - laOf a i.val + 1 := by omega
      have hsjv : sj.val = j.val - laOf b j.val + 1 := by omega
      have hi8v : i8.val = (si.val + 1) * w.val := by rw [hi8, hi7]
      have hfdlen : fd.val.length = (si.val + 1) * w.val := by
        have : fd.val.length = i8.val := hfd2
        rw [this, hi8v]
      have hGood := Ctx.win_good (mkCtx a b T) hA.wfl hB.wfl hi1 hin hj1 hjm
      have hK := (mkCtx_link a b hA hB hna hnb T hTn).win i.val j.val
      have hFBfd : Ctx.FdB fd.val (T + 1) := by rw [hfd1]; exact fdb_replicate _ _ _ hinf
      have hsiC : ((mkCtx a b T).win i.val j.val).si = si.val := by
        show i.val - laOf a i.val + 1 = si.val
        omega
      have hsjC : ((mkCtx a b T).win i.val j.val).sj = sj.val := by
        show j.val - laOf b j.val + 1 = sj.val
        omega
      step with fill_window_spec ((mkCtx a b T).win i.val j.val) hGood a b hK rfl hliP hljP td1.slice fd.slice
        false st1 i j cost rfl rfl hc
        (by rw [hsiC]; show (si.val + 1) * (2 * T + 1) ≤ fd.val.length; rw [hfdlen, hw]) hs.tdlen hFBfd hs.tdB
        (Ctx.tdinv_of_ginv ((mkCtx a b T).win i.val j.val) hs.tdinv 1 1) as ⟨r, r2, st2, e3, e4, e5, e6, e7, e8, e9⟩
      have hssum := ssum_append (laOf a) (laOf b) (stk stack_i1.val stack_j1.val topm.val) (i.val, j.val)
      rw [← hstk] at hssum
      have hSb : ssum (laOf a) (laOf b) (stk stack_i1.val stack_j1.val topm.val) + ((mkCtx a b T).win i.val j.val).si
          + ((mkCtx a b T).win i.val j.val).sj ≤ a.label.length + b.label.length := by
        have := hs.ssum_max
        rw [hsiC, hsjC]
        simp only at hssum
        omega
      have hWinOk : WinOk a b T i.val j.val ({ slice := r } : alloc.vec.Vec Std.U32) { slice := r2 } := by
        refine ⟨⟨hi1, hin⟩, ⟨hj1, hjm⟩, ?_, ?_, e9, e8, e4, ?_⟩
        · show (a.label.length + 1) * (2 * T + 1) ≤ r.val.length
          rw [e3]; exact hs.tdlen
        · show (((mkCtx a b T).win i.val j.val).si + 1) * (2 * T + 1) ≤ r2.val.length
          rw [hsiC, e7]
          show _ ≤ fd.val.length
          rw [hfdlen, hw]
        · exact Ctx.ginv_true_step (mkCtx a b T) hA.wfl hB.wfl hs.tdinv e6 e5
      have hW : WCtx a b T i.val j.val (ssum (laOf a) (laOf b) (stk stack_i1.val stack_j1.val topm.val))
          ({ slice := r } : alloc.vec.Vec Std.U32) { slice := r2 } := ⟨tt, hWinOk, hSb⟩
      have e1 : laOf a i.val + si.val - 1 = i.val := by omega
      have e2 : laOf b j.val + sj.val - 1 = j.val := by omega
      have hTinv0 : TInv (laOf a) (laOf b) (rcost a b) a.label.length b.label.length
          (Pto a.label.length to_b1.val) (stk stack_i1.val stack_j1.val topm.val)
          (laOf a i.val) i.val (laOf b j.val) j.val := by
        have := hs.oinv
        rw [hstk] at this
        exact tinv_pop this
      have hWinit : WInv a b T i.val j.val (ssum (laOf a) (laOf b) (stk stack_i1.val stack_j1.val topm.val))
          to_b1 stack_i1 stack_j1 topm.val si.val sj.val := by
        refine ⟨hs.tblen, hs.stl, by omega, hs.stmax, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact Nat.le_of_eq hsiC.symm
        · exact Nat.le_of_eq hsjC.symm
        · show D (laOf a) (laOf b) (rcost a b) (laOf a i.val) (laOf a i.val + si.val - 1) (laOf b j.val)
            (laOf b j.val + sj.val - 1) + adf (laOf a i.val) (laOf b j.val) ≤ T
          rw [e1, e2]; exact hbud
        · rw [e1, e2]; exact hTinv0
        · intro w hw'
          exact hs.stok w (by rw [hstk]; exact List.mem_append_left _ hw')
        · show _ ≤ _ + ((mkCtx a b T).win i.val j.val).si + ((mkCtx a b T).win i.val j.val).sj
          rw [hsiC, hsjC]
        · exact Or.inl ⟨hsiC.symm, hsjC.symm⟩
        · have := hs.ssum_max
          simp only at hssum
          omega
      step with walk_spec a b prefer_match hW t w inf li lj ht hw hinf hliv hljv to_b1 stack_i1 stack_j1 topm si sj
        hWinit as ⟨to_b2, si2, sj2, top2, hW2⟩
      refine ⟨⟨hWinOk.tdlen, e4, hWinOk.tdinv, hW2.tblen, hW2.stl, hW2.topl, hW2.stmax, hW2.stok,
        hW2.ssum_max, ?_⟩, ?_⟩
      · exact oinv_of_tinv (Or.inl (by omega)) (Or.inl (by omega)) hliP hljP hW2.tinv
      · have hlt := hW2.ssum_lt
        simp only at hssum
        rcases hlt with hlt | hlt
        · exfalso
          have := hlt.1
          rw [hsiC] at this
          omega
        · rw [hssum]
          rw [hsiC, hsjC] at hlt
          omega
    · rw [if_neg hz]
      simp only [WP.spec_ok]
      have h0 : top1.val = 0 := by have : ¬ 0 < top1.val := hz; omega
      have := hs.oinv
      rw [h0, stk_zero] at this
      exact ⟨hs.tblen, oinv_final this⟩
  · exact hS

end difffold_lines_extract
