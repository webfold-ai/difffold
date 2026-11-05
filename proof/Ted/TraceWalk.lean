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

/-- Everything fixed during a walk. -/
structure WCtx (a b : ted.PostTree) (T i j Sb : Nat) (td fd : alloc.vec.Vec Std.U32) : Prop where
  tt : TT a b T
  win : WinOk a b T i j td fd
  hSb : Sb + (Cw a b T i j).si + (Cw a b T i j).sj ≤ a.label.length + b.label.length

namespace WCtx
variable {a b : ted.PostTree} {T i j Sb : Nat} {td fd : alloc.vec.Vec Std.U32}

theorem good (W : WCtx a b T i j Sb td fd) : (Cw a b T i j).Good :=
  Ctx.win_good (mkCtx a b T) W.tt.hA.wfl W.tt.hB.wfl W.win.hi.1 W.win.hi.2 W.win.hj.1 W.win.hj.2

theorem li1 (W : WCtx a b T i j Sb td fd) : 1 ≤ laOf a i := (W.tt.hA.wfl.1 i W.win.hi.1).1
theorem lj1 (W : WCtx a b T i j Sb td fd) : 1 ≤ laOf b j := (W.tt.hB.wfl.1 j W.win.hj.1).1
theorem li_le (W : WCtx a b T i j Sb td fd) : laOf a i ≤ i := (W.tt.hA.wfl.1 i W.win.hi.1).2
theorem lj_le (W : WCtx a b T i j Sb td fd) : laOf b j ≤ j := (W.tt.hB.wfl.1 j W.win.hj.1).2

end WCtx

theorem Dw_pred_p {la lb : Nat → Nat} {ren : Nat → Nat → Nat} {li lj p q : Nat} (hp : 1 ≤ p) :
    Dw la lb ren li lj (p - 1) q = D la lb ren li (li + p - 1 - 1) lj (lj + q - 1) := by
  unfold Dw
  have e : li + (p - 1) - 1 = li + p - 1 - 1 := by omega
  rw [e]

theorem Dw_pred_q {la lb : Nat → Nat} {ren : Nat → Nat → Nat} {li lj p q : Nat} (hq : 1 ≤ q) :
    Dw la lb ren li lj p (q - 1) = D la lb ren li (li + p - 1) lj (lj + q - 1 - 1) := by
  unfold Dw
  have e : lj + (q - 1) - 1 = lj + q - 1 - 1 := by omega
  rw [e]

theorem Dw_pred_pq {la lb : Nat → Nat} {ren : Nat → Nat → Nat} {li lj p q : Nat} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Dw la lb ren li lj (p - 1) (q - 1) = D la lb ren li (li + p - 1 - 1) lj (lj + q - 1 - 1) := by
  unfold Dw
  have e : li + (p - 1) - 1 = li + p - 1 - 1 := by omega
  have e' : lj + (q - 1) - 1 = lj + q - 1 - 1 := by omega
  rw [e, e']

/-- One step of the walk that deletes or inserts a node. -/
theorem trans_del {a b : ted.PostTree} {T i j Sb : Nat} {td fd : alloc.vec.Vec Std.U32}
    (W : WCtx a b T i j Sb td fd) {to_b stack_i stack_j : alloc.vec.Vec Std.Usize} {top p q : Nat}
    (hW : WInv a b T i j Sb to_b stack_i stack_j top p q) (hp : 1 ≤ p)
    (hD : Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p q =
      Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) (p - 1) q + 1) :
    WInv a b T i j Sb to_b stack_i stack_j top (p - 1) q := by
  have hli := W.li1
  refine ⟨hW.tblen, hW.stl, hW.topl, hW.stmax, ⟨by have := hW.pq.1; omega, hW.pq.2⟩, ?_, ?_, hW.stok, ?_, ?_, hW.ssum_max⟩
  · have := hW.budget; omega
  · rw [Dw_pred_p hp] at hD
    have h := tinv_del (n := a.label.length) (m := b.label.length) (by omega : ¬ (laOf a i + p - 1 < laOf a i ∨ laOf a i + p - 1 = 0)) hD hW.tinv
    have e : laOf a i + p - 1 - 1 = laOf a i + (p - 1) - 1 := by omega
    rw [e] at h; exact h
  · have := hW.ssum_le; omega
  · have := hW.ssum_le; omega

theorem trans_ins {a b : ted.PostTree} {T i j Sb : Nat} {td fd : alloc.vec.Vec Std.U32}
    (W : WCtx a b T i j Sb td fd) {to_b stack_i stack_j : alloc.vec.Vec Std.Usize} {top p q : Nat}
    (hW : WInv a b T i j Sb to_b stack_i stack_j top p q) (hq : 1 ≤ q)
    (hD : Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p q =
      Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p (q - 1) + 1) :
    WInv a b T i j Sb to_b stack_i stack_j top p (q - 1) := by
  have hlj := W.lj1
  refine ⟨hW.tblen, hW.stl, hW.topl, hW.stmax, ⟨hW.pq.1, by have := hW.pq.2; omega⟩, ?_, ?_, hW.stok, ?_, ?_, hW.ssum_max⟩
  · have := hW.budget; omega
  · rw [Dw_pred_q hq] at hD
    have h := tinv_ins (n := a.label.length) (m := b.label.length) (by omega : ¬ (laOf b j + q - 1 < laOf b j ∨ laOf b j + q - 1 = 0)) hD hW.tinv
    have e : laOf b j + q - 1 - 1 = laOf b j + (q - 1) - 1 := by omega
    rw [e] at h; exact h
  · have := hW.ssum_le; omega
  · have := hW.ssum_le; omega

/-- The node matched by a leaf step is not recorded yet. -/
theorem leaf_unmapped {a b : ted.PostTree} {T i j Sb : Nat} {td fd : alloc.vec.Vec Std.U32}
    (W : WCtx a b T i j Sb td fd) {to_b stack_i stack_j : alloc.vec.Vec Std.Usize} {top p q : Nat}
    (hW : WInv a b T i j Sb to_b stack_i stack_j top p q) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hlx : laOf a (laOf a i + p - 1) = laOf a i) (hly : laOf b (laOf b j + q - 1) = laOf b j)
    (hD : Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p q =
      Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) (p - 1) (q - 1) +
        rcost a b (laOf a i + p - 1) (laOf b j + q - 1)) :
    (to_b.val[laOf a i + p - 1]!).val = 0 := by
  have hG := W.good
  have hli := W.li1
  have hlj := W.lj1
  have hA := W.tt.hA.wfl
  have hB := W.tt.hB.wfl
  have hps := hW.pq.1
  have hqs := hW.pq.2
  have hsi : (Cw a b T i j).si = i - laOf a i + 1 := rfl
  have hsj : (Cw a b T i j).sj = j - laOf b j + 1 := rfl
  have hile := W.li_le
  have hjle := W.lj_le
  have hxn : laOf a i + p - 1 ≤ a.label.length := by have := W.win.hi.2; omega
  have hym : laOf b j + q - 1 ≤ b.label.length := by have := W.win.hj.2; omega
  refine Classical.byContradiction fun hne => ?_
  have hmem : (laOf a i + p - 1, (to_b.val[laOf a i + p - 1]!).val) ∈ Pto a.label.length to_b.val :=
    mem_Pto.mpr ⟨by omega, hxn, rfl, hne⟩
  -- complete the walk below the leaf pair and the stack, and read off that `x` would be matched twice
  have hxi : laOf a i + p - 1 ≤ (Cw a b T i j).i0 := by show laOf a i + p - 1 ≤ i; omega
  have hyj : laOf b j + q - 1 ≤ (Cw a b T i j).j0 := by show laOf b j + q - 1 ≤ j; omega
  have hcA : Closed (laOf a) (laOf a i) (laOf a i + p - 1 - 1) := fun u h1 h2 =>
    Ctx.closed_win (Cw a b T i j) hG (x := laOf a i + p - 1 - 1) (by show _ ≤ i; omega) u h1 h2
  have hcB : Closed (laOf b) (laOf b j) (laOf b j + q - 1 - 1) := fun u h1 h2 =>
    Ctx.closed_winB (Cw a b T i j) hG (y := laOf b j + q - 1 - 1) (by show _ ≤ j; omega) u h1 h2
  obtain ⟨Mc, hvc, hrc, hcc⟩ := exists_map (ren := rcost a b) hA hB _ (laOf a i) (laOf a i + p - 1 - 1)
    (laOf b j) (laOf b j + q - 1 - 1) hli hlj hcA hcB rfl
  obtain ⟨MS, hMS⟩ := solsOf_exists (la := laOf a) (lb := laOf b) (ren := rcost a b) hA hB (n := a.label.length)
    (m := b.label.length) (stk stack_i.val stack_j.val top) (fun w hw => by
      have := hW.stok w hw; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩)
  rw [Dw_pred_pq hp hq] at hD
  have hsol := sol_leaf (ren := rcost a b) hA hB (l := laOf a i) (x := laOf a i + p - 1) (l' := laOf b j)
    (y := laOf b j + q - 1) (M := Mc) hli hlj (by omega) (by omega) hlx hly hD ⟨hvc, hrc, hcc⟩
  have hroot := hW.tinv MS _ hMS hsol
  obtain ⟨hv, _, _⟩ := hroot
  have hnd := hv.1
  rw [List.nodup_append] at hnd
  obtain ⟨_, _, hdis⟩ := hnd
  have hinP : (laOf a i + p - 1, (to_b.val[laOf a i + p - 1]!).val) ∈ Pto a.label.length to_b.val ++ MS :=
    List.mem_append_left _ hmem
  have hp0 : (laOf a i + p - 1, (to_b.val[laOf a i + p - 1]!).val) ∈
      Pto a.label.length to_b.val ++ MS ++ ((laOf a i + p - 1, laOf b j + q - 1) :: Mc) :=
    List.mem_append_left _ hinP
  have hq0 : (laOf a i + p - 1, laOf b j + q - 1) ∈
      Pto a.label.length to_b.val ++ MS ++ ((laOf a i + p - 1, laOf b j + q - 1) :: Mc) :=
    List.mem_append_right _ (List.mem_cons_self ..)
  have hpair := (hv.2 _ hp0 _ hq0).1
  have heq : (to_b.val[laOf a i + p - 1]!).val = laOf b j + q - 1 := hpair.mp rfl
  have hsame : (laOf a i + p - 1, (to_b.val[laOf a i + p - 1]!).val) = (laOf a i + p - 1, laOf b j + q - 1) := by
    rw [heq]
  exact hdis _ hinP _ (List.mem_cons_self ..) hsame

theorem trans_leaf {a b : ted.PostTree} {T i j Sb : Nat} {td fd : alloc.vec.Vec Std.U32}
    (W : WCtx a b T i j Sb td fd) {to_b stack_i stack_j : alloc.vec.Vec Std.Usize} {top p q : Nat}
    (hW : WInv a b T i j Sb to_b stack_i stack_j top p q) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hlx : laOf a (laOf a i + p - 1) = laOf a i) (hly : laOf b (laOf b j + q - 1) = laOf b j)
    (hD : Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p q =
      Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) (p - 1) (q - 1) +
        rcost a b (laOf a i + p - 1) (laOf b j + q - 1))
    {to_b' : alloc.vec.Vec Std.Usize} (yU : Std.Usize) (hyU : yU.val = laOf b j + q - 1)
    (hto : to_b'.val = to_b.val.set (laOf a i + p - 1) yU) :
    WInv a b T i j Sb to_b' stack_i stack_j top (p - 1) (q - 1) := by
  have hli := W.li1
  have hlj := W.lj1
  have hA := W.tt.hA.wfl
  have hB := W.tt.hB.wfl
  have hps := hW.pq.1
  have hqs := hW.pq.2
  have hsi : (Cw a b T i j).si = i - laOf a i + 1 := rfl
  have hsj : (Cw a b T i j).sj = j - laOf b j + 1 := rfl
  have hile := W.li_le
  have hjle := W.lj_le
  have hxn : laOf a i + p - 1 ≤ a.label.length := by have := W.win.hi.2; omega
  have hun := leaf_unmapped W hW hp hq hlx hly hD
  have hlenb : to_b.val.length = a.label.length + 1 := hW.tblen
  have hxl : laOf a i + p - 1 < to_b.val.length := by omega
  have hperm := Pto_set (n := a.label.length) (tb := to_b.val) (x := laOf a i + p - 1) (by omega) hxn hxl hun yU
    (by omega)
  rw [← hto] at hperm
  refine ⟨?_, hW.stl, hW.topl, hW.stmax, ⟨by omega, by omega⟩, ?_, ?_, hW.stok, ?_, ?_, hW.ssum_max⟩
  · show to_b'.val.length = a.label.length + 1
    rw [hto, List.length_set]; exact hlenb
  · have := hW.budget
    have h2 := Dw_le_leaf (la := laOf a) (lb := laOf b) (ren := rcost a b) hli hlj hp hq hlx hly
    omega
  · rw [Dw_pred_pq hp hq] at hD
    have h := tinv_leaf (ren := rcost a b) hA hB hli hlj (x := laOf a i + p - 1) (y := laOf b j + q - 1)
      (by omega) (by omega) hlx hly hD hW.tinv
    have e1 : laOf a i + p - 1 - 1 = laOf a i + (p - 1) - 1 := by omega
    have e2 : laOf b j + q - 1 - 1 = laOf b j + (q - 1) - 1 := by omega
    rw [e1, e2] at h
    rw [hyU] at hperm
    exact tinv_perm hperm.symm h
  · have := hW.ssum_le; omega
  · have := hW.ssum_le; omega

theorem trans_push {a b : ted.PostTree} {T i j Sb : Nat} {td fd : alloc.vec.Vec Std.U32}
    (W : WCtx a b T i j Sb td fd) {to_b stack_i stack_j stack_i' stack_j' : alloc.vec.Vec Std.Usize}
    {top p q : Nat} (hW : WInv a b T i j Sb to_b stack_i stack_j top p q) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hnl : ¬ (laOf a (laOf a i + p - 1) = laOf a i ∧ laOf b (laOf b j + q - 1) = laOf b j))
    (hD : Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p q =
      Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) (laOf a (laOf a i + p - 1) - laOf a i)
        (laOf b (laOf b j + q - 1) - laOf b j) + TD (laOf a) (laOf b) (rcost a b) (laOf a i + p - 1) (laOf b j + q - 1))
    (hpush : stack_i'.length = stack_j'.length ∧ top + 1 ≤ stack_i'.length ∧
      (∀ k < top, stack_i'.val[k]! = stack_i.val[k]! ∧ stack_j'.val[k]! = stack_j.val[k]!) ∧
      (stack_i'.val[top]!).val = laOf a i + p - 1 ∧ (stack_j'.val[top]!).val = laOf b j + q - 1 ∧
      (stack_i.length ≤ stack_i'.length ∧ stack_i'.length ≤ stack_i.length + 1) ∧
      (stack_i.length < stack_i'.length → top = stack_i.length)) :
    WInv a b T i j Sb to_b stack_i' stack_j' (top + 1) (laOf a (laOf a i + p - 1) - laOf a i)
      (laOf b (laOf b j + q - 1) - laOf b j) := by
  obtain ⟨hl1, hl2, hl3, hl4, hl5, ⟨hl6, hl7⟩, hl8⟩ := hpush
  have hli := W.li1
  have hlj := W.lj1
  have hA := W.tt.hA.wfl
  have hB := W.tt.hB.wfl
  have hG := W.good
  have hps := hW.pq.1
  have hqs := hW.pq.2
  have hsi : (Cw a b T i j).si = i - laOf a i + 1 := rfl
  have hsj : (Cw a b T i j).sj = j - laOf b j + 1 := rfl
  have hile := W.li_le
  have hjle := W.lj_le
  have hi := W.win.hi
  have hj := W.win.hj
  have hxn : laOf a i + p - 1 ≤ a.label.length := by omega
  have hym : laOf b j + q - 1 ≤ b.label.length := by omega
  have hxi : laOf a i + p - 1 ≤ (Cw a b T i j).i0 := by show laOf a i + p - 1 ≤ i; omega
  have hyj : laOf b j + q - 1 ≤ (Cw a b T i j).j0 := by show laOf b j + q - 1 ≤ j; omega
  have hcA : Closed (laOf a) (laOf a i) (laOf a i + p - 1) := Ctx.closed_win (Cw a b T i j) hG hxi
  have hcB : Closed (laOf b) (laOf b j) (laOf b j + q - 1) := Ctx.closed_winB (Cw a b T i j) hG hyj
  have hlx1 : laOf a i ≤ laOf a (laOf a i + p - 1) := hcA (laOf a i + p - 1) (by omega) (Nat.le_refl _)
  have hly1 : laOf b j ≤ laOf b (laOf b j + q - 1) := hcB (laOf b j + q - 1) (by omega) (Nat.le_refl _)
  have hlx2 := (hA.1 (laOf a i + p - 1) (by omega)).2
  have hly2 := (hB.1 (laOf b j + q - 1) (by omega)).2
  have hstk : stk stack_i'.val stack_j'.val (top + 1) = stk stack_i.val stack_j.val top ++
      [(laOf a i + p - 1, laOf b j + q - 1)] := stk_push hl3 hl4 hl5
  have hbc := Ctx.budget_child (Cw a b T i j) hG (p := p) (q := q) hli hlj hp hq hps hqs hW.budget hD
  have hss := ssum_append (laOf a) (laOf b) (stk stack_i.val stack_j.val top) (laOf a i + p - 1, laOf b j + q - 1)
  have hnotbase : ¬ (p = (Cw a b T i j).si ∧ q = (Cw a b T i j).sj) := by
    rintro ⟨e1, e2⟩
    apply hnl
    constructor
    · have : laOf a i + p - 1 = i := by omega
      rw [this]
    · have : laOf b j + q - 1 = j := by omega
      rw [this]
  have hsd : ssum (laOf a) (laOf b) (stk stack_i'.val stack_j'.val (top + 1)) + (laOf a (laOf a i + p - 1) - laOf a i) +
      (laOf b (laOf b j + q - 1) - laOf b j) = ssum (laOf a) (laOf b) (stk stack_i.val stack_j.val top) + p + q := by
    rw [hstk, hss]
    simp only
    omega
  have hmax : ssum (laOf a) (laOf b) (stk stack_i'.val stack_j'.val (top + 1)) ≤ a.label.length + b.label.length := by
    have := W.hSb
    have := hW.ssum_le
    omega
  have hlen_stk : (stk stack_i'.val stack_j'.val (top + 1)).length = top + 1 := by
    unfold stk; simp
  have hge := ssum_ge (laOf a) (laOf b) (stk stack_i'.val stack_j'.val (top + 1))
  refine ⟨hW.tblen, hl1, hl2, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, hmax⟩
  · by_cases hg : stack_i.length < stack_i'.length
    · have := hl8 hg
      omega
    · have := hW.stmax; omega
  · omega
  · omega
  · have h := hW.budget
    omega
  · have hd : D (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf a i + p - 1) (laOf b j) (laOf b j + q - 1) =
        D (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf a (laOf a i + p - 1) - 1) (laOf b j)
          (laOf b (laOf b j + q - 1) - 1) +
        D (laOf a) (laOf b) (rcost a b) (laOf a (laOf a i + p - 1)) (laOf a i + p - 1)
          (laOf b (laOf b j + q - 1)) (laOf b j + q - 1) := by
      have e1 : laOf a i + (laOf a (laOf a i + p - 1) - laOf a i) - 1 = laOf a (laOf a i + p - 1) - 1 := by omega
      have e2 : laOf b j + (laOf b (laOf b j + q - 1) - laOf b j) - 1 = laOf b (laOf b j + q - 1) - 1 := by omega
      unfold Dw TD at hD
      rw [e1, e2] at hD
      exact hD
    have h := tinv_push (ren := rcost a b) hA hB hli hlj (x := laOf a i + p - 1) (y := laOf b j + q - 1)
      (l := laOf a i) (l' := laOf b j) (by omega) (by omega) hcA hcB hd hW.tinv
    rw [hstk]
    have e1 : laOf a (laOf a i + p - 1) - 1 = laOf a i + (laOf a (laOf a i + p - 1) - laOf a i) - 1 := by omega
    have e2 : laOf b (laOf b j + q - 1) - 1 = laOf b j + (laOf b (laOf b j + q - 1) - laOf b j) - 1 := by omega
    rw [e1, e2] at h
    exact h
  · rw [hstk]
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hW.stok w hw
    · rw [List.mem_singleton] at hw
      subst hw
      exact ⟨by omega, hxn, by omega, hym, hbc⟩
  · have := hW.ssum_le
    omega
  · right
    have h1 := hW.ssum_le
    have h2 := hW.ssum_lt
    rcases h2 with h2 | h2
    · exact absurd h2 hnotbase
    · omega

theorem lt_push_aux (p q lx li ly lj x y : Nat) (h1 : lx ≤ x) (h2 : ly ≤ y) (h3 : x = li + p - 1)
    (h4 : y = lj + q - 1) (hp : 1 ≤ p) (hq : 1 ≤ q) : (lx - li) + (ly - lj) < p + q := by omega

theorem lt_leaf_aux (p q : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) : (p - 1) + (q - 1) < p + q := by omega

theorem lt_del_aux (p q : Nat) (hp : 1 ≤ p) : (p - 1) + q < p + q := by omega

theorem lt_ins_aux (p q : Nat) (hq : 1 ≤ q) : p + (q - 1) < p + q := by omega

theorem bool_go_true (p d de i : Bool) (h : true = (p && d || !de && !i)) :
    (p = true ∧ d = true) ∨ (de = false ∧ i = false) := by
  cases p <;> cases d <;> cases de <;> cases i <;> simp at h ⊢

theorem bool_go_false (p d de i : Bool) (h : false = (p && d || !de && !i)) (hd : de = false) : i = true := by
  cases p <;> cases d <;> cases de <;> cases i <;> simp at h hd ⊢

set_option maxHeartbeats 1600000 in
/-- The inner loop of the traceback: one walk through a window table. -/
theorem walk_spec (a b : ted.PostTree) (prefer_match : Bool) {T i j Sb : Nat} {td fd : alloc.vec.Vec Std.U32}
    (W : WCtx a b T i j Sb td fd) (t w : Std.Usize) (inf : Std.U32) (li lj : Std.Usize)
    (ht : t.val = T) (hw : w.val = 2 * T + 1) (hinf : inf.val = T + 1)
    (hli : li.val = laOf a i) (hlj : lj.val = laOf b j)
    (to_b stack_i stack_j : alloc.vec.Vec Std.Usize) (top p q : Std.Usize)
    (hW : WInv a b T i j Sb to_b stack_i stack_j top.val p.val q.val) :
    ted.traceback_loop0_loop0 a.label a.lml a.keyroots a.kids a.kind b.label b.lml b.keyroots b.kids b.kind
      prefer_match td t inf w to_b stack_i stack_j top li lj fd p q ⦃ r =>
      WInv a b T i j Sb r.1 r.2.1 r.2.2.1 r.2.2.2.val 0 0 ⦄ := by
  unfold ted.traceback_loop0_loop0
  have hUM : 2 ^ 32 ≤ Std.Usize.max + 1 := by scalar_tac
  have hA := W.tt.hA
  have hB := W.tt.hB
  have hG := W.good
  have hli1 := W.li1
  have hlj1 := W.lj1
  have hile := W.li_le
  have hjle := W.lj_le
  have hi := W.win.hi
  have hj := W.win.hj
  have hna := W.tt.hna
  have hnb := W.tt.hnb
  have hTn := W.tt.hT
  have hcA : Closed (laOf a) (laOf a i) i := Ctx.closed_win (Cw a b T i j) hG (x := i) (Nat.le_refl _)
  have hcB : Closed (laOf b) (laOf b j) j := Ctx.closed_winB (Cw a b T i j) hG (y := j) (Nat.le_refl _)
  have hF : ∀ p q, p ≤ (Cw a b T i j).si → q ≤ (Cw a b T i j).sj → (Cw a b T i j).OkF fd.val p q :=
    fun p q hp hq => W.win.rows p q hp hq (Or.inl (by omega))
  apply loop.spec_decr_nat
    (measure := fun s => s.2.2.2.2.1.val + s.2.2.2.2.2.val)
    (inv := fun s => WInv a b T i j Sb s.1 s.2.1 s.2.2.1 s.2.2.2.1.val s.2.2.2.2.1.val s.2.2.2.2.2.val)
  · intro s hs
    obtain ⟨to_b1, stack_i1, stack_j1, top1, p1, q1⟩ := s
    dsimp only at hs ⊢
    unfold ted.traceback_loop0_loop0.body
    have hps := hs.pq.1
    have hqs := hs.pq.2
    have hsi : (Cw a b T i j).si = i - laOf a i + 1 := rfl
    have hsj : (Cw a b T i j).sj = j - laOf b j + 1 := rfl
    have hp1n : p1.val ≤ a.label.length := by omega
    have hq1m : q1.val ≤ b.label.length := by omega
    step as ⟨ipq, hipq⟩
    by_cases hpos : ipq > 0#usize
    · rw [if_pos hpos]
      have hipq_pos : 0 < p1.val + q1.val := by have : 0 < ipq.val := hpos; omega
      have hbigw : ∀ k, k ≤ a.label.length → (k + 1) * w.val < 2 ^ 32 := by
        intro k hk
        have h1 : (k + 1) * w.val ≤ 2 ^ 14 * 2 ^ 16 := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hfdlen : ((Cw a b T i j).si + 1) * (2 * T + 1) ≤ fd.length := W.win.fdlen
      have hlenp : (p1.val + 1) * w.val ≤ fd.val.length := by
        rw [hw]
        exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hfdlen
      have hsF : ∀ v : alloc.vec.Vec Std.U32, (alloc.vec.Vec.deref v).val = v.val := fun v => by simp [alloc.vec.Vec.deref]
      step with get_spec (alloc.vec.Vec.deref fd) w t inf p1 q1 (by omega) (by rw [hsF]; exact hlenp) (hbigw _ hp1n) as ⟨v10, hv10⟩
      have hlig : 1 ≤ li.val := by omega
      have hljg : 1 ≤ lj.val := by omega
      have hlin : li.val ≤ a.label.length := by omega
      have hljn : lj.val ≤ b.label.length := by omega
      step as ⟨i1, hi1⟩
      have hi1b : i1.val ≤ a.label.length + 1 := by rw [hi1]; omega
      step as ⟨i2, hi2⟩
      have hi2g : 1 ≤ i2.val := by omega
      step as ⟨x, hx⟩
      step as ⟨i3, hi3⟩
      have hi3b : i3.val ≤ b.label.length + 1 := by rw [hi3]; omega
      step as ⟨i4, hi4⟩
      have hi4g : 1 ≤ i4.val := by omega
      step as ⟨y, hy⟩
      have hlml : a.lml.length = a.label.length := hA.n2
      have hlmlb : b.lml.length = b.label.length := hB.n2
      have hxv : x.val = laOf a i + max p1.val 1 - 1 := by omega
      have hyv : y.val = laOf b j + max q1.val 1 - 1 := by omega
      have hx1 : 1 ≤ x.val := by omega
      have hy1 : 1 ≤ y.val := by omega
      have hxi : x.val ≤ i := by omega
      have hyj : y.val ≤ j := by omega
      have hxl : laOf a i ≤ x.val := by omega
      have hyl : laOf b j ≤ y.val := by omega
      have hxn : x.val ≤ a.label.length := by omega
      have hym : y.val ≤ b.label.length := by omega
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨lx, hlx⟩
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8⟩
      step as ⟨ly, hly⟩
      have hxeq : 1 ≤ p1.val → x.val = laOf a i + p1.val - 1 := by intro hp; omega
      have hyeq : 1 ≤ q1.val → y.val = laOf b j + q1.val - 1 := by intro hq; omega
      have hlml' : a.lml.val.length = a.label.length := hA.n2
      have hlmlb' : b.lml.val.length = b.label.length := hB.n2
      have hlxv : lx.val = laOf a x.val := by
        rw [laOf_eq1 a _ hx1 hxn, hlx, U32.cast_Usize_val_eq, hi6, getG_eq _ _ (by omega)]
        simp only [hi5]
      have hlyv : ly.val = laOf b y.val := by
        rw [laOf_eq1 b _ hy1 hym, hly, U32.cast_Usize_val_eq, hi8, getG_eq _ _ (by omega)]
        simp only [hi7]
      have hlx1 : laOf a i ≤ lx.val := by rw [hlxv]; exact hcA x.val hxl hxi
      have hly1 : laOf b j ≤ ly.val := by rw [hlyv]; exact hcB y.val hyl hyj
      have hlx2 : lx.val ≤ x.val := by rw [hlxv]; exact (hA.wfl.1 x.val hx1).2
      have hly2 : ly.val ≤ y.val := by rw [hlyv]; exact (hB.wfl.1 y.val hy1).2
      have hlxp : lx.val - li.val ≤ p1.val := by omega
      have hlyq : ly.val - lj.val ≤ q1.val := by omega
      have hrd : ∀ (L : List Std.U32) x y, rd L w.val t.val inf.val x y =
          rd L (Cw a b T i j).w (Cw a b T i j).t (Cw a b T i j).inf x y := by
        intro L x y; rw [hw, ht, hinf]; rfl
      have hwt : w.val = 2 * t.val + 1 := by rw [hw, ht]
      have hinfb : 2 * inf.val + 2 < 2 ^ 32 := by omega
      have hlen2 : (lx.val - li.val + 1) * w.val ≤ (alloc.vec.Vec.deref fd).val.length := by
        rw [hsF]; exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlenp
      have hlent : (x.val + 1) * w.val ≤ (alloc.vec.Vec.deref td).val.length := by
        rw [hsF, hw]
        exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) W.win.tdlen
      have hFB : Ctx.FdB (alloc.vec.Vec.deref fd).val inf.val := by rw [hsF, hinf]; exact W.win.fdB
      have hTB : Ctx.FdB (alloc.vec.Vec.deref td).val inf.val := by rw [hsF, hinf]; exact W.win.tdB
      have hlenp' : (p1.val + 1) * w.val ≤ (alloc.vec.Vec.deref fd).val.length := by rw [hsF]; exact hlenp
      step with is_leaf_case_spec p1 q1 lx ly li lj as ⟨leaf_case, hleaf⟩
      step with diag_test_spec a b (alloc.vec.Vec.deref fd) (alloc.vec.Vec.deref td) w t inf li lj p1 q1 x y lx ly
        leaf_case v10 hwt hinfb hlenp' (hbigw _ hp1n) hlen2 (hbigw _ (by omega)) hlent (hbigw _ hxn) hFB hTB
        ⟨hx1, hxn⟩ ⟨hy1, hym⟩ hA.n3 hB.n3 (by omega) (by omega) as ⟨diag_ok, hdiag⟩
      step with del_test_spec (alloc.vec.Vec.deref fd) w t inf p1 q1 v10 hwt hlenp' (hbigw _ hp1n) (by omega) hFB
        as ⟨del_ok, hdel⟩
      step with ins_test_spec (alloc.vec.Vec.deref fd) w t inf p1 q1 v10 hwt hlenp' (hbigw _ hp1n) (by omega) hFB
        as ⟨ins_ok, hins⟩
      step with choose_diag_spec prefer_match diag_ok del_ok ins_ok as ⟨go_diag, hgo⟩
      have hv : v10.val = rd fd.val (Cw a b T i j).w (Cw a b T i j).t (Cw a b T i j).inf p1.val q1.val := by
        rw [hv10, hsF, hrd]
      simp only [hsF, hrd] at hdiag hdel hins
      by_cases hg : go_diag = true
      · rw [if_pos hg]
        have hall : 1 ≤ p1.val ∧ 1 ≤ q1.val ∧
            ((laOf a (laOf a i + p1.val - 1) = laOf a i ∧ laOf b (laOf b j + q1.val - 1) = laOf b j) →
              Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p1.val q1.val =
                Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) (p1.val - 1) (q1.val - 1) +
                  rcost a b (laOf a i + p1.val - 1) (laOf b j + q1.val - 1)) ∧
            (¬ (laOf a (laOf a i + p1.val - 1) = laOf a i ∧ laOf b (laOf b j + q1.val - 1) = laOf b j) →
              Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) p1.val q1.val =
                Dw (laOf a) (laOf b) (rcost a b) (laOf a i) (laOf b j) (laOf a (laOf a i + p1.val - 1) - laOf a i)
                  (laOf b (laOf b j + q1.val - 1) - laOf b j) +
                TD (laOf a) (laOf b) (rcost a b) (laOf a i + p1.val - 1) (laOf b j + q1.val - 1)) := by
          have hgd : (prefer_match = true ∧ diag_ok = true) ∨ (del_ok = false ∧ ins_ok = false) := by
            rw [hg] at hgo
            exact bool_go_true _ _ _ _ hgo
          rcases hgd with ⟨_, hdg⟩ | ⟨hd0, hi0⟩
          · obtain ⟨h1, h2, hL, hNL⟩ := hdiag.mp hdg
            have h1' : 1 ≤ p1.val := h1
            have h2' : 1 ≤ q1.val := h2
            refine ⟨h1', h2', fun hlp => ?_, fun hnlp => ?_⟩
            · have hlc : leaf_case = true := hleaf.mpr ⟨h1, h2, by rw [hlxv, hxeq h1', hlp.1, hli],
                by rw [hlyv, hyeq h2', hlp.2, hlj]⟩
              have hLc := (hL hlc).2
              rw [hxeq h1', hyeq h2', hv] at hLc
              exact (Cw a b T i j).leaf_sound hli1 hlj1 h1' h2' hs.pq.1 hs.pq.2 hlp.1 hlp.2 hF hs.budget rfl hLc
            · have hlc : leaf_case = false := by
                cases hlc' : leaf_case
                · rfl
                · exfalso
                  obtain ⟨_, _, e3, e4⟩ := hleaf.mp hlc'
                  apply hnlp
                  exact ⟨by rw [← hxeq h1', ← hlxv, e3, hli], by rw [← hyeq h2', ← hlyv, e4, hlj]⟩
              have hNc := hNL hlc
              rw [hxeq h1', hyeq h2', hv] at hNc
              have hT := (W.win.tdinv x.val y.val hx1 hxn hy1 hym).1
              rw [hxeq h1', hyeq h2'] at hT
              rw [hlxv, hlyv, hxeq h1', hyeq h2', hli, hlj] at hNc
              exact (Cw a b T i j).nonleaf_sound hG hli1 hlj1 h1' h2' hs.pq.1 hs.pq.2 hnlp hF hs.budget hT hNc
          · have hnd : ¬ (1 ≤ p1.val ∧ rd fd.val (Cw a b T i j).w (Cw a b T i j).t (Cw a b T i j).inf
                (p1.val - 1) q1.val + 1 =
                rd fd.val (Cw a b T i j).w (Cw a b T i j).t (Cw a b T i j).inf p1.val q1.val) := by
              intro h
              have := hdel.mpr ⟨h.1, by rw [hv]; exact h.2⟩
              rw [hd0] at this
              exact absurd this (by simp)
            have hni : ¬ (1 ≤ q1.val ∧ rd fd.val (Cw a b T i j).w (Cw a b T i j).t (Cw a b T i j).inf
                p1.val (q1.val - 1) + 1 =
                rd fd.val (Cw a b T i j).w (Cw a b T i j).t (Cw a b T i j).inf p1.val q1.val) := by
              intro h
              have := hins.mpr ⟨h.1, by rw [hv]; exact h.2⟩
              rw [hi0] at this
              exact absurd this (by simp)
            exact (Cw a b T i j).fallback hG hli1 hlj1 hipq_pos hs.pq.1 hs.pq.2 hF hs.budget hnd hni
        obtain ⟨hp1, hq1, hLf, hNLf⟩ := hall
        by_cases hl : leaf_case = true
        · rw [if_pos hl]
          have hlp : laOf a (laOf a i + p1.val - 1) = laOf a i ∧ laOf b (laOf b j + q1.val - 1) = laOf b j := by
            obtain ⟨_, _, e3, e4⟩ := hleaf.mp hl
            exact ⟨(by rw [← hxeq hp1, ← hlxv, e3, hli]), (by rw [← hyeq hq1, ← hlyv, e4, hlj])⟩
          have hxt : x.val < to_b1.length := by have := hs.tblen; omega
          step as ⟨old, imb, ho, himb⟩
          step as ⟨p', hp'⟩
          step as ⟨q', hq'⟩
          have hto : (imb y).val = to_b1.val.set (laOf a i + p1.val - 1) y := by
            rw [himb, alloc.vec.Vec.set_val_eq, hxeq hp1]
          refine ⟨?_, by rw [hp', hq']; exact lt_leaf_aux _ _ hp1 hq1⟩
          have := trans_leaf W hs hp1 hq1 hlp.1 hlp.2 (hLf hlp) y (hyeq hq1) hto
          rw [hp', hq']; exact this
        · rw [if_neg hl]
          have hnl : ¬ (laOf a (laOf a i + p1.val - 1) = laOf a i ∧ laOf b (laOf b j + q1.val - 1) = laOf b j) := by
            intro hlp
            apply hl
            exact hleaf.mpr ⟨hp1, hq1, (by rw [hlxv, hxeq hp1, hlp.1, hli]), (by rw [hlyv, hyeq hq1, hlp.2, hlj])⟩
          have hmx : stack_i1.length + 1 ≤ Std.Usize.max := by have := hs.stmax; omega
          step with push_slot_spec stack_i1 stack_j1 top1 x y hs.stl hs.topl hmx as ⟨si', sj', h1, h2, h3, h4, h5, h6, h7, h8⟩
          have hmx2 : top1.val + 1 ≤ Std.Usize.max := by have := hs.topl; have := hs.stmax; omega
          step as ⟨top', htop'⟩
          step as ⟨p', hp'⟩
          step as ⟨q', hq'⟩
          rw [hxeq hp1] at h4
          rw [hyeq hq1] at h5
          have hW' := trans_push (stack_i' := si') (stack_j' := sj') W hs hp1 hq1 hnl (hNLf hnl)
            ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩
          have e1 : p'.val = laOf a (laOf a i + p1.val - 1) - laOf a i := by rw [hp', hlxv, hxeq hp1, hli]
          have e2 : q'.val = laOf b (laOf b j + q1.val - 1) - laOf b j := by rw [hq', hlyv, hyeq hq1, hlj]
          refine ⟨?_, ?_⟩
          · rw [htop', e1, e2]; exact hW'
          · rw [hp', hq']
            exact lt_push_aux _ _ _ _ _ _ _ _ hlx2 hly2 (by rw [hli]; exact hxeq hp1) (by rw [hlj]; exact hyeq hq1) hp1 hq1
      · rw [if_neg hg]
        have hg' : go_diag = false := by simpa using hg
        rw [hg'] at hgo
        by_cases hd : del_ok = true
        · rw [if_pos hd]
          obtain ⟨h1, h2⟩ := hdel.mp hd
          have h1' : 1 ≤ p1.val := h1
          step as ⟨p', hp'⟩
          have hD := (Cw a b T i j).del_sound hli1 hlj1 h1' hs.pq.1 hs.pq.2 hF hs.budget (by rw [← hv]; exact h2)
          refine ⟨?_, by rw [hp']; exact lt_del_aux _ _ h1'⟩
          have := trans_del W hs h1' hD
          rw [hp']; exact this
        · rw [if_neg hd]
          have hdn : del_ok = false := by simpa using hd
          have hit : ins_ok = true := bool_go_false _ _ _ _ hgo hdn
          obtain ⟨h1, h2⟩ := hins.mp hit
          have h1' : 1 ≤ q1.val := h1
          step as ⟨q', hq'⟩
          have hD := (Cw a b T i j).ins_sound hli1 hlj1 h1' hs.pq.1 hs.pq.2 hF hs.budget (by rw [← hv]; exact h2)
          refine ⟨?_, by rw [hq']; exact lt_ins_aux _ _ h1'⟩
          have := trans_ins W hs h1' hD
          rw [hq']; exact this
    · rw [if_neg hpos]
      simp only [WP.spec_ok]
      have h0 : ipq.val = 0 := by have : ¬ 0 < ipq.val := hpos; omega
      have hp0 : p1.val = 0 := by omega
      have hq0 : q1.val = 0 := by omega
      rw [hp0, hq0] at hs
      exact hs
  · exact hW

end difffold_lines_extract
