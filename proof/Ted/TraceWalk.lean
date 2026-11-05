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

end difffold_lines_extract
