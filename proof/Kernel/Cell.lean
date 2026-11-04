import CellArith
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

/-- Everything the kernel functions assume about their inputs, and the cost oracle's contract.
The pair-cost oracle is abstract: any `O` with a `kernel.Oracle` instance whose `pair_cost` returns
`g.dd` and preserves an invariant `Inv`. -/
structure Ctx (O : Type) (inst : kernel.Oracle O) where
  g : Grid
  sa : Slice Std.U32
  sb : Slice Std.U32
  ra : Slice Std.U32
  rb : Slice Std.U32
  on : Bool
  tau : Std.U32
  Inv : O → Prop
  hn : g.n = sa.val.length
  hm : g.m = sb.val.length
  hgsa : ∀ i, g.sa i = sa.val[i]!.val
  hgsb : ∀ j, g.sb j = sb.val[j]!.val
  hsa : ∀ i < sa.val.length, sa.val[i]!.val ≤ 2 ^ 27
  hsb : ∀ j < sb.val.length, sb.val[j]!.val ≤ 2 ^ 27
  hra : ∀ i < ra.val.length, ra.val[i]!.val ≤ 2 ^ 27
  hrb : ∀ i < rb.val.length, rb.val[i]!.val ≤ 2 ^ 27
  hralen : sa.val.length < ra.val.length
  hrblen : sb.val.length < rb.val.length
  htau : tau.val + 2 ^ 28 < INFn
  hdd : ∀ i j, i < g.n → j < g.m → g.dd i j ≤ 2 ^ 28
  hsize : on = true → ∀ i j, i < g.n → j < g.m →
    g.sa i ≤ g.sb j + g.dd i j ∧ g.sb j ≤ g.sa i + g.dd i j
  pair : ∀ (o : O) (i j : Std.Usize), Inv o → i.val < g.n → j.val < g.m →
    inst.pair_cost o i j ⦃ r => r.1.val = g.dd i.val j.val ∧ Inv r.2 ⦄
  same : ∀ (o : O) (i j : Std.Usize), inst.same o i j ⦃ _ => True ⦄

variable {O : Type} {inst : kernel.Oracle O}

/-- The kernel's bound at a cell. -/
abbrev Ctx.h (C : Ctx O inst) : Nat → Nat → Nat := hK C.ra C.rb C.on

/-- The delete candidate. -/
@[step] theorem del_cand_spec (prev : kernel.Row) (j : Std.Usize) (sa : Slice Std.U32) (i : Std.Usize)
    (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ sa.val.length) (hsa : sa.val[i.val - 1]!.val ≤ 2 ^ 27) :
    kernel.del_cand prev j sa i ⦃ d =>
      d.val = if rowSem prev j.val < INFn then rowSem prev j.val + sa.val[i.val - 1]!.val else INFn ⦄ := by
  unfold kernel.del_cand
  step as ⟨above, habove⟩
  split
  · rename_i hlt
    have hk := kernel_INF_val
    have hlt' : rowSem prev j.val < INFn := by rw [← habove]; scalar_tac
    step as ⟨i1, hi1'⟩
    step as ⟨i2, hi2'⟩
    have hb : i1.val < sa.val.length := by scalar_tac
    have e0 : i2.val = sa.val[i1.val]!.val := by rw [hi2', getElem_bang_eq _ _ hb]
    have hi1v : i1.val = i.val - 1 := by scalar_tac
    rw [hi1v] at e0
    step as ⟨r, hr⟩
    · have hINF : INFn = 1073741823 := rfl
      have h1 : above.val < INFn := by rw [habove]; exact hlt'
      scalar_tac
    · rw [if_pos hlt']
      omega
  · rename_i hge
    have hk := kernel_INF_val
    have hge' : ¬ rowSem prev j.val < INFn := by rw [← habove]; scalar_tac
    rw [WP.spec_ok, if_neg hge', hk]

/-- The insert candidate. -/
@[step] theorem ins_cand_spec (v : alloc.vec.Vec Std.U32) (j plo : Std.Usize) (sb : Slice Std.U32)
    (hplo : plo.val ≤ j.val) (hvlen : v.length = j.val - plo.val) (hjm : j.val ≤ sb.val.length)
    (hv : ∀ t < v.length, v.val[t]!.val ≤ INFn) (hsb : ∀ t < sb.val.length, sb.val[t]!.val ≤ 2 ^ 27) :
    kernel.ins_cand v j plo sb ⦃ x =>
      x.val = if j.val > plo.val then v.val[v.length - 1]!.val + sb.val[j.val - 1]!.val else INFn ⦄ := by
  unfold kernel.ins_cand
  split
  · rename_i hgt
    have hgt' : j.val > plo.val := by scalar_tac
    have hvpos : 0 < v.length := by omega
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    have hb3 : i2.val < v.val.length := by scalar_tac
    have e3 : i3.val = v.val[i2.val]!.val := by rw [hi3, getElem_bang_eq _ _ hb3]
    have hb5 : i4.val < sb.val.length := by scalar_tac
    have e5 : i5.val = sb.val[i4.val]!.val := by rw [hi5, getElem_bang_eq _ _ hb5]
    have h2v : i2.val = v.length - 1 := by scalar_tac
    have h4v : i4.val = j.val - 1 := by scalar_tac
    rw [h2v] at e3; rw [h4v] at e5
    have hvi := hv (v.length - 1) (by omega)
    have hsbi := hsb (j.val - 1) (by omega)
    have hINF : INFn = 1073741823 := rfl
    step as ⟨r, hr⟩
    rw [if_pos hgt']; omega
  · rename_i hle
    have hle' : ¬ j.val > plo.val := by scalar_tac
    have hk := kernel_INF_val
    rw [WP.spec_ok, if_neg hle', hk]

/-- The lower bound on the pair candidate. -/
@[step] theorem lower_bound_spec (on : Bool) (diag sa_i sb_j : Std.U32) (hd : diag.val < INFn)
    (ha : sa_i.val ≤ 2 ^ 27) (hb : sb_j.val ≤ 2 ^ 27) :
    kernel.lower_bound on diag sa_i sb_j ⦃ x =>
      x.val = if on then diag.val + absd sa_i.val sb_j.val else diag.val ⦄ := by
  unfold kernel.lower_bound
  have hINF : INFn = 1073741823 := rfl
  split
  · rename_i hon
    step as ⟨d, hdv⟩
    step as ⟨r, hr⟩
    all_goals first
      | (simp only [absd]; split_ifs at hdv ⊢ <;> omega)
      | (split_ifs at hdv <;> scalar_tac)
  · rename_i hon
    rw [WP.spec_ok]

/-- The diagonal stage. -/
theorem diag_stage_spec (C : Ctx O inst) (o : O) (prev : kernel.Row) (i j : Std.Usize)
    (best0 : Std.U32) (c : kernel.Counters)
    (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ C.g.n) (hj : j.val ≤ C.g.m) (hInv : C.Inv o) :
    kernel.diag_stage inst o prev i j C.sa C.sb C.ra C.rb C.tau C.on best0 c ⦃ r =>
      C.Inv r.2.1 ∧
      r.1.val = diagStage C.on (C.h i.val j.val) C.tau.val (C.g.sa (i.val - 1)) (C.g.sb (j.val - 1))
        (C.g.dd (i.val - 1) (j.val - 1)) best0.val
        (if j.val > 0 then rowSem prev (j.val - 1) else INFn) ⦄ := by
  have hk := kernel_INF_val
  have hINF : INFn = 1073741823 := rfl
  have hira : i.val < C.ra.val.length := by have := C.hn; have := C.hralen; omega
  have hjrb : j.val < C.rb.val.length := by have := C.hm; have := C.hrblen; omega
  unfold kernel.diag_stage
  split
  · rename_i hj0
    have hj0' : j.val > 0 := by scalar_tac
    step as ⟨i1, hi1'⟩
    step as ⟨diag, hdiag⟩
    have hDv : rowSem prev (j.val - 1) = diag.val := by
      rw [hdiag, show i1.val = j.val - 1 by scalar_tac]
    rw [if_pos hj0', hDv]
    split
    · rename_i hdl
      have hdl' : diag.val < INFn := by rw [← hk]; scalar_tac
      have hia : i.val - 1 < C.sa.val.length := by have := C.hn; omega
      have hjb : j.val - 1 < C.sb.val.length := by have := C.hm; omega
      have hsai := C.hsa (i.val - 1) hia
      have hsbj := C.hsb (j.val - 1) hjb
      step as ⟨i2, hi2'⟩
      step as ⟨i3, hi3'⟩
      step as ⟨i4, hi4'⟩
      have hb2 : i2.val < C.sa.val.length := by scalar_tac
      have e3 : i3.val = C.sa.val[i2.val]!.val := by rw [hi3', getElem_bang_eq _ _ hb2]
      have hb4 : i1.val < C.sb.val.length := by scalar_tac
      have e4 : i4.val = C.sb.val[i1.val]!.val := by rw [hi4', getElem_bang_eq _ _ hb4]
      have hi2v : i2.val = i.val - 1 := by scalar_tac
      have hi1v : i1.val = j.val - 1 := by scalar_tac
      rw [hi2v] at e3
      rw [hi1v] at e4
      have hi3b : i3.val ≤ 2 ^ 27 := by rw [e3]; exact hsai
      have hi4b : i4.val ≤ 2 ^ 27 := by rw [e4]; exact hsbj
      step as ⟨lbound, hlb⟩
      have hlbv : lbound.val =
          (if C.on = true then diag.val + absd (C.g.sa (i.val - 1)) (C.g.sb (j.val - 1)) else diag.val) := by
        rw [hlb, e3, e4, C.hgsa, C.hgsb]
      split
      · rename_i hlt
        have hlt' : lbound.val < best0.val := by scalar_tac
        have hbh := hK_le C.ra C.rb C.on i.val j.val C.hra C.hrb hira hjrb
        step as ⟨h5, hh5⟩
        step as ⟨i6, hi6⟩
        · have hINF : INFn = 1073741823 := rfl
          have habs : absd (C.g.sa (i.val - 1)) (C.g.sb (j.val - 1)) ≤ 2 ^ 27 := by
            unfold absd; rw [C.hgsa, C.hgsb]; split_ifs <;> omega
          have hlb_le : lbound.val ≤ diag.val + 2 ^ 27 := by
            rw [hlbv]; split_ifs <;> omega
          have h5b : h5.val ≤ 2 ^ 27 := by rw [hh5]; exact hbh
          scalar_tac
        · have hi6v : i6.val = lbound.val + C.h i.val j.val := by rw [hi6, hh5]
          have hD1 : diag.val < INFn := hdl'
          have hINF : INFn = 1073741823 := rfl
          split
          · rename_i hle
            have hle' : lbound.val + C.h i.val j.val ≤ C.tau.val := by scalar_tac
            have hi2n : i2.val < C.g.n := by scalar_tac
            have hi1m : i1.val < C.g.m := by scalar_tac
            step with C.pair o i2 i1 hInv hi2n hi1m as ⟨i7, o1, hp, hp2⟩
            have hdd7 := C.hdd i2.val i1.val hi2n hi1m
            step as ⟨sub, hsub⟩
            step as ⟨best, hbest⟩
            rw [hi2v, hi1v] at hp
            refine ⟨hp2, ?_⟩
            unfold diagStage
            rw [if_pos hdl']
            simp only []
            rw [← hlbv, if_pos hlt', if_pos hle', hbest, hsub, hp]
          · rename_i hgt
            have hgt' : ¬ (lbound.val + C.h i.val j.val ≤ C.tau.val) := by scalar_tac
            have hi2n : i2.val < C.g.n := by scalar_tac
            step with C.same o i2 i1 as ⟨b⟩
            split
            · refine ⟨hInv, ?_⟩
              unfold diagStage
              rw [if_pos hdl']
              simp only []
              rw [← hlbv, if_pos hlt', if_neg hgt']
            · step as ⟨i7, hi7⟩
              refine ⟨hInv, ?_⟩
              unfold diagStage
              rw [if_pos hdl']
              simp only []
              rw [← hlbv, if_pos hlt', if_neg hgt']
      · rename_i hge
        have hge' : ¬ lbound.val < best0.val := by scalar_tac
        rw [WP.spec_ok]
        refine ⟨hInv, ?_⟩
        unfold diagStage
        rw [if_pos hdl']
        simp only []
        rw [← hlbv, if_neg hge']
    · rename_i hdg
      have hdg' : ¬ diag.val < INFn := by rw [← hk]; scalar_tac
      rw [WP.spec_ok]
      refine ⟨hInv, ?_⟩
      unfold diagStage
      rw [if_neg hdg']
  · rename_i hj0
    have hj0' : ¬ j.val > 0 := by scalar_tac
    rw [WP.spec_ok, if_neg hj0']
    refine ⟨hInv, ?_⟩
    rw [stage_none]

end difffold_kernel_extract
