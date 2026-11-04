import Cell
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

variable {O : Type} {inst : kernel.Oracle O}

/-- The model's cell in uniform form, for any row `i >= 1` and any column. -/
theorem P_cell (g : Grid) (h : Nat → Nat → Nat) (tau i j : Nat) (hi : 1 ≤ i) :
    g.P h tau i j =
      keep h tau i j
        (omin (omin (oadd (g.P h tau (i - 1) j) (g.sa (i - 1)))
                    (oadd (if j = 0 then none else g.P h tau i (j - 1)) (g.sb (j - 1))))
              (oadd (if j = 0 then none else g.P h tau (i - 1) (j - 1)) (g.dd (i - 1) (j - 1)))) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  cases j with
  | zero => simp [Grid.P, oadd, omin]; cases g.P h tau i' 0 <;> simp [omin]
  | succ j' => simp [Grid.P]

/-- Every kept model cell fits under the threshold. -/
theorem P_le_tau (g : Grid) (h : Nat → Nat → Nat) (tau i j v : Nat) (hv : g.P h tau i j = some v) :
    v ≤ tau := by
  have := Grid.P_fits (g := g) (h := h) (tau := tau) i j v hv
  omega

/-- One cell of the kernel's row is the model's cell. -/
theorem cell_value_spec (C : Ctx O inst) (o : O) (prev : kernel.Row) (v : alloc.vec.Vec Std.U32)
    (i j plo : Std.Usize) (c : kernel.Counters)
    (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ C.g.n) (hj : j.val ≤ C.g.m) (hpl : plo.val ≤ j.val)
    (hInv : C.Inv o)
    (hprev : ∀ j' ≤ C.g.m, rowSem prev j' = enc (C.g.P C.h C.tau.val (i.val - 1) j'))
    (hvlen : v.length = j.val - plo.val)
    (hv : ∀ t < v.length, v.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (plo.val + t)))
    (hnone : ∀ j' < plo.val, C.g.P C.h C.tau.val i.val j' = none) :
    kernel.cell_value inst o prev v i j plo C.sa C.sb C.ra C.rb C.tau C.on c ⦃ r =>
      C.Inv r.2.1 ∧
      r.1.val ≤ INFn + 2 ^ 27 ∧
      (if r.1.val + C.h i.val j.val ≤ C.tau.val then r.1.val else INFn) =
        enc (C.g.P C.h C.tau.val i.val j.val) ⦄ := by
  have hia : i.val - 1 < C.sa.val.length := by have := C.hn; omega
  have hi2' : i.val ≤ C.sa.val.length := by have := C.hn; omega
  have hjb : j.val ≤ C.sb.val.length := by have := C.hm; omega
  have hsai := C.hsa (i.val - 1) hia
  have hvle : ∀ t < v.length, v.val[t]!.val ≤ INFn := by
    intro t ht
    rw [hv t ht]
    cases hP : C.g.P C.h C.tau.val i.val (plo.val + t) with
    | none => simp [enc]
    | some x => have := P_le_tau _ _ _ _ _ _ hP; have := C.htau; simp [enc]; omega
  unfold kernel.cell_value
  step with del_cand_spec prev j C.sa i hi1 hi2' hsai as ⟨del, hdel⟩
  step with ins_cand_spec v j plo C.sb hpl hvlen hjb hvle C.hsb as ⟨ins, hins⟩
  step with umin_spec del ins as ⟨best0, hb0, hb0a, hb0b⟩
  step with diag_stage_spec C o prev i j best0 c hi1 hi2 hj hInv as ⟨best, hInv1, hbestv⟩
  refine ⟨hInv1, ?_, ?_⟩
  · have h1 := diagStage_le C.on (C.h i.val j.val) C.tau.val (C.g.sa (i.val - 1)) (C.g.sb (j.val - 1))
      (C.g.dd (i.val - 1) (j.val - 1)) best0.val (if j.val > 0 then rowSem prev (j.val - 1) else INFn)
    have hb : best.1.val ≤ best0.val := by rw [hbestv]; exact h1
    have hdl : del.val ≤ INFn + 2 ^ 27 := by
      rw [hdel]; split_ifs with hh
      · omega
      · omega
    omega
  have hPc := P_cell C.g C.h C.tau.val i.val j.val hi1
  have hup_eq : rowSem prev j.val = enc (C.g.P C.h C.tau.val (i.val - 1) j.val) := hprev j.val hj
  have hD : (if j.val > 0 then rowSem prev (j.val - 1) else INFn) =
      enc (if j.val = 0 then none else C.g.P C.h C.tau.val (i.val - 1) (j.val - 1)) := by
    by_cases hj0 : j.val = 0
    · simp [hj0, enc]
    · have hpos : j.val > 0 := by omega
      simp only [if_pos hpos, if_neg hj0]; exact hprev _ (by omega)
  have hsa' : C.g.sa (i.val - 1) ≤ 2 ^ 27 := by rw [C.hgsa]; exact hsai
  have hsb' : ((if j.val = 0 then none else C.g.P C.h C.tau.val i.val (j.val - 1)) ≠ none ∨
      (if j.val = 0 then none else C.g.P C.h C.tau.val (i.val - 1) (j.val - 1)) ≠ none) →
      C.g.sb (j.val - 1) ≤ 2 ^ 27 := by
    intro h
    have hj0 : j.val ≠ 0 := by
      intro hz; rcases h with h | h <;> simp [hz] at h
    rw [C.hgsb]; exact C.hsb _ (by omega)
  have hdd' : (if j.val = 0 then none else C.g.P C.h C.tau.val (i.val - 1) (j.val - 1)) ≠ none →
      C.g.dd (i.val - 1) (j.val - 1) ≤ 2 ^ 28 := by
    intro h
    have hj0 : j.val ≠ 0 := by intro hz; simp [hz] at h
    exact C.hdd _ _ (by omega) (by omega)
  have hsize' : C.on = true →
      (if j.val = 0 then none else C.g.P C.h C.tau.val (i.val - 1) (j.val - 1)) ≠ none →
      C.g.sa (i.val - 1) ≤ C.g.sb (j.val - 1) + C.g.dd (i.val - 1) (j.val - 1) ∧
      C.g.sb (j.val - 1) ≤ C.g.sa (i.val - 1) + C.g.dd (i.val - 1) (j.val - 1) := by
    intro hon h
    have hj0 : j.val ≠ 0 := by intro hz; simp [hz] at h
    exact C.hsize hon _ _ (by omega) (by omega)
  have hup : ∀ u, C.g.P C.h C.tau.val (i.val - 1) j.val = some u → u ≤ C.tau.val :=
    fun u h => P_le_tau _ _ _ _ _ _ h
  have hlf : ∀ l, (if j.val = 0 then none else C.g.P C.h C.tau.val i.val (j.val - 1)) = some l →
      l ≤ C.tau.val := by
    intro l h
    by_cases hj0 : j.val = 0
    · simp [hj0] at h
    · simp only [if_neg hj0] at h; exact P_le_tau _ _ _ _ _ _ h
  have hdg : ∀ d, (if j.val = 0 then none else C.g.P C.h C.tau.val (i.val - 1) (j.val - 1)) = some d →
      d ≤ C.tau.val := by
    intro d h
    by_cases hj0 : j.val = 0
    · simp [hj0] at h
    · simp only [if_neg hj0] at h; exact P_le_tau _ _ _ _ _ _ h
  have hdel1 : ∀ u, C.g.P C.h C.tau.val (i.val - 1) j.val = some u →
      del.val = u + C.g.sa (i.val - 1) := by
    intro u hu
    have hle := P_le_tau _ _ _ _ _ _ hu
    have hT := C.htau
    rw [hdel, hup_eq, hu, C.hgsa]
    simp only [enc]
    rw [if_pos (by omega)]
  have hdel2 : C.g.P C.h C.tau.val (i.val - 1) j.val = none → del.val = INFn := by
    intro hn
    rw [hdel, hup_eq, hn]; simp [enc]
  have hins1 : ∀ l, (if j.val = 0 then none else C.g.P C.h C.tau.val i.val (j.val - 1)) = some l →
      ins.val = l + C.g.sb (j.val - 1) := by
    intro l hl
    have hj0 : j.val ≠ 0 := by intro hz; simp [hz] at hl
    simp only [if_neg hj0] at hl
    have hgt : j.val > plo.val := by
      by_contra hle
      have := hnone (j.val - 1) (by omega)
      rw [this] at hl; cases hl
    have e := hv (v.length - 1) (by omega)
    have hidx : plo.val + (v.length - 1) = j.val - 1 := by omega
    rw [hidx, hl] at e
    rw [hins, if_pos hgt, e, C.hgsb]
    simp [enc]
  have hins2 : (if j.val = 0 then none else C.g.P C.h C.tau.val i.val (j.val - 1)) = none →
      INFn ≤ ins.val := by
    intro hn
    rw [hins]
    split_ifs with hgt
    · have hj0 : j.val ≠ 0 := by omega
      simp only [if_neg hj0] at hn
      have e := hv (v.length - 1) (by omega)
      have hidx : plo.val + (v.length - 1) = j.val - 1 := by omega
      rw [hidx, hn] at e
      simp only [enc] at e
      omega
    · exact le_rfl
  have key := kcell_eq_model C.on (C.h i.val j.val) C.tau.val (C.g.sa (i.val - 1))
    (C.g.sb (j.val - 1)) (C.g.dd (i.val - 1) (j.val - 1)) del.val ins.val
    (C.g.P C.h C.tau.val (i.val - 1) j.val)
    (if j.val = 0 then none else C.g.P C.h C.tau.val i.val (j.val - 1))
    (if j.val = 0 then none else C.g.P C.h C.tau.val (i.val - 1) (j.val - 1))
    C.htau hsa' hsb' hdd' hup hlf hdg hsize' hdel1 hdel2 hins1 hins2
  rw [hPc]
  rw [show ∀ co, enc (keep C.h C.tau.val i.val j.val co) = keepEnc (C.h i.val j.val) C.tau.val co from
    fun co => enc_keep (C.h i.val j.val) C.tau.val co]
  rw [← key]
  unfold kcell
  rw [hbestv, hb0, hD]

end difffold_kernel_extract
