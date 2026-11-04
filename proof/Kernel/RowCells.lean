import RowModel
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_kernel_extract
open Difffold

variable {O : Type} {inst : kernel.Oracle O}

/-- `pick` stores the value when kept and `INF` otherwise. -/
@[step] theorem pick_spec (kept : Bool) (best : Std.U32) :
    kernel.pick kept best ⦃ x => x.val = if kept then best.val else INFn ⦄ := by
  unfold kernel.pick
  split
  · rename_i h; subst h; rw [WP.spec_ok]
  · rename_i h
    have : kept = false := by simpa using h
    subst this
    rw [WP.spec_ok]; simp [kernel_INF_val]

/-- `count_cell` always succeeds (the counters are diagnostics). -/
@[step] theorem count_cell_spec (c : kernel.Counters) (kept : Bool) :
    kernel.count_cell c kept ⦃ r => r.pruned = c.pruned ⦄ := by
  unfold kernel.count_cell
  split <;> step* <;> rfl

/-- The loop of `row_cells`: it builds row `i` of the model from the row above. -/
theorem row_cells_loop_spec (C : Ctx O inst) (plo : Std.Usize) (v : alloc.vec.Vec Std.U32)
    (o : O) (i : Std.Usize) (c : kernel.Counters) (m phi : Std.Usize)
    (v1 : alloc.vec.Vec Std.U32) (j : Std.Usize)
    (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ C.g.n) (hm : m.val = C.g.m) (hmlt : m.val < Std.Usize.max)
    (hphi : phi.val + 1 = plo.val + v.length) (hvpos : 0 < v.length)
    (hspan : plo.val + v.length ≤ C.g.m + 1)
    (hprev : ∀ j' ≤ C.g.m, rowSem { lo := plo, v := v } j' = enc (C.g.P C.h C.tau.val (i.val - 1) j'))
    (hInv : C.Inv o) (hpl : plo.val ≤ j.val) (hjm : j.val ≤ C.g.m)
    (hvlen : v1.length = j.val - plo.val)
    (hvv : ∀ t < v1.length, v1.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (plo.val + t)))
    (hnone : ∀ j' < plo.val, C.g.P C.h C.tau.val i.val j' = none) :
    kernel.row_cells_loop inst { lo := plo, v := v } o plo v i C.sa C.sb C.ra C.rb C.tau C.on c m phi v1 j ⦃ r =>
      C.Inv r.2.1 ∧ 0 < r.1.length ∧ plo.val + r.1.length ≤ C.g.m + 1 ∧
      (∀ t < r.1.length, r.1.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (plo.val + t))) ∧
      (∀ j', plo.val + r.1.length ≤ j' → j' ≤ C.g.m → C.g.P C.h C.tau.val i.val j' = none) ⦄ := by
  unfold kernel.row_cells_loop
  apply loop.spec_decr_nat
    (measure := fun p => m.val + 1 - p.2.2.2.val)
    (inv := fun p => C.Inv p.1 ∧ plo.val ≤ p.2.2.2.val ∧ p.2.2.2.val ≤ C.g.m ∧
      p.2.2.1.length = p.2.2.2.val - plo.val ∧
      ∀ t < p.2.2.1.length, p.2.2.1.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (plo.val + t)))
  · intro p hp
    obtain ⟨o1, c1, v2, j1⟩ := p
    obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    dsimp only at h1 h2 h3 h4 h5 ⊢
    unfold kernel.row_cells_loop.body
    have hira : i.val < C.ra.val.length := by have := C.hn; have := C.hralen; omega
    have hjrb : j1.val < C.rb.val.length := by have := C.hm; have := C.hrblen; omega
    step with cell_value_spec C o1 { lo := plo, v := v } v2 i j1 plo c1 hi1 hi2 h3 h2 h1 hprev h4 h5 hnone as ⟨cv, o2, c2, hInv2, hbound, hcell⟩
    step as ⟨i1, hi1v⟩
    have hbh := hK_le C.ra C.rb C.on i.val j1.val C.hra C.hrb hira hjrb
    have hINF : INFn = 1073741823 := rfl
    step as ⟨i2, hi2v⟩
    step as ⟨c3, hc3⟩
    step as ⟨i3, hi3v⟩
    step as ⟨v3, hv3⟩
    step as ⟨j2, hj2⟩
    step as ⟨i4, hi4⟩
    have hv3len : v3.length = j2.val - plo.val := by
      have : v3.val.length = v2.val.length + 1 := by rw [hv3]; simp
      have h4' : v2.val.length = j1.val - plo.val := h4
      show v3.val.length = _
      omega
    have hi2le : (i2 ≤ C.tau) ↔ cv.val + C.h i.val j1.val ≤ C.tau.val := by
      constructor <;> intro h <;> scalar_tac
    have hi3enc : i3.val = enc (C.g.P C.h C.tau.val i.val j1.val) := by
      rw [← hcell, hi3v]
      by_cases hc : cv.val + C.h i.val j1.val ≤ C.tau.val
      · have : i2 ≤ C.tau := hi2le.mpr hc
        simp [this, hc]
      · have : ¬ (i2 ≤ C.tau) := fun h => hc (hi2le.mp h)
        simp [this, hc]
    have hv3v : ∀ t < v3.length, v3.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (plo.val + t)) := by
      intro t ht
      rcases Nat.lt_or_ge t v2.length with h | h
      · have := h5 t h
        simpa [hv3, List.getElem!_eq_getElem?_getD, List.getElem?_append_left h] using this
      · have ht' : t = v2.length := by omega
        have h6 : (v3.val)[v2.val.length]!.val = i3.val := by
          rw [hv3]; simp [List.getElem!_eq_getElem?_getD]
        have h7 : v2.val.length = v2.length := rfl
        rw [h7] at h6
        have hidx : plo.val + v2.length = j1.val := by omega
        rw [ht', h6, hi3enc, hidx]
    have hcont : j2.val ≤ C.g.m → C.Inv o2 ∧ plo.val ≤ j2.val ∧ j2.val ≤ C.g.m ∧
        v3.length = j2.val - plo.val ∧
        (∀ t < v3.length, v3.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (plo.val + t))) ∧
        m.val + 1 - j2.val < m.val + 1 - j1.val := by
      intro hle
      exact ⟨hInv2, by omega, hle, hv3len, hv3v, by omega⟩
    have hcc : j2.val ≤ m.val → (C.Inv o2 ∧ plo.val ≤ j2.val ∧ j2.val ≤ C.g.m ∧
        v3.length = j2.val - plo.val ∧
        (∀ t < v3.length, v3.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (plo.val + t)))) ∧
        m.val + 1 - j2.val < m.val + 1 - j1.val := by
      intro hle
      have := hcont (by omega)
      exact ⟨⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1⟩, this.2.2.2.2.2⟩
    have hdone : j2.val > m.val ∨ (phi.val + 1 < j2.val ∧ INFn ≤ i3.val) →
        C.Inv o2 ∧ 0 < v3.length ∧ plo.val + v3.length ≤ C.g.m + 1 ∧
        (∀ t < v3.length, v3.val[t]!.val = enc (C.g.P C.h C.tau.val i.val (plo.val + t))) ∧
        (∀ j', plo.val + v3.length ≤ j' → j' ≤ C.g.m → C.g.P C.h C.tau.val i.val j' = none) := by
      intro hd
      have hpos : 0 < v3.length := by omega
      have hrng : plo.val + v3.length ≤ C.g.m + 1 := by
        have := hcont
        omega
      refine ⟨hInv2, hpos, hrng, hv3v, ?_⟩
      rcases hd with hgt | ⟨hgt2, hge3'⟩
      · intro j' h1 h2
        exfalso; omega
      · have hpruned : C.g.P C.h C.tau.val i.val j1.val = none := by
          apply enc_ge_none _ _ _ _ _ (by have := C.htau; omega)
          rw [← hi3enc]; exact hge3'
        have hbeyond : ∀ j'', j2.val - 1 ≤ j'' → j'' ≤ C.g.m →
            C.g.P C.h C.tau.val (i.val - 1) j'' = none := by
          intro j'' h1 h2
          have hrow := hprev j'' h2
          have hrs : rowSem { lo := plo, v := v } j'' = INFn := by
            unfold rowSem
            simp only []
            split_ifs <;> first | rfl | omega
          rw [hrs] at hrow
          exact enc_inf_none _ _ _ _ _ (by have := C.htau; omega) hrow.symm
        have := P_tail_none C.g C.h C.tau.val i.val j2.val C.g.m hi1 (by omega) hbeyond
          (by rw [show j2.val - 1 = j1.val by omega]; exact hpruned)
        intro j' h1 h2
        exact this j' (by omega) h2
    split
    · rename_i hgt
      simp only [WP.spec_ok]
      exact hdone (Or.inl (by scalar_tac))
    · rename_i hle1
      have hle1' : j2.val ≤ m.val := by scalar_tac
      split
      · simp only [WP.spec_ok]
        exact hcont (by omega)
      · split
        · simp only [WP.spec_ok]
          exact hcont (by omega)
        · rename_i hge3
          simp only [WP.spec_ok]
          exact hdone (Or.inr ⟨by scalar_tac, by have hk := kernel_INF_val; scalar_tac⟩)
  · exact ⟨hInv, hpl, hjm, hvlen, hvv⟩

end difffold_kernel_extract
