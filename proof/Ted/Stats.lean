import Mirror2
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! `ted_stats`: the orientation choice never changes the distance. -/

theorem kr_mem (a : ted.PostTree) (hW : PT.Wf a) (k : Std.U32) (hk : k ∈ a.keyroots.val) :
    1 ≤ k.val ∧ k.val ≤ a.label.length := by
  have := (hW.krt k.val).mp ⟨k, hk, rfl⟩
  have h2 := hW.n2
  obtain ⟨h1, h3, _⟩ := this
  refine ⟨h1, ?_⟩
  have : a.lml.val.length = a.label.length := h2
  omega

theorem kr_len (a : ted.PostTree) (hW : PT.Wf a) : a.keyroots.val.length ≤ a.label.length := by
  have hs := hW.krs
  have hnd : (a.keyroots.val.map (fun k => k.val)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hs.imp (fun h => Nat.ne_of_lt h)
  have hsub : a.keyroots.val.map (fun k => k.val) ⊆ List.range' 1 a.label.length := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    have := kr_mem a hW k hk
    rw [List.mem_range']; exact ⟨k.val - 1, by omega, by omega⟩
  have := nodup_length_le _ _ hnd hsub
  simpa using this

theorem keyroot_work_loop_spec (a : ted.PostTree) (hW : PT.Wf a) (hn : a.label.length < 2 ^ 14)
    (s : Std.U128) (i : Std.Usize) (hi : i.val ≤ a.keyroots.val.length)
    (hs : s.val + (a.keyroots.val.length - i.val) * a.label.length < 2 ^ 100) :
    ted.keyroot_work_loop a s i ⦃ r => r.val ≤ s.val + (a.keyroots.val.length - i.val) * a.label.length ⦄ := by
  unfold ted.keyroot_work_loop
  apply loop.spec_decr_nat
    (measure := fun st => a.keyroots.val.length - st.2.val)
    (inv := fun st => st.2.val ≤ a.keyroots.val.length ∧
      st.1.val + (a.keyroots.val.length - st.2.val) * a.label.length ≤ s.val + (a.keyroots.val.length - i.val) * a.label.length)
  · intro st hst
    obtain ⟨s1, i1⟩ := st
    obtain ⟨h1, h2⟩ := hst
    dsimp only at h1 h2 ⊢
    unfold ted.keyroot_work_loop.body
    have hlk : (alloc.vec.Vec.len a.keyroots).val = a.keyroots.val.length := alloc.vec.Vec.len_val _
    by_cases hlt : i1 < alloc.vec.Vec.len a.keyroots
    · rw [if_pos hlt]
      have hlt' : i1.val < a.keyroots.val.length := by
        have : i1.val < (alloc.vec.Vec.len a.keyroots).val := hlt
        omega
      step as ⟨k, hk⟩
      have hkm : k ∈ a.keyroots.val := by rw [hk]; exact List.getElem_mem _
      have hk1 := kr_mem a hW k hkm
      have hcast : (UScalar.cast .Usize k).val = k.val := U32.cast_Usize_val_eq k
      simp only [lift, bind_tc_ok]
      step as ⟨i2, hi2⟩
      have hlml : a.lml.val.length = a.label.length := hW.n2
      have hlml' : a.lml.length = a.label.length := hW.n2
      step as ⟨i4, hi4⟩
      have hi4' : i4.val = laOf a k.val := by
        rw [laOf_eq1 a _ hk1.1 hk1.2, hi4, getG_eq _ _ (by omega)]
        congr 2; omega
      have hle := (hW.wfl.1 k.val hk1.1).2
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      have hge := (hW.wfl.1 k.val hk1.1).1
      have hc2 : (UScalar.cast .U128 i6).val = i6.val := by
        rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by omega)
      have hmul : (a.keyroots.val.length - i1.val) * a.label.length =
          a.label.length + (a.keyroots.val.length - (i1.val + 1)) * a.label.length := by
        have : a.keyroots.val.length - i1.val = (a.keyroots.val.length - (i1.val + 1)) + 1 := by omega
        rw [this, Nat.add_mul]; omega
      step as ⟨s2, hs2⟩
      step as ⟨i8, hi8⟩
      refine ⟨by omega, ?_, by omega⟩
      rw [hi8]
      omega
    · rw [if_neg hlt]
      simp only [WP.spec_ok]
      have : i1.val = a.keyroots.val.length := by
        have : ¬ i1.val < (alloc.vec.Vec.len a.keyroots).val := hlt
        omega
      rw [this] at h2
      simpa using h2
  · exact ⟨hi, Nat.le_refl _⟩

theorem keyroot_work_spec (a : ted.PostTree) (hW : PT.Wf a) (hn : a.label.length < 2 ^ 14) :
    ted.keyroot_work a ⦃ r => r.val ≤ a.label.length * a.label.length ⦄ := by
  unfold ted.keyroot_work
  have := keyroot_work_loop_spec a hW hn 0#u128 0#usize (by simp) (by
    have := kr_len a hW
    have : a.keyroots.val.length * a.label.length ≤ 2 ^ 14 * 2 ^ 14 := Nat.mul_le_mul (by omega) (by omega)
    show 0 + (a.keyroots.val.length - 0) * a.label.length < 2 ^ 100
    simp only [Nat.sub_zero, Nat.zero_add]; omega)
  refine WP.spec_mono this ?_
  intro r hr
  have := kr_len a hW
  have : a.keyroots.val.length * a.label.length ≤ a.label.length * a.label.length :=
    Nat.mul_le_mul_right _ (by omega)
  change r.val ≤ 0 + (a.keyroots.val.length - 0) * a.label.length at hr
  simp only [Nat.sub_zero, Nat.zero_add] at hr; omega

theorem cost_against_spec (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (hna : a.label.length < 2 ^ 14)
    (hnb : b.label.length < 2 ^ 14) : ted.PostTree.cost_against a b ⦃ _ => True ⦄ := by
  unfold ted.PostTree.cost_against
  refine WP.spec_bind (keyroot_work_spec a hA hna) ?_
  intro i hi
  refine WP.spec_bind (keyroot_work_spec b hB hnb) ?_
  intro i1 hi1
  have h1 : i.val ≤ 2 ^ 14 * 2 ^ 14 := le_trans hi (Nat.mul_le_mul (by omega) (by omega))
  have h2 : i1.val ≤ 2 ^ 14 * 2 ^ 14 := le_trans hi1 (Nat.mul_le_mul (by omega) (by omega))
  have h3 : i.val * i1.val ≤ 2 ^ 28 * 2 ^ 28 := Nat.mul_le_mul h1 h2
  step as ⟨r, hr⟩

theorem TED_mirror (a b ma mb : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (hMa : PT.Wf ma) (hMb : PT.Wf mb)
    (ha : MirrorOf a ma) (hb : MirrorOf b mb) : TED ma mb = TED a b := by
  unfold TED
  rw [ha.n1, hb.n1]
  symm
  apply D_mirror hA.wfl hB.wfl hMa.wfl hMb.wfl ha.lam hb.lam
  intro x y hx1 hx2 hy1 hy2
  unfold rcost
  have hpa := pim_mem hA.wfl (n := a.label.length) hx1 hx2
  have hpb := pim_mem hB.wfl (n := b.label.length) hy1 hy2
  rw [ha.lab x hx1 hx2, hb.lab y hy1 hy2, ha.knd x hx1 hx2, hb.knd y hy1 hy2]

theorem mirror_label_bound (a ma : ted.PostTree) (hA : PT.Wf a) (ha : MirrorOf a ma)
    (hla : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31) :
    ∀ j < ma.label.length, (ma.label.val[j]!).val < 2 ^ 31 := by
  intro j hj
  rw [ha.n1] at hj
  obtain ⟨x, hx1, hx2, hx3⟩ := pim_surj hA.wfl (n := a.label.length) (y := j + 1) (by omega) (by omega)
  have := ha.lab x hx1 hx2
  rw [hx3] at this
  simp only [Nat.add_sub_cancel] at this
  rw [this]
  exact hla (x - 1) (by omega)

theorem ted_stats_spec (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (hna : a.label.length < 2 ^ 14)
    (hnb : b.label.length < 2 ^ 14) (hla : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31)
    (hlb : ∀ j < b.label.length, (b.label.val[j]!).val < 2 ^ 31) :
    ted.ted_stats a b ⦃ r => r.1.val = TED a b ⦄ := by
  unfold ted.ted_stats
  have hea : ted.PostTree.is_empty a = ok false := by
    unfold ted.PostTree.is_empty
    have : alloc.vec.Vec.len a.label ≠ 0#usize := by
      intro h
      have := alloc.vec.Vec.len_val a.label
      have h2 : (alloc.vec.Vec.len a.label).val = 0 := by rw [h]; rfl
      have := hA.pos; omega
    simp [this]
  have heb : ted.PostTree.is_empty b = ok false := by
    unfold ted.PostTree.is_empty
    have : alloc.vec.Vec.len b.label ≠ 0#usize := by
      intro h
      have := alloc.vec.Vec.len_val b.label
      have h2 : (alloc.vec.Vec.len b.label).val = 0 := by rw [h]; rfl
      have := hB.pos; omega
    simp [this]
  simp only [ted.Stats.Insts.CoreDefaultDefault.default, core.default.DefaultBool.default,
    core.default.DefaultU64.default, core.default.DefaultU32.default, bind_tc_ok, hea, heb, Bool.false_eq_true,
    ↓reduceIte]
  refine WP.spec_bind (mirror_spec a hA hna) ?_
  rintro ma ⟨hMa, hMA⟩
  refine WP.spec_bind (mirror_spec b hB hnb) ?_
  rintro mb ⟨hMb, hMB⟩
  refine WP.spec_bind (cost_against_spec ma mb hMa hMb (by rw [hMA.n1]; exact hna) (by rw [hMB.n1]; exact hnb)) ?_
  intro c1 _
  refine WP.spec_bind (cost_against_spec a b hA hB hna hnb) ?_
  intro c2 _
  have hT := TED_mirror a b ma mb hA hB hMa hMb hMA hMB
  split
  · refine WP.spec_mono (ted_oriented_wf ma mb hMa hMb (by rw [hMA.n1]; exact hna) (by rw [hMB.n1]; exact hnb)
      (mirror_label_bound a ma hA hMA hla) _) ?_
    intro r hr; rw [hr]; exact hT
  · exact ted_oriented_wf a b hA hB hna hnb hla _

end difffold_lines_extract
