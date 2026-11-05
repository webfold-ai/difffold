import RealCompact
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

@[step]
theorem lift_spec' {α : Type} (x : α) : lift x ⦃ y => y = x ⦄ := by simp [lift]

theorem diff_ids_spec (a b : Slice U32) (n_ids : Usize) (A B : List Nat)
    (ha : vals a.val = A) (hb : vals b.val = B) (hN : A.length + B.length ≤ NMAX)
    (hid : ∀ x ∈ A ++ B, x < n_ids.val) :
    lines.diff_ids a b n_ids ⦃ r => ∃ da di, Myers.Optimal A B da di ∧
      r.deleted.val = da ∧ r.inserted.val = di ⦄ := by
  unfold lines.diff_ids
  have hal : a.val.length = A.length := by have := congrArg List.length ha; simpa [vals] using this
  have hbl : b.val.length = B.length := by have := congrArg List.length hb; simpa [vals] using this
  have hcl : core.clone.CloneBool.clone false = ok false := rfl
  step as ⟨deleted, hd1, hd2⟩
  step as ⟨inserted, hi1, hi2⟩
  step with (common_prefix_u32 a b) as ⟨pre, hs1, hs2, hs3⟩
  step as ⟨s, hsv⟩
  step as ⟨s1, hs1v⟩
  step with (common_suffix_u32 s s1) as ⟨suf, he1, he2, he3⟩
  rw [hs1v, hsv] at he1 he2 he3
  have hTrim := trim_slices a.val b.val pre.val suf.val hs1 hs2 hs3 he1 he2 he3
  clear hs3 he3
  have hse : pre.val + suf.val ≤ a.val.length ∧ pre.val + suf.val ≤ b.val.length := by
    simp only [List.length_drop] at he1; omega
  have hs1' : pre.val ≤ a.val.length ∧ pre.val ≤ b.val.length := by
    simp only [Nat.le_min] at hs1; exact hs1
  have hlA : a.len.val = a.val.length := by simp [Slice.len]
  have hlB : b.len.val = b.val.length := by simp [Slice.len]
  step as ⟨i3, hi3⟩
  step as ⟨am, hamv, haml⟩
  step as ⟨i5, hi5⟩
  step as ⟨bm, hbmv, hbml⟩
  have hi3v : i3.val = a.val.length - suf.val := by rw [hi3, hlA]
  have hi5v : i5.val = b.val.length - suf.val := by rw [hi5, hlB]
  have ham' : vals am.val = ((vals a.val).drop pre.val).take (a.val.length - pre.val - suf.val) := by
    rw [hamv]; simp [List.slice, vals, List.map_take, List.map_drop]
    congr 1; omega
  have hbm' : vals bm.val = ((vals b.val).drop pre.val).take (b.val.length - pre.val - suf.val) := by
    rw [hbmv]; simp [List.slice, vals, List.map_take, List.map_drop]
    congr 1; omega
  obtain ⟨p, A1, B1, sf, hT, hpl, hA1l, hB1l, hA1, hB1, hsfl⟩ : ∃ p A1 B1 sf, Myers.Trim A B p A1 B1 sf ∧
      p.length = pre.val ∧ A1.length = am.val.length ∧ B1.length = bm.val.length ∧
      vals am.val = A1 ∧ vals bm.val = B1 ∧ sf.length = suf.val := by
    refine ⟨(vals a.val).take pre.val, _, _, (vals a.val).drop (a.val.length - suf.val), ?_, ?_, ?_, ?_, ham', hbm', ?_⟩
    · rw [← ha, ← hb]; exact hTrim
    · simp [vals_len]; omega
    · rw [← vals_len am.val, ham']
    · rw [← vals_len bm.val, hbm']
    · simp [vals_len]; omega
  have hnc : core.clone.CloneBool.clone false = ok false := rfl
  step as ⟨in_a, hia, hial⟩
  have hmemA : ∀ x ∈ vals am.val, x ∈ A ++ B := by
    intro x hx
    have h1 : x ∈ A1 := by rw [← hA1]; exact hx
    have hA := hT.1
    have : x ∈ A := by rw [hA]; simp [h1]
    simp [this]
  have hmemB : ∀ x ∈ vals bm.val, x ∈ A ++ B := by
    intro x hx
    have h1 : x ∈ B1 := by rw [← hB1]; exact hx
    have hB := hT.2.1
    have : x ∈ B := by rw [hB]; simp [h1]
    simp [this]
  step as ⟨s2, back1, hdm1⟩
  have hs2 : s2 = in_a.slice := (Prod.mk.inj hdm1).1
  have hb1 : back1 = fun s => ({ slice := s } : alloc.vec.Vec Bool) := (Prod.mk.inj hdm1).2
  have hs2v : s2.val = List.replicate n_ids.val false := by rw [hs2]; exact hia
  have hidsA : ∀ x ∈ vals am.val, x < s2.val.length := by
    intro x hx; rw [hs2v]; simp only [List.length_replicate]
    exact hid x (hmemA x hx)
  step with (mark_ids_spec am.val.length am s2 rfl hidsA) as ⟨s3, hs3⟩
  step as ⟨s4, back2, hdm2⟩
  have hs4 : s4 = in_a.slice := (Prod.mk.inj hdm2).1
  have hb2 : back2 = fun s => ({ slice := s } : alloc.vec.Vec Bool) := (Prod.mk.inj hdm2).2
  have hs4v : s4.val = List.replicate n_ids.val false := by rw [hs4]; exact hia
  have hidsB : ∀ x ∈ vals bm.val, x < s4.val.length := by
    intro x hx; rw [hs4v]; simp only [List.length_replicate]
    exact hid x (hmemB x hx)
  step with (mark_ids_spec bm.val.length bm s4 rfl hidsB) as ⟨s5, hs5⟩
  have hmarkB : ∀ x ∈ vals am.val, s5.val[x]? = some (decide (x ∈ B1)) := by
    intro x hx
    have hxn : x < n_ids.val := hid x (hmemA x hx)
    rw [hs5, hs4v, ← hB1, markOf_get _ _ (by intro y hy; simp; exact hid y (hmemB y hy)) x (by simpa using hxn)]
    by_cases hxB : x ∈ vals bm.val
    · simp [hxB]
    · simp [hxB, List.getElem?_replicate, hxn]
  have hmarkA : ∀ x ∈ vals bm.val, s3.val[x]? = some (decide (x ∈ A1)) := by
    intro x hx
    have hxn : x < n_ids.val := hid x (hmemB x hx)
    rw [hs3, hs2v, ← hA1, markOf_get _ _ (by intro y hy; simp; exact hid y (hmemA y hy)) x (by simpa using hxn)]
    by_cases hxA : x ∈ vals am.val
    · simp [hxA]
    · simp [hxA, List.getElem?_replicate, hxn]
  have hUm : 4294967295 ≤ Usize.max := by scalar_tac
  have hNM : A.length + B.length ≤ 268435456 := by simpa [NMAX] using hN
  have hamL : pre.val + am.val.length ≤ a.val.length := by simp [Slice.length] at haml; omega
  have hbmL : pre.val + bm.val.length ≤ b.val.length := by simp [Slice.length] at hbml; omega
  have hother2 : (back2 s5).deref = s5 := by
    rw [hb2]; show alloc.vec.Vec.deref ⟨s5⟩ = s5
    unfold alloc.vec.Vec.deref; rw [Slice.eq_iff]; simp [alloc.vec.Vec.val]
  have hother1 : (back1 s3).deref = s3 := by
    rw [hb1]; show alloc.vec.Vec.deref ⟨s3⟩ = s3
    unfold alloc.vec.Vec.deref; rw [Slice.eq_iff]; simp [alloc.vec.Vec.val]
  rw [hother2, hother1]
  step as ⟨s7, back3, hdm3⟩
  have hs7 : s7 = deleted.slice := (Prod.mk.inj hdm3).1
  have hb3 : back3 = fun s => ({ slice := s } : alloc.vec.Vec Bool) := (Prod.mk.inj hdm3).2
  have hs7v : s7.val = List.replicate a.val.length false := by
    rw [hs7]; show deleted.val = _; rw [hd1, hlA]
  step with (compact_ids_spec (fun x => decide (x ∈ B1)) am.val.length am pre s5 (alloc.vec.Vec.new U32)
    (alloc.vec.Vec.new Usize) s7 rfl hmarkB (by rw [hs7v]; simp; omega) (by simp; omega) (by simp; omega))
    as ⟨ca, pa, s8, c1, c2, c3⟩
  step as ⟨s10, back4, hdm4⟩
  have hs10 : s10 = inserted.slice := (Prod.mk.inj hdm4).1
  have hb4 : back4 = fun s => ({ slice := s } : alloc.vec.Vec Bool) := (Prod.mk.inj hdm4).2
  have hs10v : s10.val = List.replicate b.val.length false := by
    rw [hs10]; show inserted.val = _; rw [hi1, hlB]
  step with (compact_ids_spec (fun x => decide (x ∈ A1)) bm.val.length bm pre s3 (alloc.vec.Vec.new U32)
    (alloc.vec.Vec.new Usize) s10 rfl hmarkA (by rw [hs10v]; simp; omega) (by simp; omega) (by simp; omega))
    as ⟨cb, pb, s11, d1, d2, d3⟩
  step as ⟨ra, hra, hral⟩
  step as ⟨rb, hrb, hrbl⟩
  have hcav : vals ca.val = (vals am.val).filter (fun x => decide (x ∈ B1)) := by
    rw [c1]; simp [vals]
  have hcbv : vals cb.val = (vals bm.val).filter (fun x => decide (x ∈ A1)) := by
    rw [d1]; simp [vals]
  have hcaL : ca.val.length ≤ am.val.length := by
    have := congrArg List.length hcav
    rw [vals_len] at this
    rw [this]; exact List.length_filter_le _ _ |>.trans (by simp [vals_len])
  have hcbL : cb.val.length ≤ bm.val.length := by
    have := congrArg List.length hcbv
    rw [vals_len] at this
    rw [this]; exact List.length_filter_le _ _ |>.trans (by simp [vals_len])
  have hcalen : ca.len.val = ca.val.length := by simp [alloc.vec.Vec.len]
  have hcblen : cb.len.val = cb.val.length := by simp [alloc.vec.Vec.len]
  have hnc32 : core.clone.CloneI32.clone 0#i32 = ok 0#i32 := rfl
  step as ⟨i10, hi10⟩
  step as ⟨i11, hi11⟩
  step as ⟨size, hsize⟩
  step as ⟨vf, hvf, hvfl⟩
  step as ⟨s14, back5, hdm5⟩
  step as ⟨s15, back6, hdm6⟩
  step as ⟨s16, b7, hdm7⟩
  step as ⟨s17, b8, hdm8⟩
  have hs14 : s14 = ra.slice := (Prod.mk.inj hdm5).1
  have hs15 : s15 = rb.slice := (Prod.mk.inj hdm6).1
  have hs16 : s16 = vf.slice := (Prod.mk.inj hdm7).1
  have hs17 : s17 = vf.slice := (Prod.mk.inj hdm8).1
  have hb5 : back5 = fun s => ({ slice := s } : alloc.vec.Vec Bool) := (Prod.mk.inj hdm5).2
  have hb6 : back6 = fun s => ({ slice := s } : alloc.vec.Vec Bool) := (Prod.mk.inj hdm6).2
  have hs14v : s14.val = List.replicate ca.val.length false := by
    rw [hs14]; show ra.val = _; rw [hra, hcalen]
  have hs15v : s15.val = List.replicate cb.val.length false := by
    rw [hs15]; show rb.val = _; rw [hrb, hcblen]
  have hsizev : size.val = 2 * (ca.val.length + cb.val.length) + 3 := by
    rw [hsize, hi11, hi10, hcalen, hcblen]
  have hs16l : s16.val.length = 2 * (ca.val.length + cb.val.length) + 3 := by
    rw [hs16]; show vf.val.length = _; rw [hvf]; simp [hsizev]
  have hs17l : s17.val.length = 2 * (ca.val.length + cb.val.length) + 3 := by
    rw [hs17]; show vf.val.length = _; rw [hvf]; simp [hsizev]
  have hderCa : (alloc.vec.Vec.deref ca).val = ca.val := by simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  have hderCb : (alloc.vec.Vec.deref cb).val = cb.val := by simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  have hcalN : (vals ca.val).length = ca.val.length := vals_len _
  have hcbN : (vals cb.val).length = cb.val.length := vals_len _
  have hNM2 : (vals ca.val).length + (vals cb.val).length ≤ NMAX := by
    have : NMAX = 268435456 := by decide
    rw [this, hcalN, hcbN]; omega
  step with (solve_spec _ (alloc.vec.Vec.deref ca) (alloc.vec.Vec.deref cb) (vals ca.val) (vals cb.val)
    0#usize 0#usize s14 s15 s16 s17 rfl (by rw [hderCa]) (by rw [hderCb]) hNM2
    (by rw [hs14v]; simp; omega) (by rw [hs15v]; simp; omega)
    (by intro j hj; rw [hs14v]; simp [List.getElem?_replicate]; omega)
    (by intro j hj; rw [hs15v]; simp [List.getElem?_replicate]; omega)
    (by rw [hs16l, hcalN, hcbN]) (by rw [hs17l, hcalN, hcbN])) as ⟨s18, s19, vf2, vb2, hsol⟩
  obtain ⟨da, di, hS, hra', hrb', _, _⟩ := hsol
  have hdl := Myers.Solve.lens hS
  have h0u : (0#usize).val = 0 := rfl
  rw [h0u] at hra' hrb'
  have hs18 : s18.val = da := by
    rw [hra', hs14v, Myers.splice_full _ _ (by simp [hdl.1, hcalN])]
  have hs19 : s19.val = di := by
    rw [hrb', hs15v, Myers.splice_full _ _ (by simp [hdl.2, hcbN])]
  step as ⟨s22, back9, hdm9⟩
  have hs22 : s22 = s8 := by
    have := (Prod.mk.inj hdm9).1
    rw [this, hb3]
  have hb9 : back9 = fun s => ({ slice := s } : alloc.vec.Vec Bool) := by
    exact (Prod.mk.inj hdm9).2
  have hs8l : s8.val.length = a.val.length := by rw [c3, Myers.length_editOf, hs7v]; simp
  have hpa : uvals pa.val = Myers.posOf (fun x => decide (x ∈ B1)) (vals am.val) pre.val := by
    rw [c2]; simp [uvals]
  have hder5 : (alloc.vec.Vec.deref (back5 s18)) = s18 := by
    rw [hb5]; show alloc.vec.Vec.deref ⟨s18⟩ = s18
    unfold alloc.vec.Vec.deref; rw [Slice.eq_iff]; simp [alloc.vec.Vec.val]
  have hderpa : (alloc.vec.Vec.deref pa).val = pa.val := by simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  have hpal : pa.val.length = da.length := by
    have h1 := congrArg List.length hpa
    rw [uvals_len', Myers.length_posOf] at h1
    rw [h1, hdl.1, hcalN]
    have := congrArg List.length hcav
    rw [vals_len] at this; omega
  have hbnd : ∀ q ∈ uvals (alloc.vec.Vec.deref pa).val, q < s22.val.length := by
    intro q hq
    rw [hderpa, hpa] at hq
    have := Myers.mem_posOf _ _ _ q hq
    rw [hs22, hs8l]; simp [vals_len] at this; omega
  step with (scatter_flags_spec da.length (alloc.vec.Vec.deref (back5 s18)) (alloc.vec.Vec.deref pa) s22
    (by rw [hder5, hs18]) (by rw [hderpa, hpal]) hbnd) as ⟨s23, hs23⟩
  step as ⟨s26, back10, hdm10⟩
  have hs26 : s26 = s11 := by
    have := (Prod.mk.inj hdm10).1
    rw [this, hb4]
  have hb10 : back10 = fun s => ({ slice := s } : alloc.vec.Vec Bool) := (Prod.mk.inj hdm10).2
  have hs11l : s11.val.length = b.val.length := by rw [d3, Myers.length_editOf, hs10v]; simp
  have hpb : uvals pb.val = Myers.posOf (fun x => decide (x ∈ A1)) (vals bm.val) pre.val := by
    rw [d2]; simp [uvals]
  have hder6 : (alloc.vec.Vec.deref (back6 s19)) = s19 := by
    rw [hb6]; show alloc.vec.Vec.deref ⟨s19⟩ = s19
    unfold alloc.vec.Vec.deref; rw [Slice.eq_iff]; simp [alloc.vec.Vec.val]
  have hderpb : (alloc.vec.Vec.deref pb).val = pb.val := by simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  have hpbl : pb.val.length = di.length := by
    have h1 := congrArg List.length hpb
    rw [uvals_len', Myers.length_posOf] at h1
    rw [h1, hdl.2, hcbN]
    have := congrArg List.length hcbv
    rw [vals_len] at this; omega
  have hbnd2 : ∀ q ∈ uvals (alloc.vec.Vec.deref pb).val, q < s26.val.length := by
    intro q hq
    rw [hderpb, hpb] at hq
    have := Myers.mem_posOf _ _ _ q hq
    rw [hs26, hs11l]; simp [vals_len] at this; omega
  step with (scatter_flags_spec di.length (alloc.vec.Vec.deref (back6 s19)) (alloc.vec.Vec.deref pb) s26
    (by rw [hder6, hs19]) (by rw [hderpb, hpbl]) hbnd2) as ⟨s27, hs27⟩
  have hApl : A.length = p.length + A1.length + sf.length := by
    have := congrArg List.length hT.1; simp at this; omega
  have hBpl : B.length = p.length + B1.length + sf.length := by
    have := congrArg List.length hT.2.1; simp at this; omega
  have hfA : da.length = (A1.filter (fun x => decide (x ∈ B1))).length := by
    rw [hdl.1, hcav, hA1]
  have hfB : di.length = (B1.filter (fun x => decide (x ∈ A1))).length := by
    rw [hdl.2, hcbv, hB1]
  have hS' : Myers.Solve Myers.mid (A1.filter (fun x => decide (x ∈ B1))) (B1.filter (fun x => decide (x ∈ A1))) da di := by
    simpa only [hcav, hcbv, hA1, hB1] using hS
  have hOpt0 := Myers.filter_optimal (Myers.solve_optimal Myers.mid_spec hS')
  have hOpt1 := Myers.opt_trim (p := p) (s := sf) hOpt0
  rw [← hT.1, ← hT.2.1] at hOpt1
  have hcs1 := Myers.compact_scatter (fun x => decide (x ∈ B1)) A1 (List.replicate p.length false)
    (List.replicate sf.length false) da hfA
  have hcs2 := Myers.compact_scatter (fun x => decide (x ∈ A1)) B1 (List.replicate p.length false)
    (List.replicate sf.length false) di hfB
  simp only [List.length_replicate] at hcs1 hcs2
  have hpl' := hpl
  rw [hpl] at hcs1 hcs2
  have hrepA : List.replicate a.val.length false =
      List.replicate p.length false ++ List.replicate A1.length false ++ List.replicate sf.length false := by
    rw [hal, hApl, List.replicate_add, List.replicate_add]
  have hrepB : List.replicate b.val.length false =
      List.replicate p.length false ++ List.replicate B1.length false ++ List.replicate sf.length false := by
    rw [hbl, hBpl, List.replicate_add, List.replicate_add]
  refine ⟨_, _, hOpt1, ?_, ?_⟩
  · rw [hb9]; show s23.val = _
    rw [hs23, hder5, hs18, hderpa, hpa, hs22, c3, hs7v, hrepA, hA1, hpl]
    exact hcs1
  · rw [hb10]; show s27.val = _
    rw [hs27, hder6, hs19, hderpb, hpb, hs26, d3, hs10v, hrepB, hB1, hpl]
    exact hcs2

end difffold_myers_extract
