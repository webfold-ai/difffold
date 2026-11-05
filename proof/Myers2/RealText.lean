import RealCut
import InternExact
import RealCommon
import RealDiffIds
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem bytes_inj (l1 l2 : List U8) (h : bytes l1 = bytes l2) : l1 = l2 := by
  unfold bytes at h
  apply List.map_injective_iff.mpr (fun a b hab => UScalar.eq_of_val_eq hab) h

theorem ie_all {A B : List (List U8)} {ia ib : List U32} {n : Nat} (h : InternExact A B ia ib n) :
    ∀ i j : Nat, (ia ++ ib)[i]? = (ia ++ ib)[j]? ↔ (A ++ B)[i]? = (A ++ B)[j]? := by
  obtain ⟨hl1, hl2, _, _, h1, h2, h3, _⟩ := h
  intro i j
  by_cases hi : i < A.length <;> by_cases hj : j < A.length
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact h1 i j
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_left (by omega), List.getElem?_append_right (by omega)]
    rw [hl1]; exact h2 i (j - A.length)
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by omega),
      List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
    rw [hl1]; exact Iff.trans eq_comm (Iff.trans (h2 j (i - A.length)) eq_comm)
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    rw [hl1]; exact h3 _ _


/-- The interner contract gives a numbering function on the byte lines that is injective on the lines in play. -/
theorem intern_map {A B : List (List U8)} {ia ib : List U32} {n : Nat} (h : InternExact A B ia ib n) :
    ∃ g : List Nat → Nat, ia.map (fun u => u.val) = (A.map bytes).map g ∧
      ib.map (fun u => u.val) = (B.map bytes).map g ∧
      ∀ x ∈ A.map bytes ++ B.map bytes, ∀ y ∈ A.map bytes ++ B.map bytes, g x = g y → x = y := by
  have hall := ie_all h
  obtain ⟨hl1, hl2, _⟩ := h
  apply Myers.idsExact_map
  refine ⟨by simp [hl1], by simp [hl2], ?_⟩
  intro i j x y u v hx hy hu hv
  simp only [← List.map_append, List.getElem?_map, Option.map_eq_some_iff] at hx hy hu hv
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨u0, hu0, rfl⟩ := hu
  obtain ⟨v0, hv0, rfl⟩ := hv
  have e := hall i j
  rw [hu0, hv0, ha, hb] at e
  constructor
  · intro huv
    have : u0 = v0 := UScalar.eq_of_val_eq huv
    have := e.mp (by rw [this])
    rw [Option.some.injEq] at this
    rw [this]
  · intro hxy
    have : a = b := bytes_inj _ _ hxy
    have := e.mpr (by rw [this])
    rw [Option.some.injEq] at this
    rw [this]


theorem lines_append_end (u v : List Nat) (hu : u = [] ∨ u.getLast? = some 10) :
    Myers.lines (u ++ v) = Myers.lines u ++ Myers.lines v := Myers.lines_append u v hu

/-- A prefix of `l` that is empty or ends at a newline. -/
theorem take_end10 (l : List Nat) (c : Nat) (hc : c = 0 ∨ l[c - 1]? = some 10) (hcl : c ≤ l.length) :
    (l.take c) = [] ∨ (l.take c).getLast? = some 10 := by
  by_cases hc0 : c = 0
  · left; subst hc0; simp
  · right
    have h : l[c - 1]? = some 10 := by rcases hc with h | h; exact absurd h hc0; exact h
    have hlt : c - 1 < l.length := (List.getElem?_eq_some_iff.mp h).1
    have hlen : (l.take c).length = c := by simp; omega
    rw [List.getLast?_eq_getElem?, hlen]
    simpa [List.getElem?_take, show c - 1 < c by omega] using h

theorem lines_split3 (lo ln : List Nat) (p q : Nat) (hpo : p ≤ lo.length) (hpn : p ≤ ln.length)
    (hpre : lo.take p = ln.take p) (hline : p = 0 ∨ lo[p - 1]? = some 10)
    (hq : SufPost (lo.drop p) (ln.drop p) q q) (hqo : q ≤ (lo.drop p).length) (hqn : q ≤ (ln.drop p).length) :
    Myers.lines lo = Myers.lines (lo.take p) ++
        Myers.lines ((lo.drop p).take ((lo.drop p).length - q)) ++ Myers.lines ((lo.drop p).drop ((lo.drop p).length - q)) ∧
    Myers.lines ln = Myers.lines (lo.take p) ++
        Myers.lines ((ln.drop p).take ((ln.drop p).length - q)) ++ Myers.lines ((lo.drop p).drop ((lo.drop p).length - q)) := by
  obtain ⟨_, hsuf, hbd⟩ := hq
  have hlnline : p = 0 ∨ ln[p - 1]? = some 10 := by
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · right
      have h : lo[p - 1]? = some 10 := by rcases hline with h | h; exact absurd h hp0; exact h
      have := congrArg (fun l => l[p - 1]?) hpre
      simp only [List.getElem?_take] at this
      simpa [show p - 1 < p by omega, h] using this.symm
  have key : ∀ (l : List Nat), p ≤ l.length → (p = 0 ∨ l[p - 1]? = some 10) →
      Myers.lines l = Myers.lines (l.take p) ++ Myers.lines (l.drop p) := by
    intro l hl hh
    conv_lhs => rw [← List.take_append_drop p l]
    exact Myers.lines_append _ _ (take_end10 l p hh hl)
  have hsplit : ∀ (r : List Nat), q ≤ r.length → (q = 0 ∨ (q = r.length ∨ r[r.length - q - 1]? = some 10)) →
      Myers.lines r = Myers.lines (r.take (r.length - q)) ++ Myers.lines (r.drop (r.length - q)) := by
    intro r hr hh
    conv_lhs => rw [← List.take_append_drop (r.length - q) r]
    by_cases hq0 : q = 0
    · subst hq0; simp [Myers.lines]
    · apply Myers.lines_append
      rcases hh with h | h1 | h1
      · exact absurd h hq0
      · left; rw [h1]; simp
      · exact take_end10 r (r.length - q) (Or.inr (by rw [show r.length - q - 1 = r.length - q - 1 from rfl]; exact h1)) (by omega)
  have hso := hsplit (lo.drop p) hqo (by
    rcases hbd with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h)
  have hsn := hsplit (ln.drop p) hqn (by
    rcases hbd with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h)
  rw [← hsuf] at hsn
  constructor
  · rw [key lo hpo hline, hso, List.append_assoc]
  · rw [key ln hpn hlnline, hsn, ← hpre, List.append_assoc]


theorem rep_assemble (N pre : Nat) (d : List Bool) (h : pre + d.length ≤ N) :
    (List.replicate N false).setSlice! pre d =
      List.replicate pre false ++ d ++ List.replicate (N - pre - d.length) false := by
  unfold List.setSlice!
  simp only [List.length_replicate]
  have hn : min d.length (N - pre) = d.length := by omega
  rw [hn, List.take_replicate, List.take_length, List.drop_replicate]
  rw [Nat.min_eq_left (by omega)]
  congr 2
  omega

/-- The contract the line differ needs from the interner of its instance: ids are exact. -/
def LineIdsExact {L : Type} (inst : lines.LineIds L) : Prop :=
  ∀ (a b : Slice (Slice U8)), a.val.length + b.val.length ≤ 2 ^ 28 →
    inst.intern a b ⦃ ia ib n =>
      InternExact (a.val.map (fun s => s.val)) (b.val.map (fun s => s.val)) ia.val ib.val n.val ⦄

theorem diff_text_minimal {L : Type} (inst : lines.LineIds L) (hI : LineIdsExact inst)
    (old new : Slice U8) (B : Nat) (hB : B + 8 ≤ Usize.max) (ho : old.val.length ≤ B) (hn : new.val.length ≤ B)
    (hlines : (Myers.lines (bytes old.val)).length + (Myers.lines (bytes new.val)).length ≤ 2 ^ 28) :
    lines.diff_text_core inst old new lines.Algo.Minimal ⦃ r => ∃ da di,
      r.deleted.val = da ∧ r.inserted.val = di ∧
      Myers.MinL (Myers.lines (bytes old.val)) (Myers.lines (bytes new.val)) da di ∧
      (Myers.applyS (Myers.lines (bytes old.val)) (Myers.lines (bytes new.val)) da di).flatten =
        bytes new.val ⦄ := by
  unfold lines.diff_text_core
  step with (common_prefix_u8 old new) as ⟨i, hi1, hi2, hi3⟩
  have hpi : i.val ≤ old.val.length := by have := Nat.min_le_left old.val.length new.val.length; omega
  step with (line_start_spec old i hpi) as ⟨p, hp1, hp2, hp3⟩
  step as ⟨ro, hro, hrol⟩
  step as ⟨rn, hrn, hrnl⟩
  obtain ⟨hpi', hpline, _⟩ := hp1
  have hpo : p.val ≤ old.val.length := by omega
  have hpn : p.val ≤ new.val.length := by have := Nat.min_le_right old.val.length new.val.length; omega
  have hpre : (bytes old.val).take p.val = (bytes new.val).take p.val := by
    have := congrArg (List.take p.val) hi2
    rw [List.take_take, List.take_take, Nat.min_eq_left hpi'] at this
    rw [← bytes_take, ← bytes_take, this]
  have hrov : bytes ro.val = (bytes old.val).drop p.val := by rw [hro, bytes_drop]
  have hrnv : bytes rn.val = (bytes new.val).drop p.val := by rw [hrn, bytes_drop]
  have hrol' : ro.val.length = old.val.length - p.val := by simpa [Slice.length] using hrol
  have hrnl' : rn.val.length = new.val.length - p.val := by simpa [Slice.length] using hrnl
  step with (common_suffix_u8 ro rn) as ⟨cs, hcs1, hcs2, hcs3⟩
  have hrolB : ro.val.length ≤ B := by omega
  step with (suffix_on_line_start_spec B hB ro rn cs (by omega) (by omega) hrolB
    (by rw [← bytes_drop, ← bytes_drop, hcs2])) as ⟨q, hq⟩
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hqro : q.val ≤ ro.val.length := by omega
  have hqrn : q.val ≤ rn.val.length := by omega
  step as ⟨i3, hi3⟩
  step as ⟨mo, hmo, hmol⟩
  step as ⟨i5, hi5⟩
  step as ⟨mn, hmn, hmnl⟩
  step as ⟨s, hs, hsl⟩
  step with (count_lines_spec s) as ⟨pre_lines, hpl⟩
  step as ⟨i7, hi7⟩
  step as ⟨s1, hs1, hs1l⟩
  step with (count_lines_spec s1) as ⟨suf_old, hso⟩
  step as ⟨i9, hi9⟩
  step as ⟨s2, hs2, hs2l⟩
  step with (count_lines_spec s2) as ⟨suf_new, hsn⟩
  have hmov : mo.val = ro.val.take (ro.val.length - q.val) := by rw [hmo]; simp [List.slice, hi3, Slice.len]
  have hmnv : mn.val = rn.val.take (rn.val.length - q.val) := by rw [hmn]; simp [List.slice, hi5, Slice.len]
  have hsv : s.val = old.val.take p.val := by rw [hs]; simp [List.slice]
  have hs1v : s1.val = ro.val.drop (ro.val.length - q.val) := by rw [hs1]; simp [hi7, Slice.len]
  have hs2v : s2.val = rn.val.drop (rn.val.length - q.val) := by rw [hs2]; simp [hi9, Slice.len]
  have hmol' : mo.val.length ≤ B := by rw [hmov]; simp; omega
  have hmnl' : mn.val.length ≤ B := by rw [hmnv]; simp; omega
  step with (split_lines_spec B hB mo hmol') as ⟨la, hla⟩
  step with (split_lines_spec B hB mn hmnl') as ⟨lb, hlb⟩
  have hdec := lines_split3 (bytes old.val) (bytes new.val) p.val q.val (by simpa [bytes_length] using hpo)
    (by simpa [bytes_length] using hpn) hpre hpline
    (by
      have : (bytes old.val).drop p.val = bytes ro.val := hrov.symm
      have h2 : (bytes new.val).drop p.val = bytes rn.val := hrnv.symm
      rw [this, h2]; exact ⟨le_refl _, hq2, hq3⟩)
    (by rw [← hrov]; simpa [bytes_length] using hqro) (by rw [← hrnv]; simpa [bytes_length] using hqrn)
  rw [← hrov, ← hrnv] at hdec
  have hbs : bytes s.val = (bytes old.val).take p.val := by rw [hsv, bytes_take]
  have hbmo : bytes mo.val = (bytes ro.val).take ((bytes ro.val).length - q.val) := by rw [hmov, bytes_take, bytes_length]
  have hbmn : bytes mn.val = (bytes rn.val).take ((bytes rn.val).length - q.val) := by rw [hmnv, bytes_take, bytes_length]
  have hbs1 : bytes s1.val = (bytes ro.val).drop ((bytes ro.val).length - q.val) := by rw [hs1v, bytes_drop, bytes_length]
  have hbs2 : bytes s2.val = (bytes rn.val).drop ((bytes rn.val).length - q.val) := by rw [hs2v, bytes_drop, bytes_length]
  obtain ⟨hdecO, hdecN⟩ := hdec
  rw [← hbs, ← hbmo, ← hbs1] at hdecO
  rw [← hbs, ← hbmn] at hdecN
  rw [← hbs1] at hdecN
  have hs12 : bytes s2.val = bytes s1.val := by rw [hbs2, hbs1]; exact hq2.symm
  have hlaL : la.val.length = (Myers.lines (bytes mo.val)).length := by
    have := congrArg List.length hla; simpa [sb] using this
  have hlbL : lb.val.length = (Myers.lines (bytes mn.val)).length := by
    have := congrArg List.length hlb; simpa [sb] using this
  have hcapN : la.val.length + lb.val.length ≤ 2 ^ 28 := by
    rw [hlaL, hlbL]
    have e1 := congrArg List.length hdecO
    have e2 := congrArg List.length hdecN
    simp only [List.length_append] at e1 e2
    omega
  step with (hI la.deref lb.deref (by simpa [alloc.vec.Vec.deref] using hcapN)) as ⟨ia, ib, n_ids, hie⟩
  obtain ⟨g, hga, hgb, hginj⟩ := intern_map hie
  have hAm : (la.deref.val.map (fun s => s.val)).map bytes = Myers.lines (bytes mo.val) := by
    rw [← hla]; simp [sb, alloc.vec.Vec.deref, List.map_map, Function.comp_def]
  have hBm : (lb.deref.val.map (fun s => s.val)).map bytes = Myers.lines (bytes mn.val) := by
    rw [← hlb]; simp [sb, alloc.vec.Vec.deref, List.map_map, Function.comp_def]
  rw [hAm] at hga hginj
  rw [hBm] at hgb hginj
  obtain ⟨hl1, hl2, hlt1, hlt2, _⟩ := hie
  have hvA : vals ia.deref.val = (Myers.lines (bytes mo.val)).map g := by
    rw [← hga]; simp [vals, alloc.vec.Vec.deref]
  have hvB : vals ib.deref.val = (Myers.lines (bytes mn.val)).map g := by
    rw [← hgb]; simp [vals, alloc.vec.Vec.deref]
  have hNm : (Myers.lines (bytes mo.val)).length + (Myers.lines (bytes mn.val)).length ≤ NMAX := by
    rw [← hlaL, ← hlbL]; unfold NMAX; exact hcapN
  step with (diff_ids_spec ia.deref ib.deref n_ids _ _ hvA hvB
    (by simpa using hNm)
    (by
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · rw [← hvA] at hx; simp only [vals, List.mem_map] at hx
        obtain ⟨u, hu, rfl⟩ := hx; exact hlt1 u (by simpa [alloc.vec.Vec.deref] using hu)
      · rw [← hvB] at hx; simp only [vals, List.mem_map] at hx
        obtain ⟨u, hu, rfl⟩ := hx; exact hlt2 u (by simpa [alloc.vec.Vec.deref] using hu))) as ⟨da, di, mid, hopt, hmd, hmi⟩
  have hmin := Myers.minL_of_optimal g (Myers.lines (bytes mo.val)) (Myers.lines (bytes mn.val))
    (by intro x hx y hy e; exact hginj x (by simpa using hx) y (by simpa using hy) e) hopt
  have hsufeq : suf_new.val = suf_old.val := by rw [hsn, hso, hs12]
  have hdl := hopt.1
  obtain ⟨hdl1, hdl2, _⟩ := hdl
  simp only [List.length_map] at hdl1 hdl2
  have hLo : (Myers.lines (bytes old.val)).length = pre_lines.val + la.val.length + suf_old.val := by
    have := congrArg List.length hdecO
    simp only [List.length_append] at this
    rw [this, hpl, hlaL, hso]
  have hLn : (Myers.lines (bytes new.val)).length = pre_lines.val + lb.val.length + suf_new.val := by
    have := congrArg List.length hdecN
    simp only [List.length_append] at this
    rw [this, hpl, hlbL, hsn, hs12, ← hso]
  have hcl : core.clone.CloneBool.clone false = ok false := rfl
  have hLoB := lines_length_le (bytes old.val)
  have hLnB := lines_length_le (bytes new.val)
  have holB := Slice.length_ineq old
  have hnwB := Slice.length_ineq new
  simp only [bytes_length] at hLoB hLnB
  step as ⟨i11, hi11⟩
  step as ⟨i12, hi12⟩
  step with (alloc.vec.from_elem_spec core.clone.CloneBool false i12 hcl) as ⟨deleted, hdel1, hdel2⟩
  step as ⟨i14, hi14⟩
  step as ⟨i15, hi15⟩
  step with (alloc.vec.from_elem_spec core.clone.CloneBool false i15 hcl) as ⟨inserted, hins1, hins2⟩
  step as ⟨i17, hi17⟩
  have hlaLen : la.len.val = la.val.length := by simp [alloc.vec.Vec.len]
  have hlbLen : lb.len.val = lb.val.length := by simp [alloc.vec.Vec.len]
  have hdal : mid.deleted.val.length = la.val.length := by rw [hmd, hdl1, hlaL]
  have hdil : mid.inserted.val.length = lb.val.length := by rw [hmi, hdl2, hlbL]
  step as ⟨s5, back1, hs5, hs5l, hback1⟩
  have h5len : s5.length = (alloc.vec.Vec.deref mid.deleted).length := by
    have e : (alloc.vec.Vec.deref mid.deleted).length = mid.deleted.val.length := by simp [alloc.vec.Vec.deref, Slice.length]
    omega
  step with (core.slice.Slice.copy_from_slice.step_spec core.core.marker.CopyBool s5 (alloc.vec.Vec.deref mid.deleted) h5len) as ⟨s7, hs7⟩
  step as ⟨i19, hi19⟩
  step as ⟨s8, back2, hs8, hs8l, hback2⟩
  have h8len : s8.length = (alloc.vec.Vec.deref mid.inserted).length := by
    have e : (alloc.vec.Vec.deref mid.inserted).length = mid.inserted.val.length := by simp [alloc.vec.Vec.deref, Slice.length]
    omega
  step with (core.slice.Slice.copy_from_slice.step_spec core.core.marker.CopyBool s8 (alloc.vec.Vec.deref mid.inserted) h8len) as ⟨s10, hs10⟩
  have hs7v : s7.val = da := by rw [hs7]; simp [alloc.vec.Vec.deref, hmd]
  have hs10v : s10.val = di := by rw [hs10]; simp [alloc.vec.Vec.deref, hmi]
  have hP : pre_lines.val = (Myers.lines (bytes s.val)).length := hpl
  have hdlen : da.length = la.val.length := by rw [hdl1, hlaL]
  have hilen : di.length = lb.val.length := by rw [hdl2, hlbL]
  have hfin1 : (back1 s7).val = List.replicate (Myers.lines (bytes s.val)).length false ++ da ++
      List.replicate (Myers.lines (bytes s1.val)).length false := by
    rw [hback1, ← hP, ← hso]
    have e : (deleted.setSlice! pre_lines.val s7.val).val = deleted.val.setSlice! pre_lines.val s7.val := by cases deleted; simp [alloc.vec.Vec.val, alloc.vec.Vec.setSlice!]
    rw [e, hdel1, hs7v, rep_assemble _ _ _ (by omega)]
    congr 2
    omega
  have hfin2 : (back2 s10).val = List.replicate (Myers.lines (bytes s.val)).length false ++ di ++
      List.replicate (Myers.lines (bytes s1.val)).length false := by
    rw [hback2, ← hP, ← hso, ← hsufeq]
    have e : (inserted.setSlice! pre_lines.val s10.val).val = inserted.val.setSlice! pre_lines.val s10.val := by cases inserted; simp [alloc.vec.Vec.val, alloc.vec.Vec.setSlice!]
    rw [e, hins1, hs10v, rep_assemble _ _ _ (by omega)]
    congr 2
    omega
  have hfull := Myers.minL_trim (Myers.lines (bytes s.val)) _ _ (Myers.lines (bytes s1.val)) hmin
  rw [← hdecO, ← hdecN] at hfull
  refine ⟨_, _, hfin1, hfin2, hfull, ?_⟩
  rw [Myers.applyS_eq _ _ _ _ hfull.1, Myers.lines_flatten]

end difffold_myers_extract
