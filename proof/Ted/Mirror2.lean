import Mirror
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! Structure of the child lists of a well formed tree, and the closed form of the mirror's leftmost leaves. -/

theorem pim_lt_of_anc {la : Nat → Nat} {n : Nat} (hA : WfL la) {u v : Nat} (hu : 1 ≤ u) (huv : u < v)
    (hvn : v ≤ n) (hanc : la v ≤ u) : pim la n u < pim la n v := by
  have := P_anc hA hu huv hvn hanc
  have := pre_le_n hA hu (n := n); have := pre_le_n hA (by omega : 1 ≤ v) hvn
  unfold pim; omega

/-- A node whose child list is empty is a leaf. -/
theorem leaf_la (a : ted.PostTree) (hW : PT.Wf a) {p : Nat} (hp : 1 ≤ p) (hpn : p ≤ a.label.length)
    (h : kdOf a p = []) : laOf a p = p := by
  have hle := (hW.wfl.1 p hp).2
  by_contra hne
  have hlt : laOf a p < p := by omega
  have hmem : p - 1 ∈ kdOf a p := by
    rw [hW.par p (p - 1) hp hpn]
    have hp2 : 2 ≤ p := by have := (hW.wfl.1 p hp).1; omega
    refine ⟨by omega, ⟨by omega, by omega⟩, by omega, fun w hw => ?_⟩
    have := hw.1; omega
  rw [h] at hmem
  simp at hmem

/-- A node with children has the node just before it as its last child. -/
theorem last_kid (a : ted.PostTree) (hW : PT.Wf a) {p : Nat} (hp : 1 ≤ p) (hpn : p ≤ a.label.length)
    (h : kdOf a p ≠ []) : p - 1 ∈ kdOf a p := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ h
  have hpar := ((hW.par p c hp hpn).mp hc).2
  have hlt : laOf a p < p := by
    have := hpar.1.2; have := hpar.1.1
    have : laOf a p ≤ c := hpar.1.2
    omega
  rw [hW.par p (p - 1) hp hpn]
  have hp2 : 2 ≤ p := by have := (hW.wfl.1 p hp).1; omega
  refine ⟨by omega, ⟨by omega, by omega⟩, by omega, fun w hw => ?_⟩
  have := hw.1; omega

/-- The child list of a node with children ends with the node just before it. -/
theorem kids_last (a : ted.PostTree) (hW : PT.Wf a) {p : Nat} (hp : 1 ≤ p) (hpn : p ≤ a.label.length)
    (h : kdOf a p ≠ []) :
    ∃ ks0 m, (a.kids.val[p - 1]!).val = ks0 ++ [m] ∧ m.val + 2 = p := by
  have hlast := last_kid a hW hp hpn h
  have hne : (a.kids.val[p - 1]!).val ≠ [] := by
    intro h0; apply h; unfold kdOf; rw [h0]; rfl
  obtain ⟨ks0, m, hm0⟩ := (List.eq_nil_or_concat (a.kids.val[p - 1]!).val).resolve_left hne
  have hm : (a.kids.val[p - 1]!).val = ks0 ++ [m] := by rw [hm0]; simp
  refine ⟨ks0, m, hm, ?_⟩
  have hs := hW.sorted p hp hpn
  have hmem : m.val + 1 ∈ kdOf a p := by unfold kdOf; rw [hm]; simp
  have hlt := ((hW.par p _ hp hpn).mp hmem).2.1.1
  have hsorted := hs
  unfold kdOf at hsorted hlast
  rw [hm] at hsorted hlast
  simp only [List.map_append, List.map_cons, List.map_nil] at hsorted hlast
  rw [List.pairwise_append] at hsorted
  rw [List.mem_append] at hlast
  rcases hlast with h1 | h1
  · have := hsorted.2.2 (p - 1) h1 (m.val + 1) (by simp)
    omega
  · simp at h1; omega

theorem mirror_closed (a : ted.PostTree) (hW : PT.Wf a) (pos : List Std.Usize) (L : List Std.U32)
    (K : List (alloc.vec.Vec Std.U32))
    (hP : ∀ y < a.label.length, (pos[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
    (hKl : K.length = a.label.length) (hLl : L.length = a.label.length)
    (hK : ∀ y < a.label.length, ((K[(pos[y]!).val]!).val.map (fun k => k.val)) = revPos (a.kids.val[y]!).val pos 0)
    (hL : ∀ z < a.label.length, LmlEq K L z) :
    ∀ x, 1 ≤ x → x ≤ a.label.length →
      (L[(pos[x - 1]!).val]!).val = a.label.length + 1 - Qp (laOf a) a.label.length x := by
  intro x
  induction x with
  | zero => intro h; omega
  | succ x ih =>
    intro _ hxn
    have hxn' : x < a.label.length := by omega
    have hz := pos_lt a hW pos hP hxn'
    simp only [Nat.add_sub_cancel]
    have hLE := hL _ hz
    have hKz : (pos[x]!).val < K.length := by omega
    unfold LmlEq at hLE
    rw [firstKid_get K _ hKz] at hLE
    have hKm := hK x hxn'
    rw [getG_eq _ _ hKz] at hKm
    have hpre : pim (laOf a) a.label.length (x + 1) = a.label.length + 1 - pre (laOf a) a.label.length (x + 1) := rfl
    by_cases hkd : kdOf a (x + 1) = []
    · have hks : (a.kids.val[x]!).val = [] := by
        unfold kdOf at hkd
        simp only [Nat.add_sub_cancel] at hkd
        exact List.map_eq_nil_iff.mp hkd
      rw [hks] at hKm
      simp only [revPos, List.drop_nil, List.reverse_nil, List.map_nil] at hKm
      have hnil : (K[(pos[x]!).val]'hKz).val = [] := List.map_eq_nil_iff.mp hKm
      rw [hnil] at hLE
      simp only [List.head?_nil] at hLE
      have hla := leaf_la a hW (p := x + 1) (by omega) hxn hkd
      have h1 := hP x hxn'
      have h2 : Qp (laOf a) a.label.length (x + 1) = pre (laOf a) a.label.length (x + 1) := by
        unfold Qp pre; rw [hla]
      rw [hLE, h2]; omega
    · obtain ⟨ks0, m, hm, hm2⟩ := kids_last a hW (p := x + 1) (by omega) hxn hkd
      simp only [Nat.add_sub_cancel] at hm
      rw [hm] at hKm
      simp only [revPos, List.drop_zero, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, List.map_cons] at hKm
      obtain ⟨k, rest, hkr, hk1, _⟩ := List.map_eq_cons_iff.mp hKm
      rw [hkr] at hLE
      simp only [List.head?_cons] at hLE
      have hx1 : 1 ≤ x := by omega
      have hmx : m.val = x - 1 := by omega
      have ih' := ih hx1 (by omega)
      have hkp : k.val = (pos[x - 1]!).val := by rw [hk1, hmx]
      have hlast := last_kid a hW (p := x + 1) (by omega) hxn hkd
      simp only [Nat.add_sub_cancel] at hlast
      have hpar := ((hW.par (x + 1) x (by omega) hxn).mp hlast).2
      have hdep := dep_par hW.wfl (n := a.label.length) hx1 hpar
      rw [hLE, hkp, ih']
      unfold Qp; omega
  
theorem laOf_eq1 (a : ted.PostTree) (u : Nat) (h1 : 1 ≤ u) (h2 : u ≤ a.label.length) :
    laOf a u = (a.lml.val[u - 1]!).val := by
  unfold laOf; rw [if_pos ⟨h1, h2⟩]

theorem pim_pos_eq (a : ted.PostTree) (pos : List Std.Usize)
    (hP : ∀ y < a.label.length, (pos[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
    {x : Nat} (hx : 1 ≤ x) (hxn : x ≤ a.label.length) :
    pim (laOf a) a.label.length x - 1 = (pos[x - 1]!).val := by
  have := hP (x - 1) (by omega)
  have e : x - 1 + 1 = x := by omega
  rw [e] at this; omega

/-- Siblings are carried to siblings in reverse order. -/
theorem pim_sibling (a : ted.PostTree) (hW : PT.Wf a) {p c c' : Nat} (hp : 1 ≤ p) (hpn : p ≤ a.label.length)
    (hc : c ∈ kdOf a p) (hc' : c' ∈ kdOf a p) (hlt : c < c') :
    pim (laOf a) a.label.length c' < pim (laOf a) a.label.length c := by
  have h1 := ((hW.par p c hp hpn).mp hc)
  have h2 := ((hW.par p c' hp hpn).mp hc')
  have hcn : c ≤ a.label.length := by have := h1.2.2.1; have := h1.2.1.1; omega
  have hc'n : c' ≤ a.label.length := by have := h2.2.2.1; have := h2.2.1.1; omega
  -- `c` is not below `c'`, since the parent of `c` is `p`, not `c'`.
  have hna : ¬ laOf a c' ≤ c := by
    intro hh
    have := h1.2.2.2 c' ⟨hlt, hh⟩
    have := h2.2.1.1
    omega
  have := P_un hW.wfl (n := a.label.length) h1.1 hlt hc'n (by omega)
  have := pre_le_Qp hW.wfl (n := a.label.length) h1.1
  have := pre_le_n hW.wfl (n := a.label.length) h1.1 hcn
  have := pre_le_n hW.wfl (n := a.label.length) (by omega : 1 ≤ c') hc'n
  unfold pim; omega

theorem kdOf_mirror (a r : ted.PostTree) (hW : PT.Wf a) (pos : List Std.Usize)
    (hP : ∀ y < a.label.length, (pos[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
    (hF : ∀ y < a.label.length, ((r.kids.val[(pos[y]!).val]!).val.map (fun k => k.val)) =
      revPos (a.kids.val[y]!).val pos 0)
    {p : Nat} (hp : 1 ≤ p) (hpn : p ≤ a.label.length) :
    kdOf r (pim (laOf a) a.label.length p) = ((kdOf a p).reverse).map (pim (laOf a) a.label.length) := by
  unfold kdOf
  rw [pim_pos_eq a pos hP hp hpn]
  have h := hF (p - 1) (by omega)
  have hk : ∀ k ∈ (a.kids.val[p - 1]!).val, k.val + 1 < p := by
    intro k hk
    obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hk
    have := kid_lt a hW p hp hpn i hi
    rw [getG_eq _ _ hi, hik] at this
    exact this
  rw [← List.map_reverse, List.map_map, List.map_reverse]
  have h1 : ((r.kids.val[(pos[p - 1]!).val]!).val.map (fun c => c.val + 1)) =
      ((r.kids.val[(pos[p - 1]!).val]!).val.map (fun k => k.val)).map (fun c => c + 1) := by
    rw [List.map_map]; rfl
  rw [h1, h]
  simp only [revPos, List.drop_zero, List.map_map, List.map_reverse]
  congr 1
  apply List.map_congr_left
  intro k hk'
  have := hP k.val (by have := hk k hk'; omega)
  simp only [Function.comp]
  omega

theorem mirror_wf (a r : ted.PostTree) (hW : PT.Wf a) (hn : a.label.length < 2 ^ 14) (pos : List Std.Usize)
    (hP : ∀ y < a.label.length, (pos[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
    (hrl : r.label.length = a.label.length) (hr2 : r.lml.length = a.label.length)
    (hr3 : r.kind.length = a.label.length) (hr4 : r.kids.length = a.label.length)
    (hF : ∀ y < a.label.length, ((r.kids.val[(pos[y]!).val]!).val.map (fun k => k.val)) =
      revPos (a.kids.val[y]!).val pos 0)
    (hLm : ∀ z < a.label.length, LmlEq r.kids.val r.lml.val z)
    (hkrs : r.keyroots.val.Pairwise (fun x y => x.val < y.val))
    (hkrt : ∀ v, InKR r.keyroots.val v ↔ LastWithLml r.lml.val a.label.length v) :
    PT.Wf r ∧ ∀ x, 1 ≤ x → x ≤ a.label.length →
      laOf r (pim (laOf a) a.label.length x) = a.label.length + 1 - Qp (laOf a) a.label.length x := by
  have hcl := mirror_closed a hW pos r.lml.val r.kids.val hP (by exact hr4) (by exact hr2) hF hLm
  have hlam : ∀ x, 1 ≤ x → x ≤ a.label.length →
      laOf r (pim (laOf a) a.label.length x) = a.label.length + 1 - Qp (laOf a) a.label.length x := by
    intro x hx hxn
    have hm := pim_mem hW.wfl (n := a.label.length) hx hxn
    rw [laOf_eq1 r _ hm.1 (by omega), pim_pos_eq a pos hP hx hxn]
    exact hcl x hx hxn
  have hbig : ∀ u, a.label.length < u → laOf r u = u := by
    intro u hu; unfold laOf; rw [hrl, if_neg (by omega)]
  have hwfl := wfl_mirror hW.wfl hlam hbig
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hlam⟩
  · rw [hrl]; exact hW.pos
  · rw [hrl]; exact hr2
  · rw [hrl]; exact hr3
  · rw [hrl]; exact hr4
  · exact hwfl
  · -- the last node is the root
    rw [hrl]
    have hn1 := hW.pos
    have h := hlam a.label.length hn1 (Nat.le_refl _)
    have hdep : dep (laOf a) a.label.length a.label.length = 0 := by unfold dep; simp [cn]
    have hpre : pim (laOf a) a.label.length a.label.length = a.label.length := by
      unfold pim pre; rw [hdep, hW.root]; omega
    rw [hpre] at h
    rw [h]; unfold Qp; rw [hdep]; omega
  · intro p' hp1 hp2
    rw [hrl] at hp2
    obtain ⟨p, hp1', hp2', rfl⟩ := pim_surj hW.wfl (n := a.label.length) hp1 hp2
    rw [kdOf_mirror a r hW pos hP hF hp1' hp2']
    have hs := hW.sorted p hp1' hp2'
    rw [List.pairwise_map, List.pairwise_reverse]
    refine hs.imp_of_mem (fun {c c'} hc hc' hlt => ?_)
    exact pim_sibling a hW hp1' hp2' hc hc' hlt
  · intro p' c' hp1 hp2
    rw [hrl] at hp2
    obtain ⟨p, hp1', hp2', rfl⟩ := pim_surj hW.wfl (n := a.label.length) hp1 hp2
    rw [kdOf_mirror a r hW pos hP hF hp1' hp2', List.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [List.mem_reverse] at hc
      have hpc := (hW.par p c hp1' hp2').mp hc
      have hcn : c ≤ a.label.length := by have := hpc.2.2.1; have := hpc.2.1.1; omega
      have hm := pim_mem hW.wfl hpc.1 hcn
      refine ⟨hm.1, ?_⟩
      rw [hrl]
      exact (par_mirror hW.wfl hlam hbig hpc.1 hcn hp1' hp2').mpr hpc.2
    · rintro ⟨hc1, hpar⟩
      rw [hrl] at hpar
      have hc'n : c' ≤ a.label.length := by
        have := hpar.1.1
        have := (pim_mem hW.wfl hp1' hp2').2
        omega
      obtain ⟨c, hc1', hcn, rfl⟩ := pim_surj hW.wfl (n := a.label.length) hc1 hc'n
      have hpc := (par_mirror hW.wfl hlam hbig hc1' hcn hp1' hp2').mp hpar
      refine ⟨c, ?_, rfl⟩
      rw [List.mem_reverse]
      exact (hW.par p c hp1' hp2').mpr ⟨hc1', hpc⟩
  · exact hkrs
  · rw [hrl]; exact hkrt

/-- What the mirror image of `a` looks like. -/
structure MirrorOf (a r : ted.PostTree) : Prop where
  n1 : r.label.length = a.label.length
  lab : ∀ x, 1 ≤ x → x ≤ a.label.length →
    r.label.val[pim (laOf a) a.label.length x - 1]! = a.label.val[x - 1]!
  knd : ∀ x, 1 ≤ x → x ≤ a.label.length →
    r.kind.val[pim (laOf a) a.label.length x - 1]! = a.kind.val[x - 1]!
  lam : ∀ x, 1 ≤ x → x ≤ a.label.length →
    laOf r (pim (laOf a) a.label.length x) = a.label.length + 1 - Qp (laOf a) a.label.length x

/-- The first element of a mirrored child list is the position of the node just before its parent. -/
theorem firstKid_mirror (a : ted.PostTree) (hW : PT.Wf a) (pos : List Std.Usize)
    (K : List (alloc.vec.Vec Std.U32))
    (hP : ∀ y < a.label.length, (pos[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
    (hKl : K.length = a.label.length)
    (hF : ∀ y < a.label.length, ((K[(pos[y]!).val]!).val.map (fun k => k.val)) =
      revPos (a.kids.val[y]!).val pos 0)
    {x : Nat} (hx : 1 ≤ x) (hxn : x ≤ a.label.length) (k : Std.U32)
    (hk : FirstKid K (pos[x - 1]!).val = some k) :
    kdOf a x ≠ [] ∧ k.val + 1 = pim (laOf a) a.label.length (x - 1) ∧ 2 ≤ x := by
  have hz := pos_lt a hW pos hP (y := x - 1) (by omega)
  have hKz : (pos[x - 1]!).val < K.length := by omega
  rw [firstKid_get K _ hKz] at hk
  have hKm := hF (x - 1) (by omega)
  rw [getG_eq _ _ hKz] at hKm
  by_cases hkd : kdOf a x = []
  · exfalso
    have hks : (a.kids.val[x - 1]!).val = [] := by
      unfold kdOf at hkd
      exact List.map_eq_nil_iff.mp hkd
    rw [hks] at hKm
    simp only [revPos, List.drop_nil, List.reverse_nil, List.map_nil] at hKm
    have hnil : (K[(pos[x - 1]!).val]'hKz).val = [] := List.map_eq_nil_iff.mp hKm
    rw [hnil] at hk
    simp at hk
  · obtain ⟨ks0, m, hm, hm2⟩ := kids_last a hW hx hxn hkd
    rw [hm] at hKm
    simp only [revPos, List.drop_zero, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.map_cons] at hKm
    obtain ⟨k0, rest, hkr, hk1, _⟩ := List.map_eq_cons_iff.mp hKm
    rw [hkr] at hk
    simp only [List.head?_cons, Option.some.injEq] at hk
    subst hk
    refine ⟨hkd, ?_, by omega⟩
    rw [hk1]
    have := hP m.val (by omega)
    have e : m.val + 1 = x - 1 := by omega
    rw [e] at this
    exact this

theorem mirror_spec (a : ted.PostTree) (hW : PT.Wf a) (hn : a.label.length < 2 ^ 14) :
    ted.PostTree.mirror a ⦃ r => PT.Wf r ∧ MirrorOf a r ⦄ := by
  unfold ted.PostTree.mirror
  have hlenv := alloc.vec.Vec.len_val a.label
  have hnb := (alloc.vec.Vec.len a.label).hBounds
  simp only [lift, bind_tc_ok]
  by_cases h0 : alloc.vec.Vec.len a.label = 0#usize
  · exfalso
    have := hW.pos
    have : (alloc.vec.Vec.len a.label).val = 0 := by rw [h0]; rfl
    omega
  · rw [if_neg h0]
    have hn31 : a.label.length < 2 ^ 31 := by omega
    have hal : a.label.val.length = a.label.length := rfl
    have hkv : a.kids.length = a.label.length := hW.n4
    step as ⟨depth, hdepth, hdl⟩
    have hJ0 : DepthInv a (alloc.vec.Vec.len a.label).val depth.val := by
      intro c hc1 hcn hprem
      rcases hprem with h | ⟨q, hq1, hq2, _⟩
      · have hdl' : depth.val.length = a.label.length := by rw [← hlenv]; exact hdl
        rw [hdepth, getG_eq _ _ (by simp; omega)]
        have hdep : dep (laOf a) a.label.length c = 0 := by rw [h]; unfold dep; simp [cn]
        rw [hdep]
        simp
      · omega
    refine WP.spec_bind (mirror_depth_spec a hW depth a.label.len (by omega) (by rw [hdl]; exact hlenv) hJ0) ?_
    rintro depth1 ⟨hl1, hJ1⟩
    have hD : ∀ c, 1 ≤ c → c ≤ a.label.length → (depth1.val[c - 1]!).val = dep (laOf a) a.label.length c := by
      intro c hc1 hcn
      apply hJ1 c hc1 hcn
      by_cases hcn' : c = a.label.length
      · exact Or.inl hcn'
      · obtain ⟨q, hq⟩ := par_exists hW.wfl hW.root (c := c) hc1 (by omega)
        exact Or.inr ⟨q, by have := hq.1.1; omega, hq.2.1, hq⟩
    step as ⟨pos, hpos, hpl0⟩
    refine WP.spec_bind (mirror_pos_spec a hW a.label.len depth1 pos 0#usize hlenv (by simp) hl1
      (by rw [hpl0]; exact hlenv) hD (by simp)) ?_
    rintro pos1 ⟨hpl, hP⟩
    step as ⟨label, hlabel, hll⟩
    step as ⟨kids, hkids, hkl⟩
    · exact clone_vec_u32 _
    have hll' : label.length = a.label.length := by rw [hll]; exact hlenv
    have hkl' : kids.length = a.label.length := by rw [hkl]; exact hlenv
    refine WP.spec_bind (mirror_fill_spec a hW a.label.len pos1 0#usize label label kids hlenv hn31 hpl hP hll'
      hll' hkl' (by simp) (by intro y hy; simp at hy)) ?_
    rintro ⟨label1, kind, kids1⟩ ⟨hl1', hk1', hkd1, hF⟩
    dsimp only at hl1' hk1' hkd1 hF ⊢
    have hderef : (alloc.vec.Vec.deref kids1).val = kids1.val := by
      unfold alloc.vec.Vec.deref
      rw [Slice.from_val]; rfl
    have hF3 : ∀ y < a.label.length, ((kids1.val[(pos1.val[y]!).val]!).val.map (fun k => k.val)) =
        revPos (a.kids.val[y]!).val pos1.val 0 := fun y hy => (hF y hy).2.2
    have hvalid : ∀ j < label1.length, ∀ k, FirstKid (alloc.vec.Vec.deref kids1).val j = some k → k.val < j := by
      intro j hj k hk
      rw [hderef] at hk
      obtain ⟨x, hx1, hx2, hx3⟩ := pim_surj hW.wfl (n := a.label.length) (y := j + 1) (by omega) (by omega)
      have hjx : j = (pos1.val[x - 1]!).val := by
        have := pim_pos_eq a pos1.val hP hx1 hx2; omega
      rw [hjx] at hk ⊢
      have hkl2 : kids1.val.length = a.label.length := hkd1
      have hf := firstKid_mirror a hW pos1.val kids1.val hP hkl2 hF3 hx1 hx2 k hk
      have hlast := last_kid a hW (p := x) hx1 hx2 hf.1
      have hpar := ((hW.par x (x - 1) hx1 hx2).mp hlast).2
      have hlt := pim_lt_of_anc hW.wfl (n := a.label.length) (by omega) (by have := hpar.1.1; exact this)
        hx2 hpar.1.2
      have h1 := hP (x - 1) (by omega)
      have e : x - 1 + 1 = x := by omega
      rw [e] at h1
      omega
    refine WP.spec_bind (from_kids_spec label1 (alloc.vec.Vec.deref kids1) (by omega)
      (by rw [hderef]; have : kids1.val.length = a.label.length := hkd1; omega) hvalid) ?_
    rintro pt ⟨hpl1, hplen, hlml, hsorted, hkrt, hkids, hkind⟩
    unfold ted.PostTree.with_kinds
    have hlenEq : alloc.vec.Vec.len kind = alloc.vec.Vec.len pt.label := by
      apply UScalar.eq_of_val_eq
      rw [alloc.vec.Vec.len_val, alloc.vec.Vec.len_val, hpl1]
      exact hk1'.trans hl1'.symm
    simp only [hlenEq, ↓reduceIte, WP.spec_ok]
    sorry

end difffold_lines_extract
