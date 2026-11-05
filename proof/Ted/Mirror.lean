import Wf
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The real `PostTree::mirror`: depth array, new positions, and the three rebuilt arrays. -/

theorem getG_set_eq {α : Type} [Inhabited α] (l : List α) (i : Nat) (x : α) (h : i < l.length) :
    (l.set i x)[i]! = x := by simp [h]

theorem getG_set_ne {α : Type} [Inhabited α] (l : List α) (i j : Nat) (x : α) (h : j ≠ i) :
    (l.set i x)[j]! = l[j]! := by simp [Ne.symm h]

theorem getG_eq {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[i]! = l[i]'h := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- After the nodes `P+1 .. n` have been handled, every node whose parent is above `P` (and the root) has its depth. -/
def DepthInv (a : ted.PostTree) (P : Nat) (d : List Std.Usize) : Prop :=
  ∀ c, 1 ≤ c → c ≤ a.label.length →
    (c = a.label.length ∨ ∃ q, P < q ∧ q ≤ a.label.length ∧ Par (laOf a) a.label.length c q) →
    (d[c - 1]!).val = dep (laOf a) a.label.length c

theorem kd_mem (a : ted.PostTree) (p i : Nat) (h : i < (a.kids.val[p - 1]!).val.length) :
    ((a.kids.val[p - 1]!).val[i]!).val + 1 ∈ kdOf a p := by
  unfold kdOf
  rw [List.mem_map]
  exact ⟨(a.kids.val[p - 1]!).val[i]!, by
    rw [getG_eq _ _ h]
    exact List.getElem_mem h, rfl⟩

theorem kd_lt (a : ted.PostTree) (hW : PT.Wf a) (P : Nat) (hP1 : 1 ≤ P) (hPn : P ≤ a.label.length)
    (i j : Nat) (hi : i < (a.kids.val[P - 1]!).val.length) (hj : j < (a.kids.val[P - 1]!).val.length) (hij : i < j) :
    ((a.kids.val[P - 1]!).val[i]!).val < ((a.kids.val[P - 1]!).val[j]!).val := by
  have h := hW.sorted P hP1 hPn
  unfold kdOf at h
  rw [List.pairwise_map, List.pairwise_iff_getElem] at h
  have := h i j (by simpa using hi) (by simpa using hj) hij
  rw [getG_eq _ _ hi, getG_eq _ _ hj]
  omega

theorem mirror_inner_spec (a : ted.PostTree) (hW : PT.Wf a) (pp d j : Std.Usize) (depth : alloc.vec.Vec Std.Usize)
    (P : Nat) (hpp : pp.val + 1 = P) (hP1 : 1 ≤ P) (hPn : P ≤ a.label.length)
    (hd : d.val = dep (laOf a) a.label.length P + 1) (hlen : depth.length = a.label.length)
    (hj : j.val ≤ (a.kids.val[pp.val]!).val.length) (hJ : DepthInv a P depth.val)
    (hK : ∀ i < j.val, (depth.val[((a.kids.val[pp.val]!).val[i]!).val]!).val =
      dep (laOf a) a.label.length (((a.kids.val[pp.val]!).val[i]!).val + 1)) :
    ted.PostTree.mirror_loop0_loop0 a.kids depth pp d j ⦃ r =>
      r.length = a.label.length ∧ DepthInv a (P - 1) r.val ⦄ := by
  unfold ted.PostTree.mirror_loop0_loop0
  have hkv : a.kids.val.length = a.label.length := hW.n4
  have hppn : pp.val < a.kids.val.length := by omega
  have hkp : a.kids.val[pp.val]! = a.kids.val[P - 1]! := by
    have : pp.val = P - 1 := by omega
    rw [this]
  apply loop.spec_decr_nat
    (measure := fun s => (a.kids.val[pp.val]!).val.length - s.2.val)
    (inv := fun s => s.2.val ≤ (a.kids.val[pp.val]!).val.length ∧ s.1.length = a.label.length ∧
      DepthInv a P s.1.val ∧
      ∀ i < s.2.val, (s.1.val[((a.kids.val[pp.val]!).val[i]!).val]!).val =
        dep (laOf a) a.label.length (((a.kids.val[pp.val]!).val[i]!).val + 1))
  · intro s hs
    obtain ⟨depth1, j1⟩ := s
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    dsimp only at hs1 hs2 hs3 hs4 ⊢
    unfold ted.PostTree.mirror_loop0_loop0.body
    step as ⟨v1, hv1⟩
    have hv1' : v1 = a.kids.val[pp.val]! := by rw [hv1, getG_eq _ _ hppn]
    have hlen1 : v1.len.val = (a.kids.val[pp.val]!).val.length := by
      rw [alloc.vec.Vec.len_val, hv1']
    by_cases hjl : j1 < v1.len
    · rw [if_pos hjl]
      have hjl' : j1.val < (a.kids.val[pp.val]!).val.length := by
        have : j1.val < v1.len.val := hjl
        omega
      step as ⟨i1, hi1⟩
      have hi1' : i1 = (a.kids.val[pp.val]!).val[j1.val]! := by
        rw [hi1, ← hv1', getG_eq _ _ (by rw [← hv1'] at hjl'; exact hjl')]
      have hmem := kd_mem a P j1.val (by rw [← hkp]; exact hjl')
      rw [← hkp] at hmem
      have hpar := (hW.par P ((a.kids.val[pp.val]!).val[j1.val]!).val.succ hP1 hPn).mp
      have hP2 := hpar hmem
      have hlt : i1.val + 1 < P := by rw [hi1']; exact hP2.2.1.1
      have hi2 : (UScalar.cast .Usize i1).val = i1.val := U32.cast_Usize_val_eq i1
      simp only [lift, bind_tc_ok]
      step as ⟨old, imb, ho, himb⟩
      have hset : (imb d).val = depth1.val.set i1.val d := by
        rw [himb, alloc.vec.Vec.set_val_eq, hi2]
      step as ⟨j2, hj2⟩
      have hd1 : depth1.val.length = a.label.length := hs2
      have hkid_eq : ((a.kids.val[pp.val]!).val[j1.val]!).val = i1.val := by rw [hi1']
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hd1
      · intro c hc1 hcn hprem
        rw [hset]
        by_cases hce : c - 1 = i1.val
        · exfalso
          rcases hprem with h | ⟨q, hq1, hq2, hq3⟩
          · omega
          · have hpc : Par (laOf a) a.label.length c P := by
              have : c = i1.val + 1 := by omega
              rw [this, hi1']; exact hP2.2
            have := par_unique hq3 hpc
            omega
        · rw [getG_set_ne _ _ _ _ hce]
          exact hs3 c hc1 hcn hprem
      · intro i hi
        have hii : i < j1.val ∨ i = j1.val := by omega
        rw [hset]
        rcases hii with hi' | rfl
        · have hlt2 := kd_lt a hW P hP1 hPn i j1.val (by rw [← hkp]; omega) (by rw [← hkp]; exact hjl') hi'
          have hlt2' : ((a.kids.val[pp.val]!).val[i]!).val < ((a.kids.val[pp.val]!).val[j1.val]!).val := by
            rw [hkp]; exact hlt2
          rw [getG_set_ne _ _ _ _ (by intro h; rw [← hkid_eq] at h; omega)]
          exact hs4 i hi'
        · rw [hkid_eq, getG_set_eq _ _ _ (by omega)]
          rw [hd]
          have := dep_par hW.wfl (n := a.label.length) (c := i1.val + 1) (p := P) (by omega)
            (by rw [hi1']; exact hP2.2)
          omega
    · rw [if_neg hjl]
      simp only [WP.spec_ok]
      have hjeq : j1.val = (a.kids.val[pp.val]!).val.length := by
        have : ¬ j1.val < v1.len.val := hjl
        omega
      refine ⟨hs2, ?_⟩
      intro c hc1 hcn hprem
      rcases hprem with h | ⟨q, hq1, hq2, hq3⟩
      · exact hs3 c hc1 hcn (Or.inl h)
      · by_cases hqP : P < q
        · exact hs3 c hc1 hcn (Or.inr ⟨q, hqP, hq2, hq3⟩)
        · have hqe : q = P := by omega
          subst hqe
          have hmem : c ∈ kdOf a q := (hW.par q c hP1 hPn).mpr ⟨hc1, hq3⟩
          unfold kdOf at hmem
          rw [List.mem_map] at hmem
          obtain ⟨k, hk, hkc⟩ := hmem
          obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hk
          have hi' : i < (a.kids.val[pp.val]!).val.length := by rw [hkp]; exact hi
          have h4 := hs4 i (by omega)
          have hik' : (a.kids.val[q - 1]!).val[i]! = k := by rw [getG_eq _ _ hi]; exact hik
          rw [← hkp] at hik'
          have hkk : ((a.kids.val[pp.val]!).val[i]!).val = k.val := by rw [hik']
          rw [hkk] at h4
          have hc : c - 1 = k.val := by omega
          rw [hc, h4]
          have : c = k.val + 1 := by omega
          rw [this]
  · exact ⟨hj, hlen, hJ, hK⟩

theorem mirror_depth_spec (a : ted.PostTree) (hW : PT.Wf a) (depth : alloc.vec.Vec Std.Usize) (p : Std.Usize)
    (hp : p.val ≤ a.label.length) (hlen : depth.length = a.label.length) (hJ : DepthInv a p.val depth.val) :
    ted.PostTree.mirror_loop0 a.kids depth p ⦃ r => r.length = a.label.length ∧ DepthInv a 0 r.val ⦄ := by
  unfold ted.PostTree.mirror_loop0
  apply loop.spec_decr_nat
    (measure := fun s => s.2.val)
    (inv := fun s => s.2.val ≤ a.label.length ∧ s.1.length = a.label.length ∧ DepthInv a s.2.val s.1.val)
  · intro s hs
    obtain ⟨depth1, p1⟩ := s
    obtain ⟨hs1, hs2, hs3⟩ := hs
    dsimp only at hs1 hs2 hs3 ⊢
    unfold ted.PostTree.mirror_loop0.body
    by_cases hp0 : p1 > 0#usize
    · rw [if_pos hp0]
      have hp0' : 0 < p1.val := hp0
      step as ⟨p2, hp2⟩
      have hd1 : depth1.val.length = a.label.length := hs2
      have hdep : (depth1.val[p2.val]!).val = dep (laOf a) a.label.length p1.val := by
        have := hs3 p1.val (by omega) hs1 (by
          by_cases hpn : p1.val = a.label.length
          · exact Or.inl hpn
          · obtain ⟨q, hq⟩ := par_exists hW.wfl hW.root (c := p1.val) (by omega) (by omega)
            exact Or.inr ⟨q, hq.1.1, hq.2.1, hq⟩)
        have e : p1.val - 1 = p2.val := by omega
        rw [e] at this; exact this
      step as ⟨i, hi⟩
      have hi' : i.val = (depth1.val[p2.val]!).val := by
        rw [hi, getG_eq _ _ (by omega)]
      have hdle := dep_le (la := laOf a) (n := a.label.length) p1.val
      step as ⟨d, hd⟩
      have hnb := (alloc.vec.Vec.len a.label).hBounds
      have hlv := alloc.vec.Vec.len_val a.label
      have hdv : d.val = dep (laOf a) a.label.length p1.val + 1 := by omega
      refine WP.spec_bind (mirror_inner_spec a hW p2 d 0#usize depth1 p1.val (by omega) (by omega) hs1 hdv hd1
        (by simp) hs3 (by intro i hi; exact absurd hi (by simp))) ?_
      rintro depth2 ⟨hl2, hJ2⟩
      simp only [WP.spec_ok]
      refine ⟨by omega, hl2, ?_, by omega⟩
      have e : p1.val - 1 = p2.val := by omega
      rw [← e]; exact hJ2
    · rw [if_neg hp0]
      simp only [WP.spec_ok]
      have : p1.val = 0 := by scalar_tac
      refine ⟨hs2, ?_⟩
      rw [this] at hs3; exact hs3
  · exact ⟨hp, hlen, hJ⟩

theorem laOf_eq (a : ted.PostTree) (x : Nat) (hx : x < a.label.length) :
    laOf a (x + 1) = (a.lml.val[x]!).val := by
  unfold laOf
  rw [if_pos ⟨by omega, by omega⟩]
  simp

theorem mirror_pos_spec (a : ted.PostTree) (hW : PT.Wf a) (n : Std.Usize) (depth pos : alloc.vec.Vec Std.Usize)
    (x : Std.Usize) (hn : n.val = a.label.length) (hx : x.val ≤ a.label.length)
    (hdl : depth.length = a.label.length) (hpl : pos.length = a.label.length)
    (hD : ∀ c, 1 ≤ c → c ≤ a.label.length → (depth.val[c - 1]!).val = dep (laOf a) a.label.length c)
    (hP : ∀ y < x.val, (pos.val[y]!).val + 1 = pim (laOf a) a.label.length (y + 1)) :
    ted.PostTree.mirror_loop1 a.lml n depth pos x ⦃ r =>
      r.length = a.label.length ∧ ∀ y < a.label.length, (r.val[y]!).val + 1 = pim (laOf a) a.label.length (y + 1) ⦄ := by
  unfold ted.PostTree.mirror_loop1
  apply loop.spec_decr_nat
    (measure := fun s => a.label.length - s.2.val)
    (inv := fun s => s.2.val ≤ a.label.length ∧ s.1.length = a.label.length ∧
      ∀ y < s.2.val, (s.1.val[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
  · intro s hs
    obtain ⟨pos1, x1⟩ := s
    obtain ⟨hs1, hs2, hs3⟩ := hs
    dsimp only at hs1 hs2 hs3 ⊢
    unfold ted.PostTree.mirror_loop1.body
    by_cases hxn : x1 < n
    · rw [if_pos hxn]
      have hxn' : x1.val < a.label.length := by have : x1.val < n.val := hxn; omega
      have hlml : a.lml.val.length = a.label.length := hW.n2
      step as ⟨i, hi⟩
      have hi' : i.val = laOf a (x1.val + 1) := by
        rw [laOf_eq a _ hxn', hi, getG_eq _ _ (by omega)]
      step as ⟨l, hl⟩
      have hl' : l.val = laOf a (x1.val + 1) := by rw [hl]; rw [U32.cast_Usize_val_eq]; exact hi'
      step as ⟨d, hd⟩
      have hdl' : depth.val.length = a.label.length := hdl
      have hd' : d.val = dep (laOf a) a.label.length (x1.val + 1) := by
        rw [hd]
        have := hD (x1.val + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at this
        rw [← this, getG_eq _ _ (by omega)]
      have hpre := pre_le_n hW.wfl (n := a.label.length) (u := x1.val + 1) (by omega) (by omega)
      unfold pre at hpre
      step as ⟨q, hq⟩
      step as ⟨v1, hv1⟩
      step as ⟨old, imb, ho, himb⟩
      have hset : (imb v1).val = pos1.val.set x1.val v1 := by
        rw [himb, alloc.vec.Vec.set_val_eq]
      step as ⟨x2, hx2⟩
      have hpim : pim (laOf a) a.label.length (x1.val + 1) = a.label.length + 1 - pre (laOf a) a.label.length (x1.val + 1) := rfl
      have hpos1 := pos1.val.length
      refine ⟨by omega, ?_, ?_, by omega⟩
      · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hs2
      · intro y hy
        rw [hset]
        by_cases hyx : y = x1.val
        · subst hyx
          rw [getG_set_eq _ _ _ (by have : pos1.val.length = a.label.length := hs2; omega), hpim]
          unfold pre; omega
        · rw [getG_set_ne _ _ _ _ hyx]
          exact hs3 y (by omega)
    · rw [if_neg hxn]
      simp only [WP.spec_ok]
      have : x1.val = a.label.length := by
        have : ¬ x1.val < n.val := hxn
        omega
      refine ⟨hs2, ?_⟩
      intro y hy
      exact hs3 y (by omega)
  · exact ⟨hx, hpl, hP⟩

theorem kid_lt (a : ted.PostTree) (hW : PT.Wf a) (P : Nat) (hP1 : 1 ≤ P) (hPn : P ≤ a.label.length)
    (i : Nat) (hi : i < (a.kids.val[P - 1]!).val.length) :
    ((a.kids.val[P - 1]!).val[i]!).val + 1 < P := by
  have hmem := kd_mem a P i hi
  exact ((hW.par P _ hP1 hPn).mp hmem).2.1.1

/-- The reversed list of new positions of the children, built from the back. -/
def revPos (kids : List Std.U32) (pos : List Std.Usize) (j : Nat) : List Nat :=
  ((kids.drop j).reverse).map (fun k => (pos[k.val]!).val)

theorem mirror_kids_spec (a : ted.PostTree) (hW : PT.Wf a) (pos : alloc.vec.Vec Std.Usize) (x : Std.Usize)
    (ks : alloc.vec.Vec Std.U32) (j : Std.Usize) (hn31 : a.label.length < 2 ^ 31)
    (hx : x.val < a.label.length) (hpl : pos.length = a.label.length)
    (hj : j.val ≤ (a.kids.val[x.val]!).val.length)
    (hks : ks.val.map (fun k => k.val) = revPos (a.kids.val[x.val]!).val pos.val j.val)
    (hpv : ∀ y < a.label.length, (pos.val[y]!).val + 1 ≤ a.label.length) :
    ted.PostTree.mirror_loop2_loop0 a.kids pos x ks j ⦃ r =>
      r.val.map (fun k => k.val) = revPos (a.kids.val[x.val]!).val pos.val 0 ⦄ := by
  unfold ted.PostTree.mirror_loop2_loop0
  have hkv : a.kids.val.length = a.label.length := hW.n4
  have hkx : x.val + 1 - 1 = x.val := by omega
  apply loop.spec_decr_nat
    (measure := fun s => s.2.val)
    (inv := fun s => s.2.val ≤ (a.kids.val[x.val]!).val.length ∧
      s.1.val.map (fun k => k.val) = revPos (a.kids.val[x.val]!).val pos.val s.2.val)
  · intro s hs
    obtain ⟨ks1, j1⟩ := s
    obtain ⟨hs1, hs2⟩ := hs
    dsimp only at hs1 hs2 ⊢
    unfold ted.PostTree.mirror_loop2_loop0.body
    by_cases hj0 : j1 > 0#usize
    · rw [if_pos hj0]
      have hj0' : 0 < j1.val := hj0
      step as ⟨j2, hj2⟩
      step as ⟨v1, hv1⟩
      have hv1' : v1 = a.kids.val[x.val]! := by
        rw [hv1, getG_eq _ _ (by omega)]
      subst hv1'
      step as ⟨i, hi⟩
      have hi' : i = (a.kids.val[x.val]!).val[j2.val]! := by
        rw [hi]; exact (getG_eq _ _ (by omega)).symm
      step as ⟨i1, hi1⟩
      have hi1' : i1.val = i.val := by rw [hi1]; exact U32.cast_Usize_val_eq i
      have hlt := kid_lt a hW (x.val + 1) (by omega) (by omega) j2.val (by rw [hkx]; omega)
      rw [hkx] at hlt
      have hlt' : i.val < a.label.length := by rw [hi']; omega
      step as ⟨i2, hi2⟩
      have hi2' : i2 = pos.val[i.val]! := by
        have hl1 : i1.val < pos.val.length := by
          have : pos.val.length = a.label.length := hpl; omega
        rw [hi2, ← getG_eq _ _ hl1, hi1']
      have hi2v := hpv i.val hlt'
      step as ⟨i3, hi3⟩
      have hi3' : i3.val = i2.val := by
        rw [hi3, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by have := hpv i.val hlt'; rw [← hi2'] at this; omega)
      have hkl : ks1.val.length + 1 ≤ Std.Usize.max := by
        have h1 := congrArg List.length hs2
        simp only [List.length_map, revPos, List.length_reverse, List.length_drop] at h1
        have h3 := alloc.vec.Vec.len_val (a.kids.val[x.val]!)
        have h4 := (alloc.vec.Vec.len (a.kids.val[x.val]!)).hBounds
        scalar_tac
      step as ⟨ks2, hks2⟩
      refine ⟨by omega, ?_, by omega⟩
      rw [hks2, List.map_append]
      rw [hs2]
      unfold revPos
      have hlen : j2.val < ((a.kids.val[x.val]!).val).length := by omega
      have hdrop : (a.kids.val[x.val]!).val.drop j2.val =
          (a.kids.val[x.val]!).val[j2.val]! :: (a.kids.val[x.val]!).val.drop (j2.val + 1) := by
        rw [getG_eq _ _ hlen]
        exact List.drop_eq_getElem_cons hlen
      have e : j2.val + 1 = j1.val := by omega
      rw [e] at hdrop
      rw [hdrop]
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, hi3']
      rw [hi2', hi']
    · rw [if_neg hj0]
      simp only [WP.spec_ok]
      have : j1.val = 0 := by scalar_tac
      rw [hs2, this]
  · exact ⟨hj, hks⟩

/-- The three rebuilt arrays hold, at the new position of each node, the label, kind and reversed child positions. -/
def FillInv (a : ted.PostTree) (pos : List Std.Usize) (x : Nat)
    (label kind : List Std.U32) (kids : List (alloc.vec.Vec Std.U32)) : Prop :=
  ∀ y < x, label[(pos[y]!).val]! = a.label.val[y]! ∧ kind[(pos[y]!).val]! = a.kind.val[y]! ∧
    ((kids[(pos[y]!).val]!).val.map (fun k => k.val)) = revPos (a.kids.val[y]!).val pos 0

theorem pos_inj (a : ted.PostTree) (hW : PT.Wf a) (pos : List Std.Usize)
    (hP : ∀ y < a.label.length, (pos[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
    {y z : Nat} (hy : y < a.label.length) (hz : z < a.label.length) (h : (pos[y]!).val = (pos[z]!).val) : y = z := by
  have h1 := hP y hy
  have h2 := hP z hz
  have := pim_inj hW.wfl (n := a.label.length) (x := y + 1) (y := z + 1) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  omega

theorem pos_lt (a : ted.PostTree) (hW : PT.Wf a) (pos : List Std.Usize)
    (hP : ∀ y < a.label.length, (pos[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
    {y : Nat} (hy : y < a.label.length) : (pos[y]!).val < a.label.length := by
  have h1 := hP y hy
  have := pim_mem hW.wfl (n := a.label.length) (x := y + 1) (by omega) (by omega)
  omega

set_option maxHeartbeats 3200000 in
theorem mirror_fill_spec (a : ted.PostTree) (hW : PT.Wf a) (n : Std.Usize) (pos : alloc.vec.Vec Std.Usize)
    (x : Std.Usize) (label kind : alloc.vec.Vec Std.U32) (kids : alloc.vec.Vec (alloc.vec.Vec Std.U32))
    (hn : n.val = a.label.length) (hn31 : a.label.length < 2 ^ 31)
    (hpl : pos.length = a.label.length)
    (hP : ∀ y < a.label.length, (pos.val[y]!).val + 1 = pim (laOf a) a.label.length (y + 1))
    (hll : label.length = a.label.length) (hkl : kind.length = a.label.length)
    (hkdl : kids.length = a.label.length) (hx : x.val ≤ a.label.length)
    (hI : FillInv a pos.val x.val label.val kind.val kids.val) :
    ted.PostTree.mirror_loop2 a.label a.kids a.kind n pos x label kind kids ⦃ r =>
      r.1.length = a.label.length ∧ r.2.1.length = a.label.length ∧ r.2.2.length = a.label.length ∧
      FillInv a pos.val a.label.length r.1.val r.2.1.val r.2.2.val ⦄ := by
  unfold ted.PostTree.mirror_loop2
  apply loop.spec_decr_nat
    (measure := fun s => a.label.length - s.1.val)
    (inv := fun s => s.1.val ≤ a.label.length ∧ s.2.1.length = a.label.length ∧ s.2.2.1.length = a.label.length ∧
      s.2.2.2.length = a.label.length ∧ FillInv a pos.val s.1.val s.2.1.val s.2.2.1.val s.2.2.2.val)
  · intro s hs
    obtain ⟨x1, label1, kind1, kids1⟩ := s
    obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hs
    dsimp only at hs1 hs2 hs3 hs4 hs5 ⊢
    unfold ted.PostTree.mirror_loop2.body
    by_cases hxn : x1 < n
    · rw [if_pos hxn]
      have hxn' : x1.val < a.label.length := by have : x1.val < n.val := hxn; omega
      have hpl' : pos.val.length = a.label.length := hpl
      have hal : a.label.val.length = a.label.length := rfl
      have hak : a.kind.val.length = a.label.length := hW.n3
      have hakd : a.kids.val.length = a.label.length := hW.n4
      step as ⟨y, hy⟩
      have hy' : y.val = (pos.val[x1.val]!).val := by rw [hy, getG_eq _ _ (by omega)]
      have hylt := pos_lt a hW pos.val hP hxn'
      step as ⟨i, hi⟩
      have hi' : i = a.label.val[x1.val]! := by rw [hi]; exact (getG_eq _ _ (by omega)).symm
      step as ⟨old, imb, ho, himb⟩
      step as ⟨i1, hi1⟩
      have hi1' : i1 = a.kind.val[x1.val]! := by rw [hi1]; exact (getG_eq _ _ (by omega)).symm
      step as ⟨old2, imb2, ho2, himb2⟩
      step as ⟨v3, hv3⟩
      have hv3' : v3 = a.kids.val[x1.val]! := by rw [hv3]; exact (getG_eq _ _ (by omega)).symm
      have hlen3 : v3.len.val = (a.kids.val[x1.val]!).val.length := by
        rw [alloc.vec.Vec.len_val, hv3']
      have hpv : ∀ y < a.label.length, (pos.val[y]!).val + 1 ≤ a.label.length := fun y hy => by
        have := pos_lt a hW pos.val hP hy; omega
      refine WP.spec_bind (mirror_kids_spec a hW pos x1 (alloc.vec.Vec.new Std.U32) v3.len hn31 hxn' hpl
        (by omega) (by rw [hlen3]; simp [alloc.vec.Vec.new, revPos]) hpv) ?_
      intro ks hks
      have hd3 : kids1.val.length = a.label.length := hs4
      step as ⟨old3, imb3, ho3, himb3⟩
      step as ⟨x2, hx2⟩
      have hlset : (imb i).val = label1.val.set y.val i := by rw [himb, alloc.vec.Vec.set_val_eq]
      have hkset : (imb2 i1).val = kind1.val.set y.val i1 := by rw [himb2, alloc.vec.Vec.set_val_eq]
      have hdset : (imb3 ks).val = kids1.val.set y.val ks := by rw [himb3, alloc.vec.Vec.set_val_eq]
      have hl1 : label1.val.length = a.label.length := hs2
      have hk1 : kind1.val.length = a.label.length := hs3
      refine ⟨by omega, ?_, ?_, ?_, ?_, by omega⟩
      · simp only [alloc.vec.Vec.length, hlset, List.length_set]; exact hl1
      · simp only [alloc.vec.Vec.length, hkset, List.length_set]; exact hk1
      · simp only [alloc.vec.Vec.length, hdset, List.length_set]; exact hd3
      · intro y' hyl
        rw [hlset, hkset, hdset]
        by_cases hyx : y' = x1.val
        · subst hyx
          rw [← hy', getG_set_eq _ _ _ (by omega), getG_set_eq _ _ _ (by omega), getG_set_eq _ _ _ (by omega)]
          refine ⟨hi'.symm ▸ rfl, hi1'.symm ▸ rfl, ?_⟩
          rw [hks]
        · have hy'lt : y' < x1.val := by omega
          have hne : (pos.val[y']!).val ≠ y.val := by
            intro h
            rw [hy'] at h
            exact hyx (pos_inj a hW pos.val hP (by omega) hxn' h)
          rw [getG_set_ne _ _ _ _ hne, getG_set_ne _ _ _ _ hne, getG_set_ne _ _ _ _ hne]
          exact hs5 y' hy'lt
    · rw [if_neg hxn]
      simp only [WP.spec_ok]
      have : x1.val = a.label.length := by
        have : ¬ x1.val < n.val := hxn
        omega
      refine ⟨hs2, hs3, hs4, ?_⟩
      rw [← this]; exact hs5
  · exact ⟨hx, hll, hkl, hkdl, hI⟩

end difffold_lines_extract
