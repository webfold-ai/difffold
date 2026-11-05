import RealDiffIds
import HistPure
import RealIntern
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-! Soundness of the histogram differ `diff_histogram_ids` of `src/lines.rs` over the Aeneas translation of the
real source: the flags it returns form a valid edit script (the lines kept on the two sides are equal lists).
Nothing is claimed about optimality. -/

/-- The index structure built by `index_a` over `a[alo..p)`: chain heads, links, and counts. -/
structure IdxOK (a : Slice U32) (alo p : Nat) (h : lines.Hist) : Prop where
  i1 : ∀ (k : Nat) x, h.head.val[k]? = some x → x = lines.NIL ∨
    (alo ≤ x.val ∧ x.val < p ∧ ∃ u, a.val[x.val]? = some u ∧ u.val = k)
  i2 : ∀ (j : Nat) y, alo ≤ j → j < p → h.nxt.val[j]? = some y → y = lines.NIL ∨
    (alo ≤ y.val ∧ y.val < j ∧ ∃ u, a.val[y.val]? = some u ∧ a.val[j]? = some u)
  i3 : ∀ (k : Nat) c, h.cnt.val[k]? = some c → c.val ≤ p - alo ∧
    (0 < c.val → ∃ j, alo ≤ j ∧ j < p ∧ ∃ u, a.val[j]? = some u ∧ u.val = k)

/-- Sizes of the arrays of the histogram state. -/
structure HSz (A B n : Nat) (h : lines.Hist) : Prop where
  cnt : h.cnt.val.length = n
  head : h.head.val.length = n
  nxt : h.nxt.val.length = A
  del : h.del.val.length = A
  ins : h.ins.val.length = B
  vf : 2 * (A + B) + 3 ≤ h.vf.val.length
  vb : 2 * (A + B) + 3 ≤ h.vb.val.length

/-- The state between two `hist` calls: no chain heads and no counts. -/
def HClean (h : lines.Hist) : Prop :=
  (∀ (k : Nat) x, h.head.val[k]? = some x → x = lines.NIL) ∧ (∀ (k : Nat) c, h.cnt.val[k]? = some c → c.val = 0)

theorem NIL_ne_of_lt (x : U32) (h : x.val < 4294967295) : x ≠ lines.NIL := by
  intro e; rw [e, NIL_val] at h; omega

theorem index_a_loop_spec (a : Slice U32) (n alo : Nat) (ahi : Usize)
    (hid : ∀ x ∈ a.val, x.val < n) (hahi : ahi.val ≤ a.val.length) (hN : a.val.length ≤ 2 ^ 28) :
    ∀ (h : lines.Hist) (i : Usize), alo ≤ i.val → i.val ≤ ahi.val → HSz a.val.length 0 n h →
    IdxOK a alo i.val h →
    lines.index_a_loop a h ahi i ⦃ h' => HSz a.val.length 0 n h' ∧ IdxOK a alo ahi.val h' ∧
      h'.del = h.del ∧ h'.ins = h.ins ∧ h'.vf = h.vf ∧ h'.vb = h.vb ⦄ := by
  intro h i hi1 hi2 hs hI
  unfold lines.index_a_loop
  apply loop.spec_decr_nat (fun (x : lines.Hist × Usize) => ahi.val - x.2.val)
    (fun (x : lines.Hist × Usize) => alo ≤ x.2.val ∧ x.2.val ≤ ahi.val ∧ HSz a.val.length 0 n x.1 ∧
      IdxOK a alo x.2.val x.1 ∧ x.1.del = h.del ∧ x.1.ins = h.ins ∧ x.1.vf = h.vf ∧ x.1.vb = h.vb) _ _ (h, i)
  · rintro ⟨h1, i1⟩ ⟨hi1, hi2, hs1, hI1, hd, hin, hvf, hvb⟩
    simp only at hi1 hi2 hs1 hI1 hd hin hvf hvb
    unfold lines.index_a_loop.body
    dsimp only
    by_cases hlt : i1 < ahi
    · rw [if_pos hlt]
      have hlt' : i1.val < ahi.val := hlt
      have hia : i1.val < a.val.length := by omega
      obtain ⟨u, hu⟩ : ∃ u, a.val[i1.val]? = some u := ⟨_, List.getElem?_eq_getElem hia⟩
      have hun : u.val < n := hid u (List.mem_of_getElem? hu)
      step as ⟨x, hx⟩
      have hxu : x = u := by
        rw [hx]; have := List.getElem?_eq_getElem hia; rw [hu] at this; exact (Option.some.inj this).symm
      subst hxu
      step as ⟨id, hid'⟩
      have hidv : id.val = x.val := by rw [hid']; simp
      have hcl : id.val < h1.cnt.val.length := by rw [hs1.cnt]; omega
      have hhl : id.val < h1.head.val.length := by rw [hs1.head]; omega
      have hnl : i1.val < h1.nxt.val.length := by rw [hs1.nxt]; omega
      obtain ⟨c, hcg⟩ : ∃ c, h1.cnt.val[id.val]? = some c := ⟨_, List.getElem?_eq_getElem hcl⟩
      have hcb := (hI1.i3 _ c hcg).1
      have hc28 : c.val ≤ 2 ^ 28 := by omega
      step as ⟨c', cb, hc', hcb'⟩
      have hc'c : c' = c := by
        rw [hc']; have := List.getElem?_eq_getElem hcl; rw [hcg] at this; exact (Option.some.inj this).symm
      subst hc'c
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      obtain ⟨g, hg⟩ : ∃ g, h1.head.val[id.val]? = some g := ⟨_, List.getElem?_eq_getElem hhl⟩
      have hi4g : i4 = g := by
        rw [hi4]; have := List.getElem?_eq_getElem hhl; rw [hg] at this; exact (Option.some.inj this).symm
      step as ⟨y, nb, hy, hnb⟩
      step as ⟨y2, hb2, hy2, hhb⟩
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      have hi5v : i5.val = i1.val := by rw [hi5]; simp; omega
      have hcnt' : (cb i3).val = h1.cnt.val.set id.val i3 := by rw [hcb']; simp [alloc.vec.Vec.set]
      have hhead' : (hb2 i5).val = h1.head.val.set id.val i5 := by rw [hhb]; simp [alloc.vec.Vec.set]
      have hnxt' : (nb i4).val = h1.nxt.val.set i1.val i4 := by rw [hnb]; simp [alloc.vec.Vec.set]
      refine ⟨by omega, by omega, ?_, ?_, hd, hin, hvf, hvb, by omega⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hcnt', List.length_set]; exact hs1.cnt
        · simp only [hhead', List.length_set]; exact hs1.head
        · simp only [hnxt', List.length_set]; exact hs1.nxt
        · exact hs1.del
        · exact hs1.ins
        · exact hs1.vf
        · exact hs1.vb
      · refine ⟨?_, ?_, ?_⟩
        · intro k xx hk
          simp only [hhead', List.getElem?_set] at hk
          by_cases hkk : id.val = k
          · rw [if_pos hkk, if_pos (by omega)] at hk
            have := Option.some.inj hk; subst this
            right; refine ⟨by omega, by omega, x, ?_, by omega⟩
            rw [hi5v]; exact hu
          · rw [if_neg hkk] at hk
            rcases hI1.i1 k xx hk with h | ⟨h1', h2', h3'⟩
            · exact Or.inl h
            · right; exact ⟨h1', by omega, h3'⟩
        · intro j yy hj1 hj2 hy
          simp only [hnxt', List.getElem?_set] at hy
          by_cases hjj : i1.val = j
          · rw [if_pos hjj, if_pos (by omega)] at hy
            have := Option.some.inj hy; subst this
            rcases hI1.i1 id.val g hg with h | ⟨h1', h2', u', hu', hu'v⟩
            · rw [hi4g]; exact Or.inl h
            · rw [hi4g]; right
              refine ⟨h1', by omega, u', hu', ?_⟩
              have hxe : u' = x := UScalar.eq_of_val_eq (by omega)
              rw [← hjj, hu, hxe]
          · rw [if_neg hjj] at hy
            rcases hI1.i2 j yy hj1 (by omega) hy with h | ⟨h1', h2', h3'⟩
            · exact Or.inl h
            · right; exact ⟨h1', h2', h3'⟩
        · intro k cc hk
          simp only [hcnt', List.getElem?_set] at hk
          by_cases hkk : id.val = k
          · rw [if_pos hkk, if_pos (by omega)] at hk
            have := Option.some.inj hk; subst this
            refine ⟨by omega, fun _ => ⟨i1.val, hi1, by omega, x, hu, by omega⟩⟩
          · rw [if_neg hkk] at hk
            obtain ⟨h1', h2'⟩ := hI1.i3 k cc hk
            refine ⟨by omega, fun hp => ?_⟩
            obtain ⟨j, hj1, hj2, w⟩ := h2' hp
            exact ⟨j, hj1, by omega, w⟩
    · rw [if_neg hlt]
      simp only [WP.spec_ok]
      have hge : i1.val = ahi.val := by
        have : ¬ i1.val < ahi.val := fun h => hlt h
        omega
      refine ⟨hs1, ?_, hd, hin, hvf, hvb⟩
      rw [← hge]; exact hI1
  · exact ⟨hi1, hi2, hs, hI, rfl, rfl, rfl, rfl⟩

/-- What remains to be reset by `unindex_a` from position `q`. -/
def Pending (a : Slice U32) (q ahi : Nat) (h : lines.Hist) : Prop :=
  (∀ (k : Nat) x, h.head.val[k]? = some x → x = lines.NIL ∨
    ∃ j, q ≤ j ∧ j < ahi ∧ ∃ u, a.val[j]? = some u ∧ u.val = k) ∧
  (∀ (k : Nat) c, h.cnt.val[k]? = some c → c.val = 0 ∨
    ∃ j, q ≤ j ∧ j < ahi ∧ ∃ u, a.val[j]? = some u ∧ u.val = k)

theorem unindex_a_loop_spec (a : Slice U32) (n : Nat) (ahi : Usize)
    (hid : ∀ x ∈ a.val, x.val < n) (hahi : ahi.val ≤ a.val.length) :
    ∀ (h : lines.Hist) (i : Usize), i.val ≤ ahi.val → HSz a.val.length 0 n h → Pending a i.val ahi.val h →
    lines.unindex_a_loop a h ahi i ⦃ h' => HSz a.val.length 0 n h' ∧ HClean h' ∧
      h'.del = h.del ∧ h'.ins = h.ins ∧ h'.vf = h.vf ∧ h'.vb = h.vb ∧ h'.nxt = h.nxt ⦄ := by
  intro h i hi2 hs hP
  unfold lines.unindex_a_loop
  apply loop.spec_decr_nat (fun (x : lines.Hist × Usize) => ahi.val - x.2.val)
    (fun (x : lines.Hist × Usize) => x.2.val ≤ ahi.val ∧ HSz a.val.length 0 n x.1 ∧
      Pending a x.2.val ahi.val x.1 ∧ x.1.del = h.del ∧ x.1.ins = h.ins ∧ x.1.vf = h.vf ∧ x.1.vb = h.vb ∧
      x.1.nxt = h.nxt) _ _ (h, i)
  · rintro ⟨h1, i1⟩ ⟨hi2, hs1, hP1, hd, hin, hvf, hvb, hnx⟩
    simp only at hi2 hs1 hP1 hd hin hvf hvb hnx
    unfold lines.unindex_a_loop.body
    dsimp only
    by_cases hlt : i1 < ahi
    · rw [if_pos hlt]
      have hlt' : i1.val < ahi.val := hlt
      have hia : i1.val < a.val.length := by omega
      obtain ⟨u, hu⟩ : ∃ u, a.val[i1.val]? = some u := ⟨_, List.getElem?_eq_getElem hia⟩
      have hun : u.val < n := hid u (List.mem_of_getElem? hu)
      step as ⟨x, hx⟩
      have hxu : x = u := by
        rw [hx]; have := List.getElem?_eq_getElem hia; rw [hu] at this; exact (Option.some.inj this).symm
      subst hxu
      step as ⟨id, hid'⟩
      have hidv : id.val = x.val := by rw [hid']; simp
      have hcl : id.val < h1.cnt.val.length := by rw [hs1.cnt]; omega
      have hhl : id.val < h1.head.val.length := by rw [hs1.head]; omega
      step as ⟨c', cb, hc', hcb'⟩
      step as ⟨c2, hb2, hc2, hhb⟩
      step as ⟨i2, hi2'⟩
      have hcnt' : (cb 0#u32).val = h1.cnt.val.set id.val 0#u32 := by rw [hcb']; simp [alloc.vec.Vec.set]
      have hhead' : (hb2 lines.NIL).val = h1.head.val.set id.val lines.NIL := by rw [hhb]; simp [alloc.vec.Vec.set]
      refine ⟨by omega, ?_, ?_, hd, hin, hvf, hvb, hnx, by omega⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hcnt', List.length_set]; exact hs1.cnt
        · simp only [hhead', List.length_set]; exact hs1.head
        · exact hs1.nxt
        · exact hs1.del
        · exact hs1.ins
        · exact hs1.vf
        · exact hs1.vb
      · refine ⟨?_, ?_⟩
        · intro k xx hk
          simp only [hhead', List.getElem?_set] at hk
          by_cases hkk : id.val = k
          · rw [if_pos hkk, if_pos (by omega)] at hk
            exact Or.inl (Option.some.inj hk).symm
          · rw [if_neg hkk] at hk
            rcases hP1.1 k xx hk with h | ⟨j, hj1, hj2, w, hw1, hw2⟩
            · exact Or.inl h
            · right
              refine ⟨j, ?_, hj2, w, hw1, hw2⟩
              have : j ≠ i1.val := by
                intro hji; rw [hji, hu] at hw1; have := Option.some.inj hw1; subst this; omega
              rw [hi2'] ; omega
        · intro k cc hk
          simp only [hcnt', List.getElem?_set] at hk
          by_cases hkk : id.val = k
          · rw [if_pos hkk, if_pos (by omega)] at hk
            left; have := Option.some.inj hk; rw [← this]; rfl
          · rw [if_neg hkk] at hk
            rcases hP1.2 k cc hk with h | ⟨j, hj1, hj2, w, hw1, hw2⟩
            · exact Or.inl h
            · right
              refine ⟨j, ?_, hj2, w, hw1, hw2⟩
              have : j ≠ i1.val := by
                intro hji; rw [hji, hu] at hw1; have := Option.some.inj hw1; subst this; omega
              rw [hi2']; omega
    · rw [if_neg hlt]
      simp only [WP.spec_ok]
      have hge : i1.val = ahi.val := by
        have : ¬ i1.val < ahi.val := fun h => hlt h
        omega
      refine ⟨hs1, ⟨?_, ?_⟩, hd, hin, hvf, hvb, hnx⟩
      · intro k xx hk
        rcases hP1.1 k xx hk with h | ⟨j, hj1, hj2, _⟩
        · exact h
        · omega
      · intro k cc hk
        rcases hP1.2 k cc hk with h | ⟨j, hj1, hj2, _⟩
        · exact h
        · omega
  · exact ⟨hi2, hs, hP, rfl, rfl, rfl, rfl, rfl⟩

/-- `index_a` followed by `unindex_a` is the identity on the clean state. -/
theorem index_a_spec (a : Slice U32) (n : Nat) (alo ahi : Usize)
    (hid : ∀ x ∈ a.val, x.val < n) (hahi : ahi.val ≤ a.val.length) (hN : a.val.length ≤ 2 ^ 28)
    (hlo : alo.val ≤ ahi.val) (h : lines.Hist) (hs : HSz a.val.length 0 n h) (hc : HClean h) :
    lines.index_a a h alo ahi ⦃ h' => HSz a.val.length 0 n h' ∧ IdxOK a alo.val ahi.val h' ∧
      h'.del = h.del ∧ h'.ins = h.ins ∧ h'.vf = h.vf ∧ h'.vb = h.vb ⦄ := by
  unfold lines.index_a
  apply index_a_loop_spec a n alo.val ahi hid hahi hN h alo le_rfl hlo hs
  refine ⟨?_, ?_, ?_⟩
  · intro k x hk; left; exact hc.1 k x hk
  · intro j y h1 h2; omega
  · intro k c hk; rw [hc.2 k c hk]; simp

theorem unindex_a_spec (a : Slice U32) (n : Nat) (alo ahi : Usize)
    (hid : ∀ x ∈ a.val, x.val < n) (hahi : ahi.val ≤ a.val.length) (h : lines.Hist)
    (hlo : alo.val ≤ ahi.val) (hs : HSz a.val.length 0 n h) (hI : IdxOK a alo.val ahi.val h) :
    lines.unindex_a a h alo ahi ⦃ h' => HSz a.val.length 0 n h' ∧ HClean h' ∧
      h'.del = h.del ∧ h'.ins = h.ins ∧ h'.vf = h.vf ∧ h'.vb = h.vb ∧ h'.nxt = h.nxt ⦄ := by
  unfold lines.unindex_a
  apply unindex_a_loop_spec a n ahi hid hahi h alo hlo hs
  refine ⟨?_, ?_⟩
  · intro k x hk
    rcases hI.i1 k x hk with h | ⟨h1, h2, w⟩
    · exact Or.inl h
    · exact Or.inr ⟨x.val, h1, h2, w⟩
  · intro k c hk
    obtain ⟨h1, h2⟩ := hI.i3 k c hk
    by_cases hc : c.val = 0
    · exact Or.inl hc
    · obtain ⟨j, hj1, hj2, w⟩ := h2 (by omega)
      exact Or.inr ⟨j, hj1, hj2, w⟩

/-- An anchor: a run of `len` equal ids, starting `bl` before the matching position, inside both ranges. -/
def AOK (A B : List U32) (alo ahi blo bhi : Nat) (an : lines.Anchor) : Prop :=
  alo + an.bl.val ≤ an.i.val ∧ blo + an.bl.val ≤ an.j.val ∧ an.bl.val < an.len.val ∧
  an.i.val - an.bl.val + an.len.val ≤ ahi ∧ an.j.val - an.bl.val + an.len.val ≤ bhi ∧
  Myers.sg A (an.i.val - an.bl.val) (an.i.val - an.bl.val + an.len.val) =
    Myers.sg B (an.j.val - an.bl.val) (an.j.val - an.bl.val + an.len.val)

def BestOK (A B : List U32) (alo ahi blo bhi : Nat) (best : Option lines.Anchor) : Prop :=
  ∀ an, best = some an → AOK A B alo ahi blo bhi an

theorem walk_chain_spec (a b : Slice U32) (alo ahi blo bhi j : Usize) (u : U32)
    (hahi : ahi.val ≤ a.val.length) (hbhi : bhi.val ≤ b.val.length) (hlo : alo.val ≤ ahi.val)
    (hblo : blo.val ≤ j.val) (hjb : j.val < bhi.val) (hbj : b.val[j.val]? = some u) :
    ∀ (M : Nat) (h : lines.Hist) («at» : U32) (c : U32) (best : Option lines.Anchor),
    IdxOK a alo.val ahi.val h → h.nxt.val.length = a.val.length →
    («at» = lines.NIL ∨ (alo.val ≤ «at».val ∧ «at».val < ahi.val ∧ a.val[«at».val]? = some u)) →
    (if «at» = lines.NIL then 0 else «at».val + 1) ≤ M →
    BestOK a.val b.val alo.val ahi.val blo.val bhi.val best →
    lines.walk_chain a b h «at» (alo, ahi) (blo, bhi) j c best ⦃ r =>
      BestOK a.val b.val alo.val ahi.val blo.val bhi.val r ⦄ := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro h «at» c best hI hnl hat hM hbest
  rw [lines.walk_chain.eq_1]
  by_cases hn : «at» = lines.NIL
  · simp only [hn, if_true]
    exact (WP.spec_ok best).mpr hbest
  · simp only [hn, if_false]
    obtain ⟨hat1, hat2, hat3⟩ : alo.val ≤ «at».val ∧ «at».val < ahi.val ∧ a.val[«at».val]? = some u := by
      rcases hat with h0 | h0
      · exact absurd h0 hn
      · exact h0
    simp only [if_neg hn] at hM
    step as ⟨i, hi⟩
    have hiv : i.val = «at».val := by rw [hi]; simp
    have hia : i.val ≤ a.val.length := by omega
    step as ⟨s, hsv, hsl⟩
    step as ⟨s1, hs1v, hs1l⟩
    step with common_suffix_u32 s s1 as ⟨bl, hbl1, hbl2, hbl3⟩
    step as ⟨s2, hs2v, hs2l⟩
    step as ⟨s3, hs3v, hs3l⟩
    step with common_prefix_u32 s2 s3 as ⟨fl, hfl1, hfl2, hfl3⟩
    step as ⟨i1, hi1⟩
    have hsL : s.val.length = i.val - alo.val := hsl
    have hs1L : s1.val.length = j.val - blo.val := hs1l
    have hs2L : s2.val.length = ahi.val - i.val := hs2l
    have hs3L : s3.val.length = bhi.val - j.val := hs3l
    have hfl_pos : 1 ≤ fl.val := by
      rcases hfl3 with h0 | ⟨x, y, hx, hy, hxy⟩
      · omega
      · by_contra hf0
        have hf0' : fl.val = 0 := by omega
        rw [hf0', hs2v] at hx
        rw [hf0', hs3v] at hy
        simp [List.slice, List.getElem?_take, List.getElem?_drop] at hx hy
        rw [hiv, hat3] at hx
        rw [hbj] at hy
        exact hxy ((Option.some.inj hx.2).symm.trans (Option.some.inj hy.2))
    have hcand : AOK a.val b.val alo.val ahi.val blo.val bhi.val
        { cnt := c, len := i1, i := i, j := j, bl := bl } := by
      simp only [AOK]
      have e1 : (↑bl : Nat) ≤ i.val - alo.val := by omega
      have e2 : (↑bl : Nat) ≤ j.val - blo.val := by omega
      refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
      have f1 : Myers.sg a.val (i.val - bl.val) i.val = Myers.sg b.val (j.val - bl.val) j.val := by
        have := hbl2
        rw [hsL, hs1L, hsv, hs1v] at this
        change List.drop _ (Myers.sg a.val alo.val i.val) = List.drop _ (Myers.sg b.val blo.val j.val) at this
        rw [Myers.sg_drop _ _ _ _ (by omega), Myers.sg_drop _ _ _ _ (by omega)] at this
        rwa [show alo.val + (i.val - alo.val - bl.val) = i.val - bl.val by omega,
          show blo.val + (j.val - blo.val - bl.val) = j.val - bl.val by omega] at this
      have f2 : Myers.sg a.val i.val (i.val + fl.val) = Myers.sg b.val j.val (j.val + fl.val) := by
        have := hfl2
        rw [hs2v, hs3v] at this
        change List.take _ (Myers.sg a.val i.val ahi.val) = List.take _ (Myers.sg b.val j.val bhi.val) at this
        rw [Myers.sg_take _ _ _ _ (by omega), Myers.sg_take _ _ _ _ (by omega)] at this
        exact this
      rw [show i.val - bl.val + i1.val = i.val + fl.val by omega,
        show j.val - bl.val + i1.val = j.val + fl.val by omega,
        Myers.sg_split _ (i.val - bl.val) i.val (i.val + fl.val) (by omega) (by omega),
        Myers.sg_split _ (j.val - bl.val) j.val (j.val + fl.val) (by omega) (by omega), f1, f2]
    obtain ⟨y, hy⟩ : ∃ y, h.nxt.val[i.val]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hym : y = lines.NIL ∨ (alo.val ≤ y.val ∧ y.val < i.val ∧ ∃ u', a.val[y.val]? = some u' ∧ a.val[i.val]? = some u') :=
      hI.i2 i.val y (by omega) (by omega) hy
    have hrec : ∀ best2 : Option lines.Anchor, BestOK a.val b.val alo.val ahi.val blo.val bhi.val best2 →
        lines.walk_chain a b h y (alo, ahi) (blo, bhi) j c best2 ⦃ r =>
          BestOK a.val b.val alo.val ahi.val blo.val bhi.val r ⦄ := by
      intro best2 hb2
      refine ih (if y = lines.NIL then 0 else y.val + 1) (by
        by_cases hyn : y = lines.NIL
        · simp [hyn]; omega
        · simp [hyn]; rcases hym with h0 | h0
          · exact absurd h0 hyn
          · omega) h y c best2 hI hnl ?_ le_rfl hb2
      rcases hym with h0 | ⟨h1', h2', u', hu', hu''⟩
      · exact Or.inl h0
      · right
        rw [hiv] at hu''
        rw [hat3] at hu''
        have : u' = u := (Option.some.inj hu'').symm
        subst this
        exact ⟨h1', by omega, hu'⟩
    have hcandB : BestOK a.val b.val alo.val ahi.val blo.val bhi.val
        (some { cnt := c, len := i1, i := i, j := j, bl := bl }) := by
      intro an han
      have := Option.some.inj han
      subst this
      exact hcand
    have hnxi : ∀ i2 : U32, i2 = h.nxt.val[i.val]'(by omega) → i2 = y := by
      intro i2 h2
      rw [h2]; have := List.getElem?_eq_getElem (show i.val < h.nxt.val.length by omega)
      rw [hy] at this; exact (Option.some.inj this).symm
    cases best with
    | none =>
      step*
      have hi2y : i2 = y := hnxi i2 i2_post
      simp only [if_true, bind_tc_ok]
      rw [hi2y]
      exact hrec _ hcandB
    | some b0 =>
      have hrest : ∀ x : Bool, (do
          let i2 ← h.nxt.index_usize i
          let best2 ← if x = true then ok (some { cnt := c, len := i1, i := i, j := j, bl := bl })
            else ok (some b0)
          lines.walk_chain a b h i2 (alo, ahi) (blo, bhi) j c best2) ⦃ r =>
            BestOK a.val b.val alo.val ahi.val blo.val bhi.val r ⦄ := by
        intro x
        step as ⟨i2, hi2⟩
        have hi2y : i2 = y := hnxi i2 hi2
        rw [hi2y]
        cases x
        · simp only [Bool.false_eq_true, if_false, bind_tc_ok]; exact hrec _ hbest
        · simp only [if_true, bind_tc_ok]; exact hrec _ hcandB
      by_cases h1 : c < b0.cnt
      · simp only [h1, if_true, bind_tc_ok]; exact hrest true
      · by_cases h2 : c = b0.cnt
        · simp only [if_neg h1, if_pos h2, bind_tc_ok]; exact hrest (decide (i1 > b0.len))
        · simp only [if_neg h1, if_neg h2, bind_tc_ok]; exact hrest false

theorem find_anchor_loop_spec (a b : Slice U32) (n : Nat) (alo ahi blo bhi : Usize)
    (hidb : ∀ x ∈ b.val, x.val < n) (hahi : ahi.val ≤ a.val.length) (hbhi : bhi.val ≤ b.val.length)
    (hlo : alo.val ≤ ahi.val) (h : lines.Hist) (hcn : h.cnt.val.length = n) (hhn : h.head.val.length = n)
    (hnl : h.nxt.val.length = a.val.length) (hI : IdxOK a alo.val ahi.val h) :
    ∀ (best : Option lines.Anchor) (j : Usize), blo.val ≤ j.val → j.val ≤ bhi.val →
    BestOK a.val b.val alo.val ahi.val blo.val bhi.val best →
    lines.find_anchor_loop a b h alo ahi blo bhi best j ⦃ r =>
      BestOK a.val b.val alo.val ahi.val blo.val bhi.val r ⦄ := by
  intro best j hj1 hj2 hbest
  unfold lines.find_anchor_loop
  apply loop.spec_decr_nat (fun (x : Option lines.Anchor × Usize) => bhi.val - x.2.val)
    (fun (x : Option lines.Anchor × Usize) => blo.val ≤ x.2.val ∧ x.2.val ≤ bhi.val ∧
      BestOK a.val b.val alo.val ahi.val blo.val bhi.val x.1) _ _ (best, j)
  · rintro ⟨best1, j1⟩ ⟨hj1, hj2, hb1⟩
    simp only at hj1 hj2 hb1
    unfold lines.find_anchor_loop.body
    dsimp only
    by_cases hlt : j1 < bhi
    · rw [if_pos hlt]
      have hlt' : j1.val < bhi.val := hlt
      have hjb : j1.val < b.val.length := by omega
      obtain ⟨u, hu⟩ : ∃ u, b.val[j1.val]? = some u := ⟨_, List.getElem?_eq_getElem hjb⟩
      have hun : u.val < n := hidb u (List.mem_of_getElem? hu)
      step as ⟨x, hx⟩
      have hxu : x = u := by
        rw [hx]; have := List.getElem?_eq_getElem hjb; rw [hu] at this; exact (Option.some.inj this).symm
      subst hxu
      step as ⟨id, hid'⟩
      have hidv : id.val = x.val := by rw [hid']; simp
      have hcl : id.val < h.cnt.val.length := by rw [hcn]; omega
      have hhl : id.val < h.head.val.length := by rw [hhn]; omega
      step as ⟨c, hc⟩
      refine Aeneas.Std.WP.spec_bind (Pₘ := fun r => BestOK a.val b.val alo.val ahi.val blo.val bhi.val r) ?_
        (fun r hr => ?_)
      swap
      · step as ⟨j2, hj2'⟩
        refine ⟨by omega, by omega, hr, by omega⟩
      have hwalk : ∀ best2 : Option lines.Anchor, BestOK a.val b.val alo.val ahi.val blo.val bhi.val best2 →
          (do
            let i1 ← h.head.index_usize id
            lines.walk_chain a b h i1 (alo, ahi) (blo, bhi) j1 c best2) ⦃ r =>
            BestOK a.val b.val alo.val ahi.val blo.val bhi.val r ⦄ := by
        intro best2 hb2
        obtain ⟨g, hg⟩ : ∃ g, h.head.val[id.val]? = some g := ⟨_, List.getElem?_eq_getElem hhl⟩
        step as ⟨i1, hi1⟩
        have hi1g : i1 = g := by
          rw [hi1]; have := List.getElem?_eq_getElem hhl; rw [hg] at this; exact (Option.some.inj this).symm
        rw [hi1g]
        have hgood : g = lines.NIL ∨ (alo.val ≤ g.val ∧ g.val < ahi.val ∧ a.val[g.val]? = some x) := by
          rcases hI.i1 id.val g hg with h0 | ⟨h1', h2', u', hu', hu''⟩
          · exact Or.inl h0
          · right
            have : u' = x := UScalar.eq_of_val_eq (by omega)
            subst this
            exact ⟨h1', h2', hu'⟩
        exact walk_chain_spec a b alo ahi blo bhi j1 x hahi hbhi hlo hj1 hlt' hu _ h g c best2 hI hnl hgood le_rfl hb2
      by_cases hc0 : c > 0#u32
      · rw [if_pos hc0]
        by_cases hc1 : c ≤ lines.HIST_LIMIT
        · rw [if_pos hc1]
          cases best1 with
          | none =>
            simp only [bind_tc_ok, if_true]
            exact hwalk none hb1
          | some bst =>
            by_cases hr : c ≤ bst.cnt
            · simp only [hr, decide_true, if_true, bind_tc_ok]
              exact hwalk _ hb1
            · simp only [hr, decide_false, Bool.false_eq_true, if_false, bind_tc_ok]
              exact (WP.spec_ok _).mpr hb1
        · rw [if_neg hc1]; exact (WP.spec_ok _).mpr hb1
      · rw [if_neg hc0]; exact (WP.spec_ok _).mpr hb1
    · rw [if_neg hlt]
      simp only [WP.spec_ok]
      exact hb1
  · exact ⟨hj1, hj2, hbest⟩

theorem any_common_spec (b : Slice U32) (n : Nat) (blo bhi : Usize)
    (hidb : ∀ x ∈ b.val, x.val < n) (hbhi : bhi.val ≤ b.val.length) (h : lines.Hist)
    (hcn : h.cnt.val.length = n) (hlo : blo.val ≤ bhi.val) :
    lines.any_common b h blo bhi ⦃ r => True ⦄ := by
  unfold lines.any_common lines.any_common_loop
  apply loop.spec_decr_nat (fun (x : Bool × Usize) => bhi.val - x.2.val)
    (fun (x : Bool × Usize) => x.2.val ≤ bhi.val) _ _ (false, blo)
  · rintro ⟨f1, j1⟩ hj
    simp only at hj
    unfold lines.any_common_loop.body
    dsimp only
    by_cases hlt : j1 < bhi
    · rw [if_pos hlt]
      have hlt' : j1.val < bhi.val := hlt
      have hjb : j1.val < b.val.length := by omega
      obtain ⟨u, hu⟩ : ∃ u, b.val[j1.val]? = some u := ⟨_, List.getElem?_eq_getElem hjb⟩
      have hun : u.val < n := hidb u (List.mem_of_getElem? hu)
      step as ⟨x, hx⟩
      have hxu : x = u := by
        rw [hx]; have := List.getElem?_eq_getElem hjb; rw [hu] at this; exact (Option.some.inj this).symm
      subst hxu
      step as ⟨id, hid'⟩
      have hidv : id.val = x.val := by rw [hid']; simp
      have hcl : id.val < h.cnt.val.length := by rw [hcn]; omega
      step as ⟨c, hc⟩
      by_cases hc0 : c > 0#u32
      · simp only [hc0, if_true, bind_tc_ok]
        step as ⟨j3, hj3⟩
        omega
      · simp only [hc0, if_false, bind_tc_ok]
        step as ⟨j3, hj3⟩
        omega
    · rw [if_neg hlt]; simp only [WP.spec_ok]
  · simp [hlo]

theorem find_anchor_spec (a b : Slice U32) (n : Nat) (alo ahi blo bhi : Usize)
    (hidb : ∀ x ∈ b.val, x.val < n) (hahi : ahi.val ≤ a.val.length) (hbhi : bhi.val ≤ b.val.length)
    (hlo : alo.val ≤ ahi.val) (hblo : blo.val ≤ bhi.val) (h : lines.Hist) (hcn : h.cnt.val.length = n)
    (hhn : h.head.val.length = n)
    (hnl : h.nxt.val.length = a.val.length) (hI : IdxOK a alo.val ahi.val h) :
    lines.find_anchor a b h (alo, ahi) (blo, bhi) ⦃ r =>
      BestOK a.val b.val alo.val ahi.val blo.val bhi.val r ⦄ := by
  unfold lines.find_anchor
  exact find_anchor_loop_spec a b n alo ahi blo bhi hidb hahi hbhi hlo h hcn hhn hnl hI none blo le_rfl hblo
    (by intro an han; cases han)

theorem vals_sg (l : List U32) (lo hi : Nat) : vals (Myers.sg l lo hi) = Myers.sg (vals l) lo hi := by
  simp [vals, Myers.sg, List.map_drop, List.map_take]

/-- `solve` on a trimmed range, as used by `hist`. -/
theorem hist_fallback_spec (a b : Slice U32) (n : Nat) (h : lines.Hist) (alo ahi blo bhi : Usize)
    (hs : HSz a.val.length b.val.length n h) (hN : a.val.length + b.val.length ≤ NMAX)
    (hahi : ahi.val ≤ a.val.length) (hbhi : bhi.val ≤ b.val.length) (hlo : alo.val ≤ ahi.val)
    (hblo : blo.val ≤ bhi.val)
    (hD : ∀ i, alo.val ≤ i → i < ahi.val → h.del.val[i]? = some false)
    (hI : ∀ j, blo.val ≤ j → j < bhi.val → h.ins.val[j]? = some false) :
    lines.hist_fallback a b h (alo, ahi) (blo, bhi) ⦃ h' =>
      HSz a.val.length b.val.length n h' ∧ h'.cnt = h.cnt ∧ h'.head = h.head ∧ h'.nxt = h.nxt ∧
      Myers.HPost (Myers.sg (vals a.val) alo.val ahi.val) (Myers.sg (vals b.val) blo.val bhi.val)
        alo.val blo.val h.del.val h.ins.val h'.del.val h'.ins.val ⦄ := by
  unfold lines.hist_fallback
  dsimp only
  step as ⟨s, hsv, hsl⟩
  step as ⟨s1, hs1v, hs1l⟩
  step as ⟨p2, hp2⟩
  rename_i hd2
  step as ⟨p3, hp3⟩
  rename_i hd3
  step as ⟨p4, hp4⟩
  rename_i hd4
  step as ⟨p5, hp5⟩
  rename_i hd5
  have e2 : p2.val = h.del.val := by
    have := congrArg Prod.fst hd2; simp [alloc.vec.Vec.deref_mut] at this; rw [this]; rfl
  have e3 : p3.val = h.ins.val := by
    have := congrArg Prod.fst hd3; simp [alloc.vec.Vec.deref_mut] at this; rw [this]; rfl
  have e4 : p4.val = h.vf.val := by
    have := congrArg Prod.fst hd4; simp [alloc.vec.Vec.deref_mut] at this; rw [this]; rfl
  have e5 : p5.val = h.vb.val := by
    have := congrArg Prod.fst hd5; simp [alloc.vec.Vec.deref_mut] at this; rw [this]; rfl
  have b2 : ∀ s, (hp2 s).val = s.val := by
    intro s; have := congrArg Prod.snd hd2; simp [alloc.vec.Vec.deref_mut] at this; rw [this]; rfl
  have b3 : ∀ s, (hp3 s).val = s.val := by
    intro s; have := congrArg Prod.snd hd3; simp [alloc.vec.Vec.deref_mut] at this; rw [this]; rfl
  have b4 : ∀ s, (hp4 s).val = s.val := by
    intro s; have := congrArg Prod.snd hd4; simp [alloc.vec.Vec.deref_mut] at this; rw [this]; rfl
  have b5 : ∀ s, (hp5 s).val = s.val := by
    intro s; have := congrArg Prod.snd hd5; simp [alloc.vec.Vec.deref_mut] at this; rw [this]; rfl
  have hslen : s.val.length = ahi.val - alo.val := hsl
  have hs1len : s1.val.length = bhi.val - blo.val := hs1l
  have hsvals : vals s.val = Myers.sg (vals a.val) alo.val ahi.val := by rw [hsv]; exact vals_sg _ _ _
  have hs1vals : vals s1.val = Myers.sg (vals b.val) blo.val bhi.val := by rw [hs1v]; exact vals_sg _ _ _
  have hAl : (vals s.val).length = ahi.val - alo.val := by simp [vals, hslen]
  have hBl : (vals s1.val).length = bhi.val - blo.val := by simp [vals, hs1len]
  have hsol := solve_spec _ s s1 (vals s.val) (vals s1.val) alo blo p2 p3 p4 p5 rfl rfl rfl
    (by simp only [vals_len] at *; omega)
    (by rw [e2, hs.del]; omega) (by rw [e3, hs.ins]; omega)
    (fun j hj => by rw [e2]; exact hD _ (by omega) (by omega))
    (fun j hj => by rw [e3]; exact hI _ (by omega) (by omega))
    (by rw [e4]; have := hs.vf; omega) (by rw [e5]; have := hs.vb; omega)
  step with hsol as ⟨s6, s7, s8, s9, hpost⟩
  obtain ⟨da, di, hso, hs6, hs7, hs8, hs9⟩ := hpost
  have hopt := Myers.solve_optimal Myers.mid_spec hso
  have hva := hopt.1
  have hv1 := hva.1
  have hv2 := hva.2.1
  have hdal : da.length = ahi.val - alo.val := by rw [hv1]; exact hAl
  have hdil : di.length = bhi.val - blo.val := by rw [hv2]; exact hBl
  have hl2 : alo.val + da.length ≤ p2.val.length := by rw [e2, hs.del]; omega
  have hl3 : blo.val + di.length ≤ p3.val.length := by rw [e3, hs.ins]; omega
  have hn6 : (hp2 s6).val.length = h.del.val.length := by
    rw [b2, hs6, Myers.splice_length _ _ _ hl2, e2]
  have hn7 : (hp3 s7).val.length = h.ins.val.length := by
    rw [b3, hs7, Myers.splice_length _ _ _ hl3, e3]
  refine ⟨⟨hs.cnt, hs.head, hs.nxt, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only []; rw [hn6]; exact hs.del
  · simp only []; rw [hn7]; exact hs.ins
  · simp only []; rw [b4, hs8, e4]; exact hs.vf
  · simp only []; rw [b5, hs9, e5]; exact hs.vb
  · refine ⟨da, di, ?_, ?_, ?_⟩
    · rw [← hsvals, ← hs1vals]; exact hva
    · rw [b2, hs6, e2]
    · rw [b3, hs7, e3]

theorem vec_setSlice_val (v : alloc.vec.Vec Bool) (lo : Nat) (d : List Bool) (h : lo + d.length ≤ v.val.length) :
    (alloc.vec.Vec.setSlice! v lo d).val = Myers.splice v.val lo d := by
  have : (alloc.vec.Vec.setSlice! v lo d).val = v.val.setSlice! lo d := by
    show (v.slice.setSlice! lo d).val = v.val.setSlice! lo d
    exact Slice.setSlice!_val _ _ _
  rw [this]; exact setSlice_splice _ _ _ h

/-- Setting a range of a flag vector to `true`, as `hist` does with `fill`. -/
theorem fill_true (v : alloc.vec.Vec Bool) (lo hi : Usize) (h1 : lo.val ≤ hi.val) (h2 : hi.val ≤ v.val.length) :
    (do
      let (s4, back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Bool) v
        { start := lo, «end» := hi }
      let s5 ← core.slice.Slice.fill core.clone.CloneBool s4 true
      ok (back s5)) ⦃ v' => v'.val = Myers.splice v.val lo.val (List.replicate (hi.val - lo.val) true) ⦄ := by
  have hcl : core.clone.CloneBool.clone true ⦃ fun v' => v' = true ⦄ := by
    simp [core.clone.CloneBool]
  step as ⟨s4, back, hs4v, hs4l, hback⟩
  step as ⟨s5, hs5l, hs5v⟩
  rw [hback, vec_setSlice_val]
  · simp [hs5v, hs5l, hs4l]
  · simp [hs5v, hs5l, hs4l]; omega

/-- The postcondition of `hist` on a trimmed range, and what the recursion hands back. -/
def HOut (a b : Slice U32) (n : Nat) (h : lines.Hist) (alo ahi blo bhi : Nat) (h' : lines.Hist) : Prop :=
  HSz a.val.length b.val.length n h' ∧ HClean h' ∧
  Myers.HPost (Myers.sg (vals a.val) alo ahi) (Myers.sg (vals b.val) blo bhi) alo blo
    h.del.val h.ins.val h'.del.val h'.ins.val

theorem hist_spec (a b : Slice U32) (n : Nat) (hida : ∀ x ∈ a.val, x.val < n) (hidb : ∀ x ∈ b.val, x.val < n)
    (hN : a.val.length + b.val.length ≤ NMAX) :
    ∀ (N : Nat) (h : lines.Hist) (alo ahi blo bhi : Usize) (depth : U32),
    (ahi.val - alo.val) + (bhi.val - blo.val) ≤ N → alo.val ≤ ahi.val → ahi.val ≤ a.val.length →
    blo.val ≤ bhi.val → bhi.val ≤ b.val.length → HSz a.val.length b.val.length n h → HClean h →
    (∀ i, alo.val ≤ i → i < ahi.val → h.del.val[i]? = some false) →
    (∀ j, blo.val ≤ j → j < bhi.val → h.ins.val[j]? = some false) →
    lines.hist a b h (alo, ahi) (blo, bhi) depth ⦃ h' => HOut a b n h alo.val ahi.val blo.val bhi.val h' ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro h alo ahi blo bhi depth hNN hlo hahi hblo hbhi hs hcl hD hI
  rw [lines.hist.eq_1]
  step as ⟨s, hsv, hsl⟩
  step as ⟨s1, hs1v, hs1l⟩
  have hsL : s.val.length = ahi.val - alo.val := hsl
  have hs1L : s1.val.length = bhi.val - blo.val := hs1l
  step with common_prefix_u32 s s1 as ⟨p2, hp2a, hp2b, hp2c⟩
  have hp2v : p2.val ≤ ahi.val - alo.val ∧ p2.val ≤ bhi.val - blo.val := by omega
  step as ⟨alo1, halo1⟩
  step as ⟨blo1, hblo1⟩
  step as ⟨s2, hs2v, hs2l⟩
  step as ⟨s3, hs3v, hs3l⟩
  have hs2L : s2.val.length = ahi.val - alo1.val := hs2l
  have hs3L : s3.val.length = bhi.val - blo1.val := hs3l
  step with common_suffix_u32 s2 s3 as ⟨sfx, hsf1, hsf2, hsf3⟩
  have hsfv : sfx.val ≤ ahi.val - alo1.val ∧ sfx.val ≤ bhi.val - blo1.val := by omega
  have hsfa : sfx.val ≤ ahi.val := by omega
  have hsfb : sfx.val ≤ bhi.val := by omega
  step as ⟨ahi1, hahi1⟩
  step as ⟨bhi1, hbhi1⟩
  have hq1 : alo.val ≤ alo1.val ∧ alo1.val ≤ ahi1.val ∧ ahi1.val ≤ ahi.val := by omega
  have hq2 : blo.val ≤ blo1.val ∧ blo1.val ≤ bhi1.val ∧ bhi1.val ≤ bhi.val := by omega
  have hPu : Myers.sg a.val alo.val alo1.val = Myers.sg b.val blo.val blo1.val := by
    have := hp2b
    rw [hsv, hs1v] at this
    change List.take _ (Myers.sg a.val alo.val ahi.val) = List.take _ (Myers.sg b.val blo.val bhi.val) at this
    rw [Myers.sg_take _ _ _ _ (by omega), Myers.sg_take _ _ _ _ (by omega)] at this
    rw [halo1, hblo1]; exact this
  have hSu : Myers.sg a.val ahi1.val ahi.val = Myers.sg b.val bhi1.val bhi.val := by
    have := hsf2
    rw [hs2L, hs3L, hs2v, hs3v] at this
    change List.drop _ (Myers.sg a.val alo1.val ahi.val) = List.drop _ (Myers.sg b.val blo1.val bhi.val) at this
    rw [Myers.sg_drop _ _ _ _ (by omega), Myers.sg_drop _ _ _ _ (by omega)] at this
    rwa [show alo1.val + (ahi.val - alo1.val - sfx.val) = ahi1.val by omega,
      show blo1.val + (bhi.val - blo1.val - sfx.val) = bhi1.val by omega] at this
  have hP : Myers.sg (vals a.val) alo.val alo1.val = Myers.sg (vals b.val) blo.val blo1.val := by
    rw [← vals_sg, ← vals_sg, hPu]
  have hS : Myers.sg (vals a.val) ahi1.val ahi.val = Myers.sg (vals b.val) bhi1.val bhi.val := by
    rw [← vals_sg, ← vals_sg, hSu]
  have hpp : blo1.val = blo.val + (alo1.val - alo.val) := by omega
  have hvl : (vals a.val).length = a.val.length := vals_len _
  have hvlb : (vals b.val).length = b.val.length := vals_len _
  refine Aeneas.Std.WP.spec_mono (P₁ := fun h' => HOut a b n h alo1.val ahi1.val blo1.val bhi1.val h') ?_ ?_
  swap
  · intro h' hh
    obtain ⟨hs', hc', hp⟩ := hh
    refine ⟨hs', hc', ?_⟩
    exact Myers.hp_wrap hq1.1 hq1.2.1 hq1.2.2 (by omega) hq2.1 hq2.2.1 hq2.2.2 (by omega) hpp hP hS
      (by rw [hs.del]; omega) (by rw [hs.ins]; omega) (fun j h1 h2 => hD j h1 h2) (fun j h1 h2 => hI j h1 h2) hp
  have hDl : ahi1.val ≤ h.del.val.length := by rw [hs.del]; omega
  have hIl : bhi1.val ≤ h.ins.val.length := by rw [hs.ins]; omega
  have hD1 : ∀ i, alo1.val ≤ i → i < ahi1.val → h.del.val[i]? = some false := fun i h1 h2 => hD i (by omega) (by omega)
  have hI1 : ∀ j, blo1.val ≤ j → j < bhi1.val → h.ins.val[j]? = some false := fun j h1 h2 => hI j (by omega) (by omega)
  by_cases hc1 : alo1 = ahi1
  · rw [if_pos hc1]
    sorry
  · rw [if_neg hc1]
    by_cases hc2 : blo1 = bhi1
    · rw [if_pos hc2]
      sorry
    · rw [if_neg hc2]
      by_cases hc3 : depth ≥ lines.HIST_DEPTH
      · rw [if_pos hc3]
        sorry
      · rw [if_neg hc3]
        sorry

end difffold_myers_extract
