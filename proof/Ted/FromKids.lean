import DifffoldTed
import Basic
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_lines_extract

/-! Theorems over the Aeneas-extraction of the real `PostTree::from_kids` of `src/ted.rs` (included by `#[path]`).

Postorder with 0-based nodes `0 .. n-1`. `kids[j]` lists the children of node `j`, all smaller than `j`.
The first child of `j`, if any, is `FirstKid kids j`. The leftmost leaf of `j` (1-based, as stored) satisfies
`lml[j] = j + 1` for a leaf and `lml[j] = lml[first child]` otherwise (`LmlEq`); because the first child is
smaller than `j`, these equations determine `lml` uniquely. The keyroots are the 1-based nodes that are the
last node (in postorder) with their leftmost leaf. -/

/-- The first child of node `j`, if it has one. -/
def FirstKid (kids : List (alloc.vec.Vec Std.U32)) (j : Nat) : Option Std.U32 :=
  (kids[j]?).bind (fun v => v.val.head?)

/-- The defining equation of the leftmost leaf of node `j` (1-based values). -/
def LmlEq (kids : List (alloc.vec.Vec Std.U32)) (L : List Std.U32) (j : Nat) : Prop :=
  match FirstKid kids j with
  | none => (L[j]!).val = j + 1
  | some k => (L[j]!).val = (L[k.val]!).val

/-- Node `v` (1-based) is the last node whose leftmost leaf is `L[v-1]`. -/
def LastWithLml (L : List Std.U32) (n v : Nat) : Prop :=
  1 ≤ v ∧ v ≤ n ∧ ∀ j, v - 1 < j → j < n → (L[j]!).val ≠ (L[v-1]!).val


theorem getb_set_eq (l : List Std.U32) (i : Nat) (x : Std.U32) (h : i < l.length) :
    (l.set i x)[i]! = x := by
  simp [h]

theorem getb_set_ne (l : List Std.U32) (i j : Nat) (x : Std.U32) (h : j ≠ i) :
    (l.set i x)[j]! = l[j]! := by
  simp [Ne.symm h]

theorem firstKid_get (kids : List (alloc.vec.Vec Std.U32)) (c : Nat) (h : c < kids.length) :
    FirstKid kids c = (kids[c]'h).val.head? := by
  simp [FirstKid, List.getElem?_eq_getElem h]

/-- Writing at a later node does not disturb the equation of an earlier node. -/
theorem lmlEq_set (kids : List (alloc.vec.Vec Std.U32)) (o : List Std.U32) (c j : Nat) (x : Std.U32)
    (hj : j < c) (hv : ∀ k, FirstKid kids j = some k → k.val < j) (h : LmlEq kids o j) :
    LmlEq kids (o.set c x) j := by
  unfold LmlEq at *
  rcases hfk : FirstKid kids j with _ | k
  · rw [hfk] at h; simp only at h ⊢
    rw [getb_set_ne _ _ _ _ (by omega)]; exact h
  · rw [hfk] at h; simp only at h ⊢
    have := hv k hfk
    rw [getb_set_ne _ _ _ _ (by omega), getb_set_ne _ _ _ _ (by omega)]; exact h

theorem cast_u32_of_lt (c : Std.Usize) (h : c.val < 2 ^ 31) : (UScalar.cast .U32 c).val = c.val := by
  rw [UScalar.cast_val_eq]
  simp only [UScalarTy.numBits]
  apply Nat.mod_eq_of_lt
  omega

/-- Loop 1 fills `lml` in increasing order of node. -/
@[step] theorem from_kids_lml_loop_spec (kids : Slice (alloc.vec.Vec Std.U32)) (n : Std.Usize)
    (lml : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (hn : n.val < 2 ^ 31) (hk : n.val ≤ kids.val.length) (hlen : lml.length = n.val)
    (hvalid : ∀ j < n.val, ∀ k, FirstKid kids.val j = some k → k.val < j)
    (hi : i.val ≤ n.val)
    (hinv : ∀ j < i.val, LmlEq kids.val lml.val j ∧ 1 ≤ (lml.val[j]!).val ∧ (lml.val[j]!).val ≤ j + 1) :
    ted.PostTree.from_kids_loop0 kids n lml i ⦃ r => r.length = n.val ∧
      ∀ j < n.val, LmlEq kids.val r.val j ∧ 1 ≤ (r.val[j]!).val ∧ (r.val[j]!).val ≤ j + 1 ⦄ := by
  unfold ted.PostTree.from_kids_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - p.2.val)
    (inv := fun p => p.2.val ≤ n.val ∧ p.1.length = n.val ∧
      ∀ j < p.2.val, LmlEq kids.val p.1.val j ∧ 1 ≤ (p.1.val[j]!).val ∧ (p.1.val[j]!).val ≤ j + 1)
  · intro p hp
    obtain ⟨o, c⟩ := p
    obtain ⟨hc, hl, hinv'⟩ := hp
    unfold ted.PostTree.from_kids_loop0.body
    dsimp only at hc hl hinv' ⊢
    split
    · rename_i hlt
      have hcn : c.val < n.val := by scalar_tac
      have hkc : c.val < kids.val.length := by omega
      step as ⟨v, v_post⟩
      have hfk : FirstKid kids.val c.val = v.val.head? := by
        rw [firstKid_get _ _ hkc, v_post]
      have hvl : (alloc.vec.Vec.len v).val = v.val.length := alloc.vec.Vec.len_val v
      split
      · rename_i hleaf
        have h0 : v.val.length = 0 := by rw [hleaf] at hvl; simpa using hvl.symm
        have hnone : FirstKid kids.val c.val = none := by
          rw [hfk]; rw [List.length_eq_zero_iff] at h0; simp [h0]
        step as ⟨x, x_post⟩
        have hx : x.val = c.val := by rw [x_post]; exact cast_u32_of_lt c (by omega)
        step as ⟨v1, v1_post⟩
        step as ⟨old, index_mut_back, old_post, index_mut_back_post⟩
        step as ⟨i2, i2_post⟩
        have hvv : v1.val = c.val + 1 := by omega
        have hset : (index_mut_back v1).val = o.val.set c.val v1 := by
          rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
        have hol : c.val < o.val.length := by have : o.val.length = n.val := hl; omega
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hl
        · intro j hj
          rw [hset]
          by_cases hjc : j = c.val
          · subst hjc
            rw [getb_set_eq _ _ _ hol]
            refine ⟨?_, by omega, by omega⟩
            unfold LmlEq; rw [hnone]; simp only; rw [getb_set_eq _ _ _ hol, hvv]
          · have hjc' : j < c.val := by scalar_tac
            have := hinv' j hjc'
            refine ⟨lmlEq_set _ _ _ _ _ hjc' (hvalid j (by omega)) this.1, ?_, ?_⟩
            · rw [getb_set_ne _ _ _ _ (by omega)]; exact this.2.1
            · rw [getb_set_ne _ _ _ _ (by omega)]; exact this.2.2
      · rename_i hnl
        have hne : v.val.length ≠ 0 := by
          intro h0; apply hnl; apply UScalar.eq_of_val_eq; rw [hvl, h0]; simp
        have hpos : 0 < v.val.length := Nat.pos_of_ne_zero hne
        step as ⟨k, k_post⟩
        have hk0 : FirstKid kids.val c.val = some k := by
          rw [hfk, k_post]
          obtain ⟨a, rest, ha⟩ := List.exists_cons_of_length_pos hpos
          simp [ha]
        have hklt : k.val < c.val := hvalid c.val hcn k hk0
        step as ⟨x, x_post⟩
        have hx : x.val = k.val := by rw [x_post]; exact U32.cast_Usize_val_eq k
        step as ⟨v1, v1_post⟩
        step as ⟨old, index_mut_back, old_post, index_mut_back_post⟩
        step as ⟨i2, i2_post⟩
        have hset : (index_mut_back v1).val = o.val.set c.val v1 := by
          rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
        have hol : c.val < o.val.length := by have : o.val.length = n.val := hl; omega
        have hv1 : v1 = o.val[k.val]! := by
          rw [v1_post]; simp [List.getElem!_eq_getElem?_getD, hx, List.getElem?_eq_getElem (show k.val < o.val.length by omega)]
        have hkb := hinv' k.val hklt
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hl
        · intro j hj
          rw [hset]
          by_cases hjc : j = c.val
          · subst hjc
            rw [getb_set_eq _ _ _ hol]
            refine ⟨?_, ?_, ?_⟩
            · unfold LmlEq; rw [hk0]; simp only
              rw [getb_set_eq _ _ _ hol, getb_set_ne _ _ _ _ (by omega), hv1]
            · rw [hv1]; exact hkb.2.1
            · rw [hv1]; have := hkb.2.2; omega
          · have hjc' : j < c.val := by scalar_tac
            have := hinv' j hjc'
            refine ⟨lmlEq_set _ _ _ _ _ hjc' (hvalid j (by omega)) this.1, ?_, ?_⟩
            · rw [getb_set_ne _ _ _ _ (by omega)]; exact this.2.1
            · rw [getb_set_ne _ _ _ _ (by omega)]; exact this.2.2
    · rename_i hnot
      refine ⟨hl, fun j hj => hinv' j (by scalar_tac)⟩
  · exact ⟨hi, hlen, hinv⟩


/-- `v` occurs in the list of keyroots. -/
def InKR (K : List Std.U32) (v : Nat) : Prop := ∃ r ∈ K, r.val = v

theorem getb_eq (l : List Std.U32) (i : Nat) (h : i < l.length) : l[i]! = l[i]'h := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getb_eq' (l : List Bool) (i : Nat) (h : i < l.length) : l[i]! = l[i]'h := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getbB_set_eq (l : List Bool) (i : Nat) (x : Bool) (h : i < l.length) :
    (l.set i x)[i]! = x := by
  simp [h]

theorem getbB_set_ne (l : List Bool) (i j : Nat) (x : Bool) (h : j ≠ i) :
    (l.set i x)[j]! = l[j]! := by
  simp [Ne.symm h]

/-- Loop 3 walks the nodes from the last to the first and records the first one met for each leftmost leaf
(that is, the last one in postorder), newest last. -/
@[step] theorem from_kids_keyroot_loop_spec (lml : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (seen : alloc.vec.Vec Bool) (keyroots : alloc.vec.Vec Std.U32)
    (hN : lml.length < 2 ^ 31) (hbd : ∀ j < lml.length, 1 ≤ (lml.val[j]!).val ∧ (lml.val[j]!).val ≤ j + 1)
    (hi : i.val ≤ lml.length) (hs : seen.length = lml.length + 2)
    (hseen : ∀ l < seen.length, seen.val[l]! = true ↔
      ∃ j, i.val ≤ j ∧ j < lml.length ∧ (lml.val[j]!).val = l)
    (hsort : keyroots.val.Pairwise (fun a b => b.val < a.val))
    (hkr : ∀ v, InKR keyroots.val v ↔ i.val + 1 ≤ v ∧ LastWithLml lml.val lml.length v)
    (hKl : keyroots.length + i.val ≤ lml.length) :
    ted.PostTree.from_kids_loop1 lml i seen keyroots ⦃ r =>
      r.val.Pairwise (fun a b => b.val < a.val) ∧ ∀ v, InKR r.val v ↔ LastWithLml lml.val lml.length v ⦄ := by
  unfold ted.PostTree.from_kids_loop1
  apply loop.spec_decr_nat
    (measure := fun p => p.1.val)
    (inv := fun p => p.1.val ≤ lml.length ∧ p.2.1.length = lml.length + 2 ∧
      (∀ l < p.2.1.length, p.2.1.val[l]! = true ↔ ∃ j, p.1.val ≤ j ∧ j < lml.length ∧ (lml.val[j]!).val = l) ∧
      p.2.2.val.Pairwise (fun a b => b.val < a.val) ∧
      (∀ v, InKR p.2.2.val v ↔ p.1.val + 1 ≤ v ∧ LastWithLml lml.val lml.length v) ∧
      p.2.2.length + p.1.val ≤ lml.length)
  · intro p hp
    obtain ⟨c, o, K⟩ := p
    obtain ⟨hc, hl, hse, hso, hk, hKl'⟩ := hp
    unfold ted.PostTree.from_kids_loop1.body
    dsimp only at hc hl hse hso hk hKl' ⊢
    split
    · rename_i hpos
      step as ⟨i1, i1_post⟩
      step as ⟨e, e_post⟩
      step as ⟨l, l_post⟩
      have hi1 : i1.val < lml.length := by omega
      have hel : e.val = (lml.val[i1.val]!).val := by rw [e_post, getb_eq _ _ hi1]
      have hlv : l.val = e.val := by rw [l_post]; exact U32.cast_Usize_val_eq e
      have hbe := hbd i1.val hi1
      have hll : l.val < o.length := by omega
      step as ⟨b, b_post⟩
      have hb : b = o.val[l.val]! := by rw [b_post, ← getb_eq' o.val l.val hll]
      have hc1 : c.val = i1.val + 1 := by scalar_tac
      split
      · rename_i hbt
        have hbt' : o.val[l.val]! = true := by rw [← hb]; exact hbt
        obtain ⟨j0, hj0a, hj0b, hj0c⟩ := (hse l.val (by omega)).mp hbt'
        simp only [WP.spec_ok]
        refine ⟨?_, hl, ?_, hso, ?_, by omega, by omega⟩
        · omega
        · intro l' hl'
          rw [hse l' hl']
          constructor
          · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, by omega, h2, h3⟩
          · rintro ⟨j, h1, h2, h3⟩
            by_cases hj : j = i1.val
            · subst hj
              have : l' = l.val := by rw [← h3, hlv, hel]
              subst this
              exact ⟨j0, hj0a, hj0b, hj0c⟩
            · exact ⟨j, by omega, h2, h3⟩
        · intro v
          rw [hk v]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
          · rintro ⟨h1, h2⟩
            by_cases hv : v = i1.val + 1
            · exfalso
              subst hv
              have := h2.2.2 j0 (by omega) hj0b
              apply this
              rw [hj0c, hlv, hel]; simp
            · exact ⟨by omega, h2⟩
      · rename_i hbf
        have hbf' : o.val[l.val]! = false := by rw [← hb]; simpa using hbf
        have hno : ¬ ∃ j, c.val ≤ j ∧ j < lml.length ∧ (lml.val[j]!).val = l.val := by
          intro h
          have := (hse l.val (by omega)).mpr h
          rw [hbf'] at this; exact absurd this (by simp)
        step as ⟨old, imb, old_post, imb_post⟩
        step as ⟨i3, i3_post⟩
        have hi3 : i3.val = i1.val := by rw [i3_post]; exact cast_u32_of_lt i1 (by omega)
        step as ⟨i4, i4_post⟩
        step as ⟨K1, K1_post⟩
        have hset : (imb true).val = o.val.set l.val true := by
          rw [imb_post, alloc.vec.Vec.set_val_eq]
        have hK1len : K1.length = K.length + 1 := by simp [alloc.vec.Vec.length, K1_post]
        refine ⟨?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
        · omega
        · simp only [alloc.vec.Vec.length, hset, List.length_set]; exact hl
        · intro l' hl'
          simp only [alloc.vec.Vec.length, hset, List.length_set] at hl'
          simp only [hset]
          by_cases hll' : l' = l.val
          · subst hll'
            rw [getbB_set_eq _ _ _ hll]
            simp only [true_iff]
            exact ⟨i1.val, le_refl _, hi1, by rw [hlv, hel]⟩
          · rw [getbB_set_ne _ _ _ _ hll', hse l' (by omega)]
            constructor
            · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, by omega, h2, h3⟩
            · rintro ⟨j, h1, h2, h3⟩
              by_cases hj : j = i1.val
              · subst hj; exfalso; apply hll'; rw [← h3, hlv, hel]
              · exact ⟨j, by omega, h2, h3⟩
        · rw [K1_post, List.pairwise_append]
          refine ⟨hso, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb'
          have hbb : b = i4 := List.mem_singleton.mp hb'
          have := (hk a.val).mp ⟨a, ha, rfl⟩
          have h4 : i4.val = i1.val + 1 := by omega
          rw [hbb]
          omega
        · intro v
          have h4 : i4.val = i1.val + 1 := by omega
          constructor
          · rintro ⟨r, hr, hrv⟩
            rw [K1_post, List.mem_append] at hr
            rcases hr with hr | hr
            · have := (hk v).mp ⟨r, hr, hrv⟩
              exact ⟨by omega, this.2⟩
            · have hr' : r = i4 := List.mem_singleton.mp hr
              have hv : v = i1.val + 1 := by rw [← hrv, hr']; exact h4
              subst hv
              refine ⟨by omega, by omega, by omega, ?_⟩
              intro j hj1 hj2 hj3
              apply hno
              have e1 : i1.val + 1 - 1 = i1.val := by omega
              rw [e1] at hj3
              exact ⟨j, by omega, hj2, by rw [hlv, hel]; exact hj3⟩
          · rintro ⟨h1, h2⟩
            by_cases hv : v = i1.val + 1
            · exact ⟨i4, by rw [K1_post]; simp, by omega⟩
            · obtain ⟨r, hr, hrv⟩ := (hk v).mpr ⟨by omega, h2⟩
              exact ⟨r, by rw [K1_post]; simp [hr], hrv⟩
    · rename_i hnot
      simp only [WP.spec_ok]
      refine ⟨hso, fun v => ?_⟩
      rw [hk v]
      have : c.val = 0 := by scalar_tac
      rw [this]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨by have := h.1; omega, h⟩
  · exact ⟨hi, hs, hseen, hsort, hkr, hKl⟩


/-- `PostTree::from_kids` computes the leftmost-leaf table and the keyroot list.
* `lml` satisfies the defining equation of the leftmost leaf at every node, with values in `1 .. j + 1`;
* the keyroots are strictly ascending, and a 1-based `v` is a keyroot exactly when it is the last node of the
  postorder whose leftmost leaf is that of `v`.
Hypotheses: fewer than `2^31` nodes (the casts and `+ 1` do not overflow), a child list for every node, and
the first child of each node precedes the node (the postorder property; the proof never reads the other
children). -/
theorem from_kids_spec (label : alloc.vec.Vec Std.U32) (kids : Slice (alloc.vec.Vec Std.U32))
    (hn : label.length < 2 ^ 31) (hk : label.length ≤ kids.val.length)
    (hvalid : ∀ j < label.length, ∀ k, FirstKid kids.val j = some k → k.val < j) :
    ted.PostTree.from_kids label kids ⦃ t =>
      t.label = label ∧ t.lml.length = label.length ∧
      (∀ j < label.length, LmlEq kids.val t.lml.val j ∧ 1 ≤ (t.lml.val[j]!).val ∧ (t.lml.val[j]!).val ≤ j + 1) ∧
      t.keyroots.val.Pairwise (fun a b => a.val < b.val) ∧
      (∀ v, InKR t.keyroots.val v ↔ LastWithLml t.lml.val label.length v) ∧
      t.kids.val = kids.val ∧ t.kind.val = List.replicate label.length 0#u32 ⦄ := by
  unfold ted.PostTree.from_kids
  have hlenv := alloc.vec.Vec.len_val label
  step*
  · intro l hl
    have hf : seen.val[l]! = false := by
      have h1 : l < seen.val.length := hl
      rw [seen_post]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
      split <;> simp
    rw [hf]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨j, h1, h2, _⟩; omega
  · simp [alloc.vec.Vec.new]
  · intro v
    constructor
    · rintro ⟨r, hr, _⟩
      simp [alloc.vec.Vec.new] at hr
    · rintro ⟨h1, h2⟩
      have := h2.2.1
      have hl := alloc.vec.Vec.len_val label
      omega
  · have hrev : (({ slice := core.slice.Slice.reverse keyroots.slice } : alloc.vec.Vec Std.U32)).val
        = keyroots.val.reverse := by
      simp [core.slice.Slice.reverse, alloc.vec.Vec.val]
    have hlen := alloc.vec.Vec.len_val label
    simp only [lift, bind_tc_ok, alloc.vec.Vec.deref_mut]
    step*
    · intro x _; exact clone_vec_u32 x
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have := lml1_post1 j (by omega)
      exact this
    · simp only [hrev, List.pairwise_reverse]
      exact keyroots_post
    · intro v
      have := keyroots_post1 v
      simp only [hrev, InKR, List.mem_reverse] at this ⊢
      rw [this]
      simp only [LastWithLml, lml1_post]
      rw [hlen]
    · rw [kids_post]; rfl
    · rw [kind_post, hlen]

end difffold_lines_extract
