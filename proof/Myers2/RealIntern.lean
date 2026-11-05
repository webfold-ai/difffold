import DifffoldReal
import InternExact
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-! The interner of `src/lines.rs` (`intern_seeded` and its helpers) over the Aeneas translation of the real
source. `InternExact` (file `InternExact.lean`) is proved for `intern_seeded`, whose only difference from the
shipped `intern` is that the hash seed is a parameter (`intern` passes a fresh random seed). The hash is
total (no failure) and otherwise irrelevant to correctness: it only picks a bucket, lines are compared by
their bytes. -/

/-! ### The hash is total -/

@[step]
theorem lift_spec_i {α : Type} (x : α) : lift x ⦃ y => y = x ⦄ := by simp [lift]

@[step]
theorem hash_loop0_total (l : Slice U8) (h : U64) (i : Usize) (hi : i.val ≤ l.val.length) :
    lines.hash_line_loop0 l h i ⦃ r => r.2.val ≤ l.val.length ⦄ := by
  unfold lines.hash_line_loop0
  apply loop.spec_decr_nat (fun (x : U64 × Usize) => l.val.length - x.2.val)
    (fun (x : U64 × Usize) => x.2.val ≤ l.val.length) _ _ (h, i)
  · rintro ⟨h1, i1⟩ hinv
    simp only at hinv
    unfold lines.hash_line_loop0.body
    step*
    all_goals (try scalar_tac)
  · exact hi

@[step]
theorem hash_loop1_total (l : Slice U8) (i : Usize) (acc : U64) (hi : i.val ≤ l.val.length) :
    lines.hash_line_loop1 l i acc ⦃ r => True ⦄ := by
  unfold lines.hash_line_loop1
  apply loop.spec_decr_nat (fun (x : Usize × U64) => l.val.length - x.1.val)
    (fun (x : Usize × U64) => x.1.val ≤ l.val.length) _ _ (i, acc)
  · rintro ⟨i1, a1⟩ hinv
    simp only at hinv
    unfold lines.hash_line_loop1.body
    step*
    all_goals (try scalar_tac)
  · exact hi

/-- The hash never fails. -/
theorem hash_line_total (seed : U64) (l : Slice U8) : lines.hash_line seed l ⦃ h => True ⦄ := by
  unfold lines.hash_line
  step*

/-- The hash of a line, which is all that is known (and needed) about it. -/
noncomputable def hashOf (seed : U64) (l : Slice U8) : U64 :=
  Classical.epsilon (fun h : U64 => lines.hash_line seed l = ok h)

theorem hash_line_eq (seed : U64) (l : Slice U8) : lines.hash_line seed l = ok (hashOf seed l) := by
  have h := hash_line_total seed l
  rw [WP.spec_equiv_exists] at h
  obtain ⟨y, hy, _⟩ := h
  have hex : ∃ h : U64, lines.hash_line seed l = ok h := ⟨y, hy⟩
  exact Classical.epsilon_spec hex

/-! ### `table_size` -/

theorem table_size_loop_spec (total : Usize) (hT : total.val ≤ 2 ^ 28) (cap : Usize) (hc : 2 ≤ cap.val)
    (hc2 : cap.val ≤ 2 ^ 28 ∨ total.val ≤ cap.val) :
    lines.table_size_loop total cap ⦃ r => 2 ≤ r.val ∧ total.val ≤ r.val ⦄ := by
  unfold lines.table_size_loop
  apply loop.spec_decr_nat (fun (x : Usize) => total.val - x.val)
    (fun (x : Usize) => 2 ≤ x.val ∧ (x.val ≤ 2 ^ 28 ∨ total.val ≤ x.val)) _ _ cap
  · intro x hx
    unfold lines.table_size_loop.body
    step*
    all_goals (try scalar_tac)
  · exact ⟨hc, hc2⟩

theorem table_size_spec (total : Usize) (hT : total.val ≤ 2 ^ 28) :
    lines.table_size total ⦃ r => 2 ≤ r.val ∧ total.val ≤ r.val ⦄ := by
  unfold lines.table_size
  exact table_size_loop_spec total hT 2#usize (by simp) (Or.inl (by simp))

/-! ### The chain structure -/

theorem NIL_val : lines.NIL.val = 4294967295 := by
  simp [lines.NIL, core.num.U32.MAX]
  rfl

/-- `InChain nxt s k`: following the links `nxt` from `s` (stopping at the end marker `NIL`) reaches the id `k`. -/
inductive InChain (nxt : List U32) : U32 → Nat → Prop
  | refl (s : U32) (k : Nat) : s.val = k → InChain nxt s k
  | step (s s' : U32) (k : Nat) : s ≠ lines.NIL → nxt[s.val]? = some s' → InChain nxt s' k → InChain nxt s k

/-- Slice equality on bytes. -/
theorem slice_u8_eq (s l : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s l ⦃ b => b = true ↔ s = l ⦄ :=
  core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 s l (by intro x y; simp [liftFun2])

theorem find_in_chain_spec (reps : alloc.vec.Vec (Slice U8)) (nxt : alloc.vec.Vec U32) (l : Slice U8)
    (hn : reps.val.length < lines.NIL.val) (hnl : nxt.val.length = reps.val.length)
    (hnx : ∀ i (hi : i < nxt.val.length), nxt.val[i] = lines.NIL ∨ (nxt.val[i]).val < i) :
    ∀ (N : Nat) (k : U32), (k = lines.NIL ∨ k.val < reps.val.length) →
    (if k = lines.NIL then 0 else k.val + 1) ≤ N →
    lines.find_in_chain reps nxt k l ⦃ r =>
      (r = lines.NIL ∧ ∀ j, InChain nxt.val k j → reps.val[j]? ≠ some l) ∨
      (r ≠ lines.NIL ∧ r.val < reps.val.length ∧ reps.val[r.val]? = some l) ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro k hk hN
  rw [lines.find_in_chain.eq_1]
  by_cases hkn : k = lines.NIL
  · subst hkn
    simp only [if_true]
    simp only [WP.spec_ok, true_and, ne_eq, not_true, false_and, or_false]
    intro j hj
    cases hj with
    | refl _ _ hv =>
      have : reps.val[j]? = none := by
        rw [List.getElem?_eq_none_iff]; rw [NIL_val] at hv; rw [NIL_val] at hn; omega
      simp [this]
    | step _ _ _ hne _ _ => exact absurd rfl hne
  · have hkl : k.val < reps.val.length := by
      rcases hk with h | h
      · exact absurd h hkn
      · exact h
    rw [if_neg hkn]
    simp only [if_neg hkn] at hN
    step as ⟨i, hi⟩
    have hiv : i.val = k.val := by rw [hi]; simp
    step as ⟨s, hs⟩
    have hsk : reps.val[k.val]? = some s := by
      rw [hs]; simp only [hiv]; exact List.getElem?_eq_getElem hkl
    step with slice_u8_eq s l as ⟨b, hb⟩
    split
    · rename_i hbt
      simp only [WP.spec_ok]
      right
      refine ⟨hkn, hkl, ?_⟩
      rw [hsk]; simp [hb.mp hbt]
    · rename_i hbf
      have hbf' : ¬ s = l := fun h => hbf (hb.mpr h)
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = k.val := by rw [hi1]; simp
      have hk2 : k.val < nxt.val.length := by omega
      step as ⟨i2, hi2⟩
      have hi2' : nxt.val[k.val]? = some i2 := by
        rw [hi2]; simp only [hi1v]; exact List.getElem?_eq_getElem hk2
      have hnk := hnx k.val hk2
      have hi2g : nxt.val[k.val] = i2 := by
        have := hi2'; rw [List.getElem?_eq_getElem hk2] at this; exact Option.some.inj this
      rw [hi2g] at hnk
      have hmeas : (if i2 = lines.NIL then 0 else i2.val + 1) < N := by
        by_cases h2 : i2 = lines.NIL
        · simp only [h2, if_true]; omega
        · simp only [h2, if_false]; rcases hnk with h | h
          · exact absurd h h2
          · omega
      have hb2 : i2 = lines.NIL ∨ i2.val < reps.val.length := by
        rcases hnk with h | h
        · left; exact h
        · right; omega
      have key := ih _ hmeas i2 hb2 le_rfl
      refine Aeneas.Std.WP.spec_mono key ?_
      intro r hr
      rcases hr with ⟨hr1, hr2⟩ | hr
      · left
        refine ⟨hr1, ?_⟩
        intro j hj
        cases hj with
        | refl _ _ hv =>
          rw [← hv, hsk]; intro h; exact hbf' (Option.some.inj h)
        | step _ s'' _ _ hst hrest =>
          rw [hi2'] at hst
          have : s'' = i2 := (Option.some.inj hst).symm
          subst this
          exact hr2 j hrest
      · right; exact hr

@[step]
theorem hash_line_spec (seed : U64) (l : Slice U8) : lines.hash_line seed l ⦃ h => h = hashOf seed l ⦄ := by
  rw [hash_line_eq]; simp

/-- The bucket of a line in a table of `L` buckets. -/
noncomputable def bkNat (seed : U64) (L : Nat) (l : Slice U8) : Nat :=
  (UScalar.cast .Usize (hashOf seed l)).val &&& (L - 1)

theorem bkNat_lt (seed : U64) (L : Nat) (l : Slice U8) (hL : 1 ≤ L) : bkNat seed L l < L := by
  unfold bkNat
  have := Nat.and_le_right (n := (UScalar.cast .Usize (hashOf seed l)).val) (m := L - 1)
  omega

/-- The invariant of the interner state: a table of `head.length` buckets, `nxt` the older-id links, `reps`
the distinct lines seen so far (an id is a position in `reps`). -/
structure TInv (seed : U64) (head nxt : List U32) (reps : List (Slice U8)) : Prop where
  hpos : 1 ≤ head.length
  hnl : nxt.length = reps.length
  hhd : ∀ x ∈ head, x = lines.NIL ∨ x.val < reps.length
  hnx : ∀ (i : Nat) s, nxt[i]? = some s → s = lines.NIL ∨ s.val < i
  hrc : ∀ (k : Nat) r, reps[k]? = some r → ∃ b, head[bkNat seed head.length r]? = some b ∧ InChain nxt b k
  hds : ∀ (i j : Nat) r, reps[i]? = some r → reps[j]? = some r → i = j

theorem InChain_ext {nxt nxt' : List U32} (hext : nxt <+: nxt') {s : U32} {k : Nat}
    (h : InChain nxt s k) : InChain nxt' s k := by
  induction h with
  | refl s k hv => exact InChain.refl _ _ hv
  | step s s' k hne hst _ ih =>
    refine InChain.step s s' k hne ?_ ih
    obtain ⟨t, rfl⟩ := hext
    have hlt : s.val < nxt.length := by
      by_contra hh; rw [List.getElem?_eq_none (by omega)] at hst; simp at hst
    rw [List.getElem?_append_left hlt]; exact hst

theorem tinv_push (seed : U64) (head nxt : List U32) (reps : List (Slice U8)) (l : Slice U8) (b : Nat)
    (i4 i6 : U32) (hI : TInv seed head nxt reps) (hbv : b = bkNat seed head.length l) (hbl : b < head.length)
    (hi4 : head[b]? = some i4) (hi6 : i6.val = reps.length) (hn : reps.length < 2 ^ 28)
    (hkl : ∀ j, InChain nxt i4 j → reps[j]? ≠ some l) :
    TInv seed (head.set b i6) (nxt ++ [i4]) (reps ++ [l]) := by
  have hNb : (lines.NIL).val = 4294967295 := NIL_val
  have hnl := hI.hnl
  have hhd4 : i4 = lines.NIL ∨ i4.val < reps.length := hI.hhd i4 (List.mem_of_getElem? hi4)
  have hext : nxt <+: nxt ++ [i4] := List.prefix_append _ _
  have hlen : (head.set b i6).length = head.length := by simp
  refine ⟨by rw [hlen]; exact hI.hpos, by simp [hI.hnl], ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with h | h
    · rcases hI.hhd x h with h' | h'
      · exact Or.inl h'
      · right; simp; omega
    · right; simp [h, hi6]
  · intro i s hs
    by_cases hi : i < nxt.length
    · rw [List.getElem?_append_left hi] at hs
      rcases hI.hnx i s hs with h | h
      · exact Or.inl h
      · exact Or.inr h
    · have hin : i = nxt.length := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hs; simp at hs
      subst hin
      rw [List.getElem?_append_right (by omega)] at hs
      simp at hs
      subst hs
      rcases hhd4 with h | h
      · exact Or.inl h
      · right; rw [hI.hnl]; exact h
  · intro k r hk
    rw [hlen]
    by_cases hkn : k < reps.length
    · rw [List.getElem?_append_left hkn] at hk
      obtain ⟨b', hb', hch⟩ := hI.hrc k r hk
      have hch' : InChain (nxt ++ [i4]) b' k := InChain_ext hext hch
      by_cases hbb : bkNat seed head.length r = b
      · rw [hbb] at hb'
        have : b' = i4 := by rw [hi4] at hb'; exact (Option.some.inj hb').symm
        subst this
        refine ⟨i6, ?_, ?_⟩
        · rw [hbb, List.getElem?_set_self hbl]
        · refine InChain.step i6 b' k ?_ ?_ hch'
          · intro h; rw [h, hNb] at hi6; omega
          · rw [List.getElem?_append_right (by omega)]; simp [hi6, hI.hnl]
      · refine ⟨b', ?_, hch'⟩
        rw [List.getElem?_set_ne (Ne.symm hbb)]; exact hb'
    · have hk' : k = reps.length := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hk; simp at hk
      subst hk'
      rw [List.getElem?_append_right (by omega)] at hk
      simp at hk
      subst hk
      refine ⟨i6, ?_, InChain.refl _ _ hi6⟩
      rw [← hbv, List.getElem?_set_self hbl]
  · intro i j r hi hj
    by_cases hin : i < reps.length <;> by_cases hjn : j < reps.length
    · rw [List.getElem?_append_left hin] at hi
      rw [List.getElem?_append_left hjn] at hj
      exact hI.hds i j r hi hj
    · exfalso
      have hj' : j = reps.length := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hj; simp at hj
      subst hj'
      rw [List.getElem?_append_right (by omega)] at hj
      simp at hj
      subst hj
      rw [List.getElem?_append_left hin] at hi
      obtain ⟨b', hb', hch⟩ := hI.hrc i _ hi
      rw [← hbv] at hb'
      rw [hi4] at hb'
      have := Option.some.inj hb'
      subst this
      exact hkl i hch hi
    · exfalso
      have hi' : i = reps.length := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hi; simp at hi
      subst hi'
      rw [List.getElem?_append_right (by omega)] at hi
      simp at hi
      subst hi
      rw [List.getElem?_append_left hjn] at hj
      obtain ⟨b', hb', hch⟩ := hI.hrc j _ hj
      rw [← hbv] at hb'
      rw [hi4] at hb'
      have := Option.some.inj hb'
      subst this
      exact hkl j hch hj
    · have hi' : i = reps.length := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hi; simp at hi
      have hj' : j = reps.length := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hj; simp at hj
      omega

theorem intern_line_spec (head nxt : alloc.vec.Vec U32) (reps : alloc.vec.Vec (Slice U8)) (seed : U64)
    (l : Slice U8) (hI : TInv seed head.val nxt.val reps.val) (hn : reps.val.length < 2 ^ 28) :
    lines.intern_line head nxt reps seed l ⦃ id reps' head' nxt' =>
      id.val < reps'.val.length ∧ reps'.val[id.val]? = some l ∧ head'.val.length = head.val.length ∧
      TInv seed head'.val nxt'.val reps'.val ∧
      ((reps'.val = reps.val ∧ id.val < reps.val.length) ∨
        (reps'.val = reps.val ++ [l] ∧ id.val = reps.val.length)) ⦄ := by
  unfold lines.intern_line
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  have hpos := hI.hpos
  have hi2 : (alloc.vec.Vec.len head).val = head.val.length := by simp
  step as ⟨i3, hi3⟩
  step as ⟨bucket, hbk⟩
  have hi1v : i1 = UScalar.cast .Usize (hashOf seed l) := by rw [hi1, hi]
  have hbv : bucket.val = bkNat seed head.val.length l := by
    rw [hbk, UScalar.val_and]; unfold bkNat; rw [hi1v]; congr 1
  have hbl : bucket.val < head.val.length := by rw [hbv]; exact bkNat_lt _ _ _ hpos
  step as ⟨i4, hi4⟩
  have hi4g : head.val[bucket.val]? = some i4 := by rw [hi4]; exact List.getElem?_eq_getElem hbl
  have hhd4 : i4 = lines.NIL ∨ i4.val < reps.val.length := hI.hhd i4 (List.mem_of_getElem? hi4g)
  have hNb : reps.val.length < lines.NIL.val := by rw [NIL_val]; omega
  have hf := find_in_chain_spec reps nxt l hNb hI.hnl
    (fun i hi => hI.hnx i _ (List.getElem?_eq_getElem hi))
    (if i4 = lines.NIL then 0 else i4.val + 1) i4 hhd4 le_rfl
  step with hf as ⟨k, hk⟩
  by_cases hkn : k = lines.NIL
  · have hkl : ∀ j, InChain nxt.val i4 j → reps.val[j]? ≠ some l := by
      rcases hk with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd hkn h
    have hc : (k != lines.NIL) = false := by simp [hkn]
    rw [hc]
    simp only [Bool.false_eq_true, if_false]
    have hrn : reps.val.length < 2 ^ 28 := hn
    step as ⟨i5, hi5⟩
    have hrl : (alloc.vec.Vec.len reps).val = reps.val.length := by simp
    have hi5v : i5.val = 4294967295 := by rw [hi5, ← NIL_val]; simp
    have hm : reps.len < i5 := by
      rw [UScalar.lt_equiv]; omega
    have hm' : massert (reps.len < i5) = ok () := by simp [massert, hm]
    rw [hm']
    simp only [bind_tc_ok]
    have hnxl : nxt.val.length < Usize.max := by have := hI.hnl; scalar_tac
    have hrpl : reps.val.length < Usize.max := by scalar_tac
    step as ⟨nxt1, hnx1⟩
    step as ⟨x0, back, hx0, hback⟩
    step as ⟨i6, hi6⟩
    have hi6v : i6.val = reps.val.length := by rw [hi6]; simp; omega
    step as ⟨reps1, hr1⟩
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = reps.val.length := by rw [hk1]; simp; omega
    have hhead' : (back i6).val = head.val.set bucket.val i6 := by rw [hback]; simp [alloc.vec.Vec.set]
    have hbl' : bucket.val < head.val.length := hbl
    have hT := tinv_push seed head.val nxt.val reps.val l bucket.val i4 i6 hI hbv hbl' hi4g hi6v hn hkl
    rw [hhead', hr1, hnx1, hk1v]
    refine ⟨by simp, by simp, by simp, hT, Or.inr ⟨rfl, rfl⟩⟩
  · have hkr : k ≠ lines.NIL ∧ k.val < reps.val.length ∧ reps.val[k.val]? = some l := by
      rcases hk with ⟨h, _⟩ | h
      · exact absurd h hkn
      · exact h
    have hc : (k != lines.NIL) = true := by simpa using hkn
    rw [hc]
    simp only [if_true, WP.spec_ok]
    exact ⟨hkr.2.1, hkr.2.2, rfl, hI, Or.inl ⟨rfl, hkr.2.1⟩⟩

end difffold_myers_extract
