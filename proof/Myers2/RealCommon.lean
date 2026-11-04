import DifffoldReal
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-! Theorems over the Aeneas-extracted `lines::common_prefix` and `lines::common_suffix` (real `src/lines.rs`).
Generic in the element type: the only assumption is that the element `PartialEq` instance is lawful
(`eq` and `ne` return `x = y` and `x != y`). `common_prefix_u8` and `common_suffix_u8` discharge it for `u8`,
the instance `lines.rs` uses. -/

theorem minlen {T : Type} (a b : Slice T) :
    (core.cmp.impls.OrdUsize.min a.len b.len).val = min a.val.length b.val.length := by
  unfold core.cmp.impls.OrdUsize.min
  have h1 : a.len.val = a.val.length := by simp [Slice.len]
  have h2 : b.len.val = b.val.length := by simp [Slice.len]
  split
  · rename_i h; have : b.len.val < a.len.val := by scalar_tac
    omega
  · rename_i h; have : ¬ b.len.val < a.len.val := by scalar_tac
    omega

theorem common_prefix_aux {T : Type} (inst : core.cmp.PartialEq T T)
    (heq : ∀ x y, inst.eq x y ⦃ b => b = true ↔ x = y ⦄)
    (hne : ∀ x y, inst.ne x y ⦃ b => b = true ↔ ¬ x = y ⦄) :
    ∀ N : Nat, ∀ a b : Slice T, min a.val.length b.val.length = N →
    lines.common_prefix inst a b ⦃ l => l.val ≤ N ∧ a.val.take l.val = b.val.take l.val ∧
      (l.val = N ∨ ∃ x y, a.val[l.val]? = some x ∧ b.val[l.val]? = some y ∧ x ≠ y) ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a b hn
  rw [lines.common_prefix.eq_1]
  step*
  · -- the minimum is 0
    have hnv : n.val = N := by rw [n_post, minlen]; exact hn
    have : N = 0 := by scalar_tac
    subst this
    simp
  · -- the minimum is 1
    have hnv : n.val = N := by rw [n_post, minlen]; exact hn
    have hN : N = 1 := by scalar_tac
    subst hN
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_length_pos (l := a.val) (by omega)
    obtain ⟨y, ys, hy⟩ := List.exists_cons_of_length_pos (l := b.val) (by omega)
    simp [hx] at t_post
    simp [hy] at t1_post
    cases b1 with
    | true =>
      have : t = t1 := b1_post.mp rfl
      simp [core.convert.num.FromUsizeBool.from, hx, hy, ← t_post, ← t1_post, this]
    | false =>
      have : t ≠ t1 := fun h => by simpa using b1_post.mpr h
      simp [core.convert.num.FromUsizeBool.from, hx, hy]
      simp_all
  · -- halve
    have hnv : n.val = N := by rw [n_post, minlen]; exact hn
    have hN2 : 2 ≤ N := by scalar_tac
    have hh : h.val = N / 2 := by omega
    have hla : N ≤ a.val.length := by omega
    have hlb : N ≤ b.val.length := by omega
    have s_eq : s.val = a.val.take h.val := by simp [s_post, List.slice]
    have s1_eq : s1.val = b.val.take h.val := by simp [s1_post, List.slice]
    step with core.slice.cmp.PartialEqSlice.eq_homo_spec inst s s1 hne as ⟨b1, hb1⟩
    split
    · rename_i hb
      have heq' : a.val.take h.val = b.val.take h.val := by
        rw [← s_eq, ← s1_eq]; rw [hb1.mp hb]
      step as ⟨s2, s2_post, s2_post1⟩
      step as ⟨s3, s3_post, s3_post1⟩
      have s2_eq : s2.val = a.val.drop h.val := s2_post
      have s3_eq : s3.val = b.val.drop h.val := s3_post
      have hM : min s2.val.length s3.val.length = N - h.val := by
        rw [s2_eq, s3_eq]; simp; omega
      have hlt : N - h.val < N := by omega
      step with (ih (N - h.val) hlt s2 s3 hM) as ⟨i2, hi2a, hi2b, hi2c⟩
      step as ⟨r, r_post⟩
      have hr : r.val = h.val + i2.val := by scalar_tac
      refine ⟨by omega, ?_, ?_⟩
      · rw [hr, List.take_add, List.take_add, heq', ← s2_eq, ← s3_eq]
        rw [hi2b]
      · rcases hi2c with hc | ⟨x, y, hx, hy, hxy⟩
        · left; omega
        · right
          refine ⟨x, y, ?_, ?_, hxy⟩
          · rw [hr, ← List.getElem?_drop]; simpa [s2_eq, Nat.add_comm] using hx
          · rw [hr, ← List.getElem?_drop]; simpa [s3_eq, Nat.add_comm] using hy
    · rename_i hb
      have hM : min s.val.length s1.val.length = h.val := by
        rw [s_eq, s1_eq]; simp; omega
      have hlt : h.val < N := by omega
      step with (ih h.val hlt s s1 hM) as ⟨l, hla', hlb', hlc'⟩
      have hne' : s ≠ s1 := fun e => hb (hb1.mpr e)
      have hl1 : l.val ≤ h.val := hla'
      refine ⟨by omega, ?_, ?_⟩
      · have e1 := congrArg (List.take l.val) s_eq
        have e2 := congrArg (List.take l.val) s1_eq
        rw [List.take_take, Nat.min_eq_left hl1] at e1 e2
        rw [← e1, ← e2]; exact hlb'
      · rcases hlc' with hc | ⟨x, y, hx, hy, hxy⟩
        · exfalso
          apply hne'
          have hsl : s.val.length = h.val := by simp [s_eq]; omega
          have hsl1 : s1.val.length = h.val := by simp [s1_eq]; omega
          have h1 : List.take l.val s.val = s.val := by rw [hc, ← hsl]; exact List.take_length
          have h2 : List.take l.val s1.val = s1.val := by rw [hc, ← hsl1]; exact List.take_length
          rw [h1, h2] at hlb'
          rw [Slice.eq_iff]; exact hlb'
        · right
          have hlh : l.val < h.val := by
            by_contra hcon
            rw [s_eq] at hx
            simp [List.getElem?_take, show ¬ l.val < h.val from hcon] at hx
          refine ⟨x, y, ?_, ?_, hxy⟩
          · rw [s_eq] at hx; simpa [List.getElem?_take, hlh] using hx
          · rw [s1_eq] at hy; simpa [List.getElem?_take, hlh] using hy


theorem drop_split {α : Type} (x : List α) (k i : Nat) (hi : i ≤ k) (hk : k ≤ x.length) :
    x.drop (k - i) = (x.take k).drop (k - i) ++ x.drop k := by
  conv_lhs => rw [← List.take_append_drop k x]
  rw [List.drop_append_of_le_length (by simp; omega)]

theorem common_suffix_aux {T : Type} (inst : core.cmp.PartialEq T T)
    (heq : ∀ x y, inst.eq x y ⦃ b => b = true ↔ x = y ⦄)
    (hne : ∀ x y, inst.ne x y ⦃ b => b = true ↔ ¬ x = y ⦄) :
    ∀ N : Nat, ∀ a b : Slice T, min a.val.length b.val.length = N →
    lines.common_suffix inst a b ⦃ l => l.val ≤ N ∧
      a.val.drop (a.val.length - l.val) = b.val.drop (b.val.length - l.val) ∧
      (l.val = N ∨ (l.val < N ∧ ∃ x y, a.val[a.val.length - 1 - l.val]? = some x ∧
        b.val[b.val.length - 1 - l.val]? = some y ∧ x ≠ y)) ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a b hn
  rw [lines.common_suffix.eq_1]
  step*
  · -- the minimum is 0
    have hnv : n.val = N := by rw [n_post, minlen]; exact hn
    have : N = 0 := by scalar_tac
    subst this
    simp
  · -- the minimum is 1
    have hnv : n.val = N := by rw [n_post, minlen]; exact hn
    have hN : N = 1 := by scalar_tac
    subst hN
    have hla : a.val.length = a.len.val := by simp [Slice.len]
    have hlb : b.val.length = b.len.val := by simp [Slice.len]
    have e1 : t = a.val[a.val.length - 1]'(by omega) := by rw [t_post]; congr 1
    have e2 : t1 = b.val[b.val.length - 1]'(by omega) := by rw [t1_post]; congr 1
    have g1 : a.val[a.val.length - 1]? = some t := by
      rw [e1]; exact List.getElem?_eq_getElem (by omega)
    have g2 : b.val[b.val.length - 1]? = some t1 := by
      rw [e2]; exact List.getElem?_eq_getElem (by omega)
    have d1 : a.val.drop (a.val.length - 1) = [t] := by
      rw [List.drop_eq_getElem_cons (by omega), e1]
      have : a.val.length - 1 + 1 = a.val.length := by omega
      simp [this]
    have d2 : b.val.drop (b.val.length - 1) = [t1] := by
      rw [List.drop_eq_getElem_cons (by omega), e2]
      have : b.val.length - 1 + 1 = b.val.length := by omega
      simp [this]
    cases b1 with
    | true =>
      have : t = t1 := b1_post.mp rfl
      simp [core.convert.num.FromUsizeBool.from, d1, d2, this]
    | false =>
      have : t ≠ t1 := fun h => by simpa using b1_post.mpr h
      simp [core.convert.num.FromUsizeBool.from]
      exact ⟨t, g1, t1, g2, this⟩
  · -- halve
    have hnv : n.val = N := by rw [n_post, minlen]; exact hn
    have hN2 : 2 ≤ N := by scalar_tac
    have hh : h.val = N / 2 := by omega
    have hla : N ≤ a.val.length := by omega
    have hlb : N ≤ b.val.length := by omega
    have hal : a.len.val = a.val.length := by simp [Slice.len]
    have hbl : b.len.val = b.val.length := by simp [Slice.len]
    have s_eq : s.val = a.val.drop (a.val.length - h.val) := by rw [s_post, i3_post, hal]
    have s1_eq : s1.val = b.val.drop (b.val.length - h.val) := by rw [s1_post, i5_post, hbl]
    step with core.slice.cmp.PartialEqSlice.eq_homo_spec inst s s1 hne as ⟨b1, hb1⟩
    split
    · rename_i hb
      have heq' : a.val.drop (a.val.length - h.val) = b.val.drop (b.val.length - h.val) := by
        rw [← s_eq, ← s1_eq]; rw [hb1.mp hb]
      step as ⟨i7, i7_post, i7_post1⟩
      step as ⟨s2, s2_post, s2_post1⟩
      step as ⟨i9, i9_post, i9_post1⟩
      step as ⟨s3, s3_post, s3_post1⟩
      have s2_eq : s2.val = a.val.take (a.val.length - h.val) := by
        simp [s2_post, List.slice, i7_post, hal]
      have s3_eq : s3.val = b.val.take (b.val.length - h.val) := by
        simp [s3_post, List.slice, i9_post, hbl]
      have hM : min s2.val.length s3.val.length = N - h.val := by
        rw [s2_eq, s3_eq]; simp; omega
      have hlt : N - h.val < N := by omega
      step with (ih (N - h.val) hlt s2 s3 hM) as ⟨i10, hi2a, hi2b, hi2c⟩
      step as ⟨r, r_post⟩
      have hr : r.val = h.val + i10.val := by scalar_tac
      have l2 : s2.val.length = a.val.length - h.val := by simp [s2_eq]
      have l3 : s3.val.length = b.val.length - h.val := by simp [s3_eq]
      have ea : a.val.length - (h.val + i10.val) = s2.val.length - i10.val := by omega
      have eb : b.val.length - (h.val + i10.val) = s3.val.length - i10.val := by omega
      refine ⟨by omega, ?_, ?_⟩
      · have key : s2.val.drop (a.val.length - h.val - i10.val) =
            s3.val.drop (b.val.length - h.val - i10.val) := by
          rw [show a.val.length - h.val - i10.val = s2.val.length - i10.val by omega,
            show b.val.length - h.val - i10.val = s3.val.length - i10.val by omega]
          exact hi2b
        rw [hr, show a.val.length - (h.val + i10.val) = a.val.length - h.val - i10.val by omega,
          show b.val.length - (h.val + i10.val) = b.val.length - h.val - i10.val by omega,
          drop_split a.val (a.val.length - h.val) i10.val (by omega) (by omega),
          drop_split b.val (b.val.length - h.val) i10.val (by omega) (by omega),
          ← s2_eq, ← s3_eq, key, heq']
      · rcases hi2c with hc | ⟨hc, x, y, hx, hy, hxy⟩
        · left; omega
        · right
          refine ⟨by omega, ?_⟩
          have ia : a.val.length - 1 - (h.val + i10.val) = s2.val.length - 1 - i10.val := by omega
          have ib : b.val.length - 1 - (h.val + i10.val) = s3.val.length - 1 - i10.val := by omega
          refine ⟨x, y, ?_, ?_, hxy⟩
          · rw [hr, ia]
            have hlt2 : s2.val.length - 1 - i10.val < a.val.length - h.val := by omega
            have hx' : (a.val.take (a.val.length - h.val))[s2.val.length - 1 - i10.val]? = some x := by
              rw [← s2_eq]; exact hx
            rwa [List.getElem?_take_of_lt hlt2] at hx'
          · rw [hr, ib]
            have hlt2 : s3.val.length - 1 - i10.val < b.val.length - h.val := by omega
            have hy' : (b.val.take (b.val.length - h.val))[s3.val.length - 1 - i10.val]? = some y := by
              rw [← s3_eq]; exact hy
            rwa [List.getElem?_take_of_lt hlt2] at hy'
    · rename_i hb
      have hsl : s.val.length = h.val := by simp [s_eq]; omega
      have hsl1 : s1.val.length = h.val := by simp [s1_eq]; omega
      have hM : min s.val.length s1.val.length = h.val := by rw [hsl, hsl1]; simp
      have hlt : h.val < N := by omega
      step as ⟨i7, i7_post, i7_post1⟩
      step as ⟨s2, s2_post, s2_post1⟩
      step as ⟨i9, i9_post, i9_post1⟩
      step as ⟨s3, s3_post, s3_post1⟩
      have e2 : s2 = s := by rw [Slice.eq_iff, s2_post, s_eq, i7_post, hal]
      have e3 : s3 = s1 := by rw [Slice.eq_iff, s3_post, s1_eq, i9_post, hbl]
      subst e2 e3
      step with (ih h.val hlt s2 s3 hM) as ⟨l, hla', hlb', hlc'⟩
      have hne' : s2 ≠ s3 := fun e => hb (hb1.mpr e)
      have hl1 : l.val ≤ h.val := hla'
      have k1 : s2.val.drop (h.val - l.val) = a.val.drop (a.val.length - l.val) := by
        rw [s_eq, List.drop_drop]; congr 1; omega
      have k2 : s3.val.drop (h.val - l.val) = b.val.drop (b.val.length - l.val) := by
        rw [s1_eq, List.drop_drop]; congr 1; omega
      refine ⟨by omega, ?_, ?_⟩
      · rw [hsl, hsl1, k1, k2] at hlb'
        exact hlb'
      · rcases hlc' with hc | ⟨hc, x, y, hx, hy, hxy⟩
        · exfalso
          apply hne'
          rw [hsl, hsl1, hc, Nat.sub_self, List.drop_zero, List.drop_zero] at hlb'
          rw [Slice.eq_iff]; exact hlb'
        · right
          refine ⟨by omega, x, y, ?_, ?_, hxy⟩
          · have g : s2.val[s2.val.length - 1 - l.val]? = a.val[a.val.length - 1 - l.val]? := by
              rw [hsl, s_eq, List.getElem?_drop]; congr 1; omega
            rw [← g]; exact hx
          · have g : s3.val[s3.val.length - 1 - l.val]? = b.val[b.val.length - 1 - l.val]? := by
              rw [hsl1, s1_eq, List.getElem?_drop]; congr 1; omega
            rw [← g]; exact hy

section generic
variable {T : Type} (inst : core.cmp.PartialEq T T)
  (heq : ∀ x y, inst.eq x y ⦃ b => b = true ↔ x = y ⦄)
  (hne : ∀ x y, inst.ne x y ⦃ b => b = true ↔ ¬ x = y ⦄)
include heq hne

/-- `common_prefix a b` returns `l <= min (len a) (len b)` with `a[..l] = b[..l]`, and either `l` is the
minimum or `a[l] != b[l]` (both indices are in range). -/
theorem common_prefix_spec (a b : Slice T) :
    lines.common_prefix inst a b ⦃ l => l.val ≤ min a.val.length b.val.length ∧
      a.val.take l.val = b.val.take l.val ∧
      (l.val = min a.val.length b.val.length ∨
        ∃ x y, a.val[l.val]? = some x ∧ b.val[l.val]? = some y ∧ x ≠ y) ⦄ :=
  common_prefix_aux inst heq hne _ a b rfl

/-- `common_suffix a b` returns `l <= min (len a) (len b)` with equal last `l` elements, and either `l` is the
minimum or the next elements from the end differ. -/
theorem common_suffix_spec (a b : Slice T) :
    lines.common_suffix inst a b ⦃ l => l.val ≤ min a.val.length b.val.length ∧
      a.val.drop (a.val.length - l.val) = b.val.drop (b.val.length - l.val) ∧
      (l.val = min a.val.length b.val.length ∨
        (l.val < min a.val.length b.val.length ∧ ∃ x y, a.val[a.val.length - 1 - l.val]? = some x ∧
          b.val[b.val.length - 1 - l.val]? = some y ∧ x ≠ y)) ⦄ :=
  common_suffix_aux inst heq hne _ a b rfl
end generic

theorem common_prefix_u8 (a b : Slice U8) :
    lines.common_prefix core.cmp.PartialEqU8 a b ⦃ l => l.val ≤ min a.val.length b.val.length ∧
      a.val.take l.val = b.val.take l.val ∧
      (l.val = min a.val.length b.val.length ∨
        ∃ x y, a.val[l.val]? = some x ∧ b.val[l.val]? = some y ∧ x ≠ y) ⦄ :=
  common_prefix_spec _ (by intro x y; simp [liftFun2]) (by intro x y; simp [liftFun2]) a b

theorem common_suffix_u8 (a b : Slice U8) :
    lines.common_suffix core.cmp.PartialEqU8 a b ⦃ l => l.val ≤ min a.val.length b.val.length ∧
      a.val.drop (a.val.length - l.val) = b.val.drop (b.val.length - l.val) ∧
      (l.val = min a.val.length b.val.length ∨
        (l.val < min a.val.length b.val.length ∧ ∃ x y, a.val[a.val.length - 1 - l.val]? = some x ∧
          b.val[b.val.length - 1 - l.val]? = some y ∧ x ≠ y)) ⦄ :=
  common_suffix_spec _ (by intro x y; simp [liftFun2]) (by intro x y; simp [liftFun2]) a b

theorem common_prefix_u32 (a b : Slice U32) :
    lines.common_prefix core.cmp.PartialEqU32 a b ⦃ l => l.val ≤ min a.val.length b.val.length ∧
      a.val.take l.val = b.val.take l.val ∧
      (l.val = min a.val.length b.val.length ∨
        ∃ x y, a.val[l.val]? = some x ∧ b.val[l.val]? = some y ∧ x ≠ y) ⦄ :=
  common_prefix_spec _ (by intro x y; simp [liftFun2]) (by intro x y; simp [liftFun2]) a b

theorem common_suffix_u32 (a b : Slice U32) :
    lines.common_suffix core.cmp.PartialEqU32 a b ⦃ l => l.val ≤ min a.val.length b.val.length ∧
      a.val.drop (a.val.length - l.val) = b.val.drop (b.val.length - l.val) ∧
      (l.val = min a.val.length b.val.length ∨
        (l.val < min a.val.length b.val.length ∧ ∃ x y, a.val[a.val.length - 1 - l.val]? = some x ∧
          b.val[b.val.length - 1 - l.val]? = some y ∧ x ≠ y)) ⦄ :=
  common_suffix_spec _ (by intro x y; simp [liftFun2]) (by intro x y; simp [liftFun2]) a b

end difffold_myers_extract
