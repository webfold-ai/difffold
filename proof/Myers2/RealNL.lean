import RealWord
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- `i` is the index of the first newline of `l`. -/
def IsFirst10 (l : List Nat) (i : Nat) : Prop := l[i]? = some 10 ∧ ∀ j, j < i → l[j]? ≠ some 10

/-- `r` is the answer of a first-newline search of `l`. -/
def FirstNL (l : List Nat) : Option Nat → Prop
  | none => 10 ∉ l
  | some i => IsFirst10 l i

/-- `i` is the index of the last newline of `l`. -/
def IsLast10 (l : List Nat) (i : Nat) : Prop := l[i]? = some 10 ∧ ∀ j, i < j → l[j]? ≠ some 10

def LastNL (l : List Nat) : Option Nat → Prop
  | none => 10 ∉ l
  | some i => IsLast10 l i

theorem lowest_byte_spec : ∀ (n : Nat) (L : List Nat) (k : Usize) (m : U64), L.length = n →
    k.val + n = 8 → (∀ b ∈ L, b < 256) → m.val = Pl (L.map gmask) → 10 ∈ L →
    lines.lowest_byte m k ⦃ r => ∃ i, IsFirst10 L i ∧ r.val = k.val + i ⦄ := by
  intro n
  induction n with
  | zero => intro L k m hl _ _ _ h10; have : L = [] := List.length_eq_zero_iff.mp hl; simp [this] at h10
  | succ n ih =>
    intro L k m hl hk hb hm h10
    obtain ⟨x, L', rfl⟩ : ∃ x L', L = x :: L' := by
      cases L with
      | nil => simp at hl
      | cons x L' => exact ⟨x, L', rfl⟩
    rw [lines.lowest_byte.eq_1]
    simp only [lift, bind_tc_ok]
    have hx : x < 256 := hb x (by simp)
    have hm' : m.val = gmask x + 256 * Pl (L'.map gmask) := by rw [hm]; simp [Pl]
    have hg : gmask x ≤ 128 := by unfold gmask; split <;> omega
    have hand : (m &&& 255#u64).val = gmask x := by
      rw [u64_and]
      have : (255#u64).val = 255 := by simp
      rw [this, show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod, hm']
      omega
    by_cases h10x : x = 10
    · have hne : (m &&& 255#u64) ≠ 0#u64 := by
        intro h
        have := congrArg UScalar.val h
        rw [hand] at this
        simp [gmask, h10x] at this
      have hbne : (m &&& 255#u64 != 0#u64) = true := by simpa using hne
      rw [if_pos hbne]
      simp only [Aeneas.Std.WP.spec_ok]
      exact ⟨0, ⟨by simp [h10x], by simp⟩, by simp⟩
    · have hzero : (m &&& 255#u64) = 0#u64 := by
        apply UScalar.eq_of_val_eq
        rw [hand]; simp [gmask, h10x]
      have hbne : ¬ (m &&& 255#u64 != 0#u64) = true := by simp [hzero]
      rw [if_neg hbne]
      have h10' : 10 ∈ L' := by simpa [Ne.symm h10x] using h10
      have hL' : L'.length = n := by simpa using hl
      have hn1 : 1 ≤ n := by
        cases L' with
        | nil => simp at h10'
        | cons _ _ => simp at hL'; omega
      have hk7 : ¬ k ≥ 7#usize := by
        have : (7#usize).val = 7 := by simp
        scalar_tac
      rw [if_neg hk7]
      step as ⟨i1, hi1, hi1b⟩
      step as ⟨i2, hi2⟩
      have hi1v : i1.val = Pl (L'.map gmask) := by
        rw [hi1, hm', Nat.shiftRight_eq_div_pow]
        have : 2 ^ 8 = 256 := by norm_num
        rw [this]; omega
      step with (ih L' i2 i1 hL' (by omega) (fun b hb' => hb b (List.mem_cons_of_mem _ hb')) hi1v h10') as
        ⟨i, rr, hfi, hr⟩
      refine ⟨i + 1, ⟨?_, ?_⟩, by omega⟩
      · simpa using hfi.1
      · intro j hj
        cases j with
        | zero => simp [h10x]
        | succ j => simpa using hfi.2 j (by omega)

theorem pad8_length (l : List Nat) : (pad8 l).length = 8 := by
  simp only [pad8, List.length_append, List.length_take, List.length_replicate]; omega

theorem pad8_getElem? (l : List Nat) (i : Nat) (hi : i < l.length) (h8 : i < 8) : (pad8 l)[i]? = l[i]? := by
  simp only [pad8]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]; simp [h8]

theorem pad8_lt (l : List Nat) (h : ∀ b ∈ l, b < 256) : ∀ b ∈ pad8 l, b < 256 := by
  intro b hb
  simp only [pad8, List.mem_append, List.mem_replicate] at hb
  rcases hb with hb | ⟨_, rfl⟩
  · exact h b (List.mem_of_mem_take hb)
  · omega

theorem mem_pad8 (l : List Nat) : 10 ∈ pad8 l ↔ 10 ∈ l.take 8 := by
  simp [pad8, List.mem_replicate]

theorem IsFirst10_pad8 (l : List Nat) (i : Nat) (h : IsFirst10 (pad8 l) i) : IsFirst10 l i := by
  obtain ⟨h1, h2⟩ := h
  have hi8 : i < 8 := by
    have := (List.getElem?_eq_some_iff.mp h1).1; rw [pad8_length] at this; exact this
  have hil : i < l.length := by
    by_contra hc
    simp only [pad8] at h1
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_replicate] at h1
    split at h1 <;> simp at h1
  refine ⟨by rw [← pad8_getElem? l i hil hi8]; exact h1, ?_⟩
  intro j hj
  rw [← pad8_getElem? l j (by omega) (by omega)]
  exact h2 j hj

theorem IsFirst10_skip (s : List Nat) (hno : 10 ∉ s.take 8) (i : Nat) (h : IsFirst10 (s.drop 8) i) :
    IsFirst10 s (i + 8) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [List.getElem?_drop] at h1; simpa [Nat.add_comm] using h1, ?_⟩
  intro j hj
  by_cases hj8 : j < 8
  · intro hc
    apply hno
    have : (s.take 8)[j]? = some 10 := by rw [List.getElem?_take]; simpa [hj8] using hc
    exact List.mem_of_getElem? this
  · have := h2 (j - 8) (by omega)
    rw [List.getElem?_drop] at this
    rwa [show 8 + (j - 8) = j by omega] at this

/-- Result of a first-newline search of `l` from position `p0` onward. -/
def Found (p0 : Nat) (l : List Nat) : Option Usize → Prop
  | none => 10 ∉ l.drop p0
  | some i => p0 ≤ i.val ∧ IsFirst10 (l.drop p0) (i.val - p0)

theorem Pl_eq_zero : ∀ L : List Nat, Pl L = 0 ↔ ∀ b ∈ L, b = 0
  | [] => by simp [Pl]
  | b :: L => by
    have := Pl_eq_zero L
    simp only [Pl, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h; exact ⟨by omega, this.mp (by omega)⟩
    · rintro ⟨h1, h2⟩; have := this.mpr h2; omega

theorem first_in_block_spec (t : Slice U8) (hlen : t.val.length + 8 ≤ Usize.max) :
    ∀ (N : Nat) (a0 : Usize), t.val.length - a0.val = N →
    lines.first_in_block t a0 ⦃ r => Found a0.val (bytes t.val) r ⦄ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a0 hN
  rw [lines.first_in_block.eq_1]
  have hl : (Slice.len t).val = t.val.length := by simp [Slice.len]
  split
  · rename_i hge
    have : t.val.length ≤ a0.val := by scalar_tac
    simp only [Aeneas.Std.WP.spec_ok, Found]
    have : (bytes t.val).drop a0.val = [] := List.drop_of_length_le (by simp [bytes]; omega)
    simp [this]
  · rename_i hlt
    step as ⟨s, hs, hs1⟩
    step with (word_spec _ s rfl) as ⟨w, hw⟩
    have hu8 : ∀ u : U8, u.val < 256 := fun u => by scalar_tac
    have hbl : ∀ b ∈ bytes s.val, b < 256 := by
      intro b hb; simp only [bytes, List.mem_map] at hb
      obtain ⟨u, _, rfl⟩ := hb; exact hu8 u
    have hbs : bytes s.val = (bytes t.val).drop a0.val := by rw [hs]; simp [bytes, List.map_drop]
    have hlt' : a0.val < t.val.length := by scalar_tac
    step with (nl_mask_spec w (pad8 (bytes s.val)) (pad8_length _) (pad8_lt _ hbl) hw) as ⟨m, hm⟩
    by_cases hm0 : m = 0#u64
    · have hbne : ¬ (m != 0#u64) = true := by simp [hm0]
      rw [if_neg hbne]
      have hmv : m.val = 0 := by rw [hm0]; rfl
      have hno : 10 ∉ (bytes s.val).take 8 := by
        intro h10
        have h10' : 10 ∈ pad8 (bytes s.val) := (mem_pad8 _).mpr h10
        rw [hm0] at hm
        have hz := (Pl_eq_zero _).mp (by rw [← hm]; rfl) (gmask 10) (List.mem_map_of_mem h10')
        simp [gmask] at hz
      step as ⟨i2, hi2⟩
      have hN' : t.val.length - i2.val < N := by omega
      step with (ih _ hN' i2 rfl) as ⟨r, hr⟩
      cases r with
      | none =>
        simp only [Found] at hr ⊢
        have hdrop : (bytes t.val).drop a0.val = (bytes s.val).take 8 ++ (bytes s.val).drop 8 := by
          rw [← hbs, List.take_append_drop]
        rw [hdrop]
        simp only [List.mem_append, not_or]
        refine ⟨hno, ?_⟩
        rw [hbs, List.drop_drop, show a0.val + 8 = i2.val by omega]; exact hr
      | some j =>
        simp only [Found] at hr ⊢
        obtain ⟨hj1, hj2⟩ := hr
        refine ⟨by omega, ?_⟩
        have := IsFirst10_skip (bytes s.val) hno (j.val - i2.val) (by rw [hbs, List.drop_drop, show a0.val + 8 = i2.val by omega]; exact hj2)
        rw [hbs] at this
        rwa [show j.val - i2.val + 8 = j.val - a0.val by omega] at this
    · have hbne : (m != 0#u64) = true := by simpa using hm0
      rw [if_pos hbne]
      have hmv : m.val ≠ 0 := fun h => hm0 (UScalar.eq_of_val_eq h)
      have h10 : 10 ∈ pad8 (bytes s.val) := by
        by_contra hc
        apply hmv
        rw [hm]
        apply (Pl_eq_zero _).mpr
        intro b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
        have : x ≠ 10 := fun h => hc (h ▸ hx)
        simp [gmask, this]
      step with (lowest_byte_spec 8 (pad8 (bytes s.val)) 0#usize m (pad8_length _) (by simp) (pad8_lt _ hbl) hm h10) as ⟨i, i2, hfi, hi2⟩
      have hfi' := IsFirst10_pad8 _ _ hfi
      have hil : i < (bytes s.val).length := (List.getElem?_eq_some_iff.mp hfi'.1).1
      have hsl : (bytes s.val).length = t.val.length - a0.val := by simp [bytes_length, hs]
      step as ⟨i3, hi3⟩
      simp only [Aeneas.Std.WP.spec_ok, Found]
      refine ⟨by omega, ?_⟩
      rw [← hbs, show i3.val - a0.val = i by omega]
      exact hfi'

end difffold_myers_extract
