import RealSwar
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-- Byte values of a list of `u8`. -/
def bytes (l : List U8) : List Nat := l.map (fun u => u.val)

theorem bytes_length (l : List U8) : (bytes l).length = l.length := by simp [bytes]

/-- A word load: the first eight bytes, padded with zeros. -/
def pad8 (l : List Nat) : List Nat := l.take 8 ++ List.replicate (8 - l.length) 0

theorem Pl_append : ∀ (l1 l2 : List Nat), Pl (l1 ++ l2) = Pl l1 + 256 ^ l1.length * Pl l2
  | [], l2 => by simp [Pl]
  | b :: l1, l2 => by
    simp only [List.cons_append, Pl, Pl_append l1 l2, List.length_cons, pow_succ]
    ring

theorem Pl_replicate_zero : ∀ k, Pl (List.replicate k 0) = 0
  | 0 => by simp [Pl]
  | k + 1 => by simp [List.replicate_succ, Pl, Pl_replicate_zero k]

theorem or_add_shift (A x s : Nat) (hA : A < 2 ^ s) : A ||| (x * 2 ^ s) = A + x * 2 ^ s := by
  apply Nat.eq_of_testBit_eq
  intro j
  have e : A + x * 2 ^ s = 2 ^ s * x + A := by ring
  have e2 : x * 2 ^ s = 2 ^ s * x + 0 := by ring
  rw [e, e2, Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hA, Nat.testBit_two_pow_mul_add _ (Nat.pow_pos (by omega : 0 < 2))]
  by_cases hj : j < s
  · simp [hj]
  · have : A.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hj, this]

theorem fromLEBytes_toNat : ∀ l : List (BitVec 8), (BitVec.fromLEBytes l).toNat = Pl (l.map BitVec.toNat)
  | [] => by simp [BitVec.fromLEBytes, Pl]
  | b :: l => by
    have ih := fromLEBytes_toNat l
    have hb : b.toNat < 256 := b.isLt
    have hF := (BitVec.fromLEBytes l).isLt
    rw [ih] at hF
    unfold BitVec.fromLEBytes
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have hW : 2 ^ (8 * (b :: l).length) = 256 * 2 ^ (8 * l.length) := by
      simp only [List.length_cons]
      rw [show 8 * (l.length + 1) = 8 * l.length + 8 by ring, pow_add]; ring
    have hpos : 0 < 2 ^ (8 * l.length) := Nat.pow_pos (by omega)
    have m1 : b.toNat % 2 ^ (8 * (b :: l).length) = b.toNat := Nat.mod_eq_of_lt (by omega)
    have m2 : Pl (List.map BitVec.toNat l) % 2 ^ (8 * (b :: l).length) = Pl (List.map BitVec.toNat l) :=
      Nat.mod_eq_of_lt (by omega)
    have m3 : (Pl (List.map BitVec.toNat l) <<< 8) % 2 ^ (8 * (b :: l).length) =
        Pl (List.map BitVec.toNat l) * 256 := by
      rw [Nat.shiftLeft_eq, hW]; apply Nat.mod_eq_of_lt
      have : 2 ^ 8 = 256 := by norm_num
      rw [this]; omega
    rw [m1, ih, m2, m3]
    simp only [List.map_cons, Pl]
    have := peel_or b.toNat 0 hb (by omega) 0 (Pl (List.map BitVec.toNat l))
    simpa [mul_comm] using this

theorem Pl_pad8 (l : List Nat) (h : l.length ≤ 8) : Pl (pad8 l) = Pl l := by
  simp only [pad8]
  rw [List.take_of_length_le h, Pl_append, Pl_replicate_zero]; simp

theorem pad8_step (l : List Nat) (k x : Nat) (hk : l.length = k + 1) (hk7 : k + 1 ≤ 7) (hx : l[k]? = some x) :
    Pl (pad8 (l.take k)) + x * 256 ^ k = Pl (pad8 l) := by
  have hne : l ≠ [] := by intro h; subst h; simp at hk
  obtain ⟨L, y, rfl⟩ : ∃ L y, l = L ++ [y] :=
    ⟨l.dropLast, l.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  have hL : L.length = k := by simpa using hk
  have hy : y = x := by
    rw [List.getElem?_append_right (by omega)] at hx; simpa [hL] using hx
  subst hy
  rw [show (L ++ [y]).take k = L by rw [← hL]; exact List.take_left]
  have h1 : pad8 L = L ++ List.replicate (8 - k) 0 := by
    simp only [pad8, hL]; rw [List.take_of_length_le (by omega)]
  have h2 : pad8 (L ++ [y]) = (L ++ [y]) ++ List.replicate (8 - (k + 1)) 0 := by
    simp only [pad8, List.length_append, hL, List.length_singleton]
    rw [List.take_of_length_le (by simp; omega)]
  rw [h1, h2, Pl_append, Pl_append, Pl_append, Pl_replicate_zero, Pl_replicate_zero]
  simp [hL, Pl]
  ring

theorem hfl (a : Array U8 8#usize) : (core.num.U64.from_le_bytes a).val = Pl (bytes a.val) := by
  rw [← UScalar.bv_toNat]
  unfold core.num.U64.from_le_bytes
  rw [BitVec.toNat_cast, fromLEBytes_toNat]
  simp [bytes, List.map_map, Function.comp_def]

theorem word_spec : ∀ (n : Nat) (t : Slice U8), t.val.length = n →
    lines.word t ⦃ w => w.val = Pl (pad8 (bytes t.val)) ⦄ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t hn
  rw [lines.word.eq_1]
  have hlen : t.len.val = n := by simp [Slice.len, hn]
  split
  · rename_i h0
    have : t.val = [] := List.length_eq_zero_iff.mp (by rw [hn]; omega)
    simp [Aeneas.Std.WP.spec_ok, this, pad8, bytes, Pl]
  · rename_i h0
    split
    · rename_i h8
      step*
      have hl8 : 8 ≤ t.val.length := by
        have : (8#usize).val = 8 := by simp
        scalar_tac
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rest, ht⟩ :
          ∃ a0 a1 a2 a3 a4 a5 a6 a7 rest, t.val = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest := by
        match h : t.val, hl8 with
        | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest, _ => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      simp only [ht] at i_post i1_post i2_post i3_post i4_post i5_post i6_post i7_post
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at i_post i1_post i2_post i3_post i4_post i5_post i6_post i7_post
      rw [hfl]
      simp [ht, pad8, bytes, i_post, i1_post, i2_post, i3_post, i4_post, i5_post, i6_post, i7_post, Array.make]
    · rename_i h8
      step*
      simp only [lift, bind_tc_ok]
      step*
      have hn7 : t.val.length ≤ 7 := by
        have : ¬ 8 ≤ t.len.val := by scalar_tac
        omega
      have hn1 : 1 ≤ t.val.length := by omega
      have hik : i.val = t.val.length - 1 := by omega
      have hu8 : ∀ u : U8, u.val < 256 := fun u => by scalar_tac
      have hbl : ∀ b ∈ bytes t.val, b < 256 := by
        intro b hb; simp only [bytes, List.mem_map] at hb
        obtain ⟨u, _, rfl⟩ := hb; exact hu8 u
      have hs : bytes s.val = (bytes t.val).take i.val := by
        rw [s_post]; simp [List.slice, bytes, List.map_take]
      have hx : (bytes t.val)[i.val]? = some i2.val := by
        have hlt : i.val < t.val.length := by omega
        simp [bytes, i2_post, List.getElem?_eq_getElem hlt]
      have hstep := pad8_step (bytes t.val) i.val i2.val (by rw [bytes_length]; omega)
        (by omega) hx
      have hA : Pl (pad8 (bytes s.val)) < 256 ^ i.val := by
        rw [hs]
        have hlenA : ((bytes t.val).take i.val).length = i.val := by
          simp [bytes_length]; omega
        rw [Pl_pad8 _ (by omega)]
        have := Pl_lt ((bytes t.val).take i.val) (fun b hb => hbl b (List.mem_of_mem_take hb))
        rwa [hlenA] at this
      have hB : i5.val = i2.val * 256 ^ i.val := by
        have e : U64.size = 2 ^ 64 := by simp [U64.size, U64.numBits]
        rw [i5_post, core.convert.num.FromU64U8.from_val_eq, Nat.shiftLeft_eq, i4_post, e]
        have : 2 ^ (8 * i.val) = 256 ^ i.val := by rw [pow_mul]; norm_num
        rw [this]
        apply Nat.mod_eq_of_lt
        have h1 : 256 ^ i.val ≤ 256 ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
        have h2 := hu8 i2
        calc i2.val * 256 ^ i.val ≤ 255 * 256 ^ 6 := Nat.mul_le_mul (by omega) h1
          _ < 2 ^ 64 := by norm_num
      have hor : (i1 ||| i5).val = i1.val + i5.val := by
        rw [u64_or, hB, i1_post]
        have : 256 ^ i.val = 2 ^ (8 * i.val) := by rw [pow_mul]; norm_num
        rw [this] at hA ⊢
        exact or_add_shift _ _ _ hA
      rw [hor, i1_post, hB, ← hstep, hs]

end difffold_myers_extract
