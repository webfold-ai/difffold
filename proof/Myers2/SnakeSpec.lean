import DifffoldMyers
import CommonCopy
import CpreChar
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

/-! Theorem over the Aeneas translation of the closure-free copy of `snake` (`proof/extract/myers_core.rs`):
it returns exactly `Myers.snake` of `Myers/Snake.lean`, the run length of the pure model that the proofs in
`proof/Myers/` use. The copy is tied to the real `src/lines.rs` by `tests/myers_core.rs` only. -/

/-- The ids of a slice of `u32` as naturals, the lists the pure model works on. -/
def vals (l : List U32) : List Nat := l.map (fun u => u.val)

theorem hlen (a : Slice U32) (ha : a.val.length ≤ I32.max) :
    (UScalar.hcast IScalarTy.I32 a.len).val = (a.val.length : Int) := by
  rw [UScalar.hcast_val_eq]
  have h1 : (a.len.val : Int) = a.val.length := by simp [Slice.len]
  simp only [IScalarTy.numBits, h1]
  have : (I32.max : Int) = 2147483647 := by scalar_tac
  rw [Int.bmod_eq_of_le] <;> omega

theorem hus (x : I32) (hx : 0 ≤ x.val) : (IScalar.hcast UScalarTy.Usize x).val = x.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have h32 : x.val < 2 ^ 31 := by scalar_tac
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> omega

theorem cpre_drop (a b : Slice U32) (x y : Nat) (l : Nat) (hl : l ≤ min (a.val.drop x).length (b.val.drop y).length)
    (h1 : (a.val.drop x).take l = (b.val.drop y).take l)
    (h2 : l = min (a.val.drop x).length (b.val.drop y).length ∨
      ∃ p q, (a.val.drop x)[l]? = some p ∧ (b.val.drop y)[l]? = some q ∧ p ≠ q) :
    Myers.cpre (vals (a.val.drop x)) (vals (b.val.drop y)) = l := by
  apply Myers.cpre_char
  · simpa [vals] using hl
  · simp only [vals]; rw [← List.map_take, ← List.map_take, h1]
  · rcases h2 with h2 | ⟨p, q, hp, hq, hpq⟩
    · left; simpa [vals] using h2
    · right
      refine ⟨p.val, q.val, ?_, ?_, ?_⟩
      · simp only [vals, List.getElem?_map, hp, Option.map_some]
      · simp only [vals, List.getElem?_map, hq, Option.map_some]
      · intro e; apply hpq; exact UScalar.eq_of_val_eq e

theorem hcast32 (i : Usize) (h : i.val ≤ I32.max) : (UScalar.hcast IScalarTy.I32 i).val = (i.val : Int) := by
  rw [UScalar.hcast_val_eq]
  simp only [IScalarTy.numBits]
  have : (I32.max : Int) = 2147483647 := by scalar_tac
  rw [Int.bmod_eq_of_le] <;> omega

theorem snake_eq_cpre (a b : List U32) (x : Nat) (y : Int)
    (hc : ¬ (y < 0 ∨ (vals a).length ≤ x ∨ ((vals b).length : Int) ≤ y)) :
    Myers.snake (vals a) (vals b) x y = Myers.cpre (vals (a.drop x)) (vals (b.drop y.toNat)) := by
  unfold Myers.snake
  rw [if_neg hc]
  simp [vals, List.map_drop]

theorem snake_spec (a b : Slice U32) (x y : I32) (hx : 0 ≤ x.val) (hy : 0 ≤ y.val)
    (ha : a.val.length ≤ I32.max) (hb : b.val.length ≤ I32.max) :
    mcore.snake a b x y ⦃ r => r.val = Myers.snake (vals a.val) (vals b.val) x.val.toNat y.val ⦄ := by
  have hn := hlen a ha
  have hm := hlen b hb
  unfold mcore.snake
  step*
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have h1 : n ≤ x := by assumption
    rw [IScalar.le_equiv] at h1
    have hxn : a.val.length ≤ x.val.toNat := by omega
    unfold Myers.snake
    rw [if_pos (Or.inr (Or.inl (by simpa [vals] using hxn)))]
    simp
  · have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have h1 : m ≤ y := by assumption
    rw [IScalar.le_equiv] at h1
    have hym : (b.val.length : Int) ≤ y.val := by omega
    unfold Myers.snake
    rw [if_pos (Or.inr (Or.inr (by simpa [vals] using hym)))]
    simp
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hi2 : i2.val = x.val.toNat := by rw [i2_post]; exact hus x hx
    have h1 : ¬ (n ≤ x) := by assumption
    rw [IScalar.le_equiv] at h1
    show i2.val < a.val.length
    omega
  · have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hi4 : i4.val = y.val.toNat := by rw [i4_post]; exact hus y hy
    have h1 : ¬ (m ≤ y) := by assumption
    rw [IScalar.le_equiv] at h1
    show i4.val < b.val.length
    omega
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hi2 : i2.val = x.val.toNat := by rw [i2_post]; exact hus x hx
    have hi4 : i4.val = y.val.toNat := by rw [i4_post]; exact hus y hy
    have hxn : ¬ (n ≤ x) := by assumption
    have hym : ¬ (m ≤ y) := by assumption
    rw [IScalar.le_equiv] at hxn hym
    have h3 : (i3 != i5) = true := by assumption
    have hc : ¬ (y.val < 0 ∨ (vals a.val).length ≤ x.val.toNat ∨ ((vals b.val).length : Int) ≤ y.val) := by
      simp only [vals, List.length_map]; omega
    rw [snake_eq_cpre _ _ _ _ hc]
    have hne : i3 ≠ i5 := by simpa using h3
    have e0 : Myers.cpre (vals (a.val.drop x.val.toNat)) (vals (b.val.drop y.val.toNat)) = 0 := by
      apply cpre_drop a b x.val.toNat y.val.toNat 0
      · exact Nat.zero_le _
      · simp
      · right
        refine ⟨i3, i5, ?_, ?_, hne⟩
        · have g3 : a.val[i2.val]? = some i3 := by rw [i3_post]; exact List.getElem?_eq_getElem _
          rw [hi2] at g3; simpa [List.getElem?_drop] using g3
        · have g5 : b.val[i4.val]? = some i5 := by rw [i5_post]; exact List.getElem?_eq_getElem _
          rw [hi4] at g5; simpa [List.getElem?_drop] using g5
    rw [e0]; simp
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hi6 : i6.val = x.val.toNat := by rw [i6_post]; exact hus x hx
    have hxn : ¬ (n ≤ x) := by assumption
    rw [IScalar.le_equiv] at hxn
    show i6.val ≤ a.val.length
    omega
  · have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hi7 : i7.val = y.val.toNat := by rw [i7_post]; exact hus y hy
    have hym : ¬ (m ≤ y) := by assumption
    rw [IScalar.le_equiv] at hym
    show i7.val ≤ b.val.length
    omega
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hi6 : i6.val = x.val.toNat := by rw [i6_post]; exact hus x hx
    have hi7 : i7.val = y.val.toNat := by rw [i7_post]; exact hus y hy
    have hxn : ¬ (n ≤ x) := by assumption
    have hym : ¬ (m ≤ y) := by assumption
    rw [IScalar.le_equiv] at hxn hym
    have hc : ¬ (y.val < 0 ∨ (vals a.val).length ≤ x.val.toNat ∨ ((vals b.val).length : Int) ≤ y.val) := by
      simp only [vals, List.length_map]; omega
    step with common_prefix_u32 s s1 as ⟨i8, h8a, h8b, h8c⟩
    rw [snake_eq_cpre _ _ _ _ hc]
    have hs : s.val = a.val.drop x.val.toNat := by rw [s_post, hi6]
    have hs1 : s1.val = b.val.drop y.val.toNat := by rw [s1_post, hi7]
    rw [hs, hs1] at h8a h8b h8c
    rw [cpre_drop a b _ _ i8.val h8a h8b h8c]
    have hle : i8.val ≤ I32.max := by
      have h1 : (List.drop x.val.toNat a.val).length ≤ a.val.length := by simp
      have h2 : min (List.drop x.val.toNat a.val).length (List.drop y.val.toNat b.val).length ≤
          (List.drop x.val.toNat a.val).length := Nat.min_le_left _ _
      omega
    rw [hcast32 i8 hle]

end difffold_myers_extract
