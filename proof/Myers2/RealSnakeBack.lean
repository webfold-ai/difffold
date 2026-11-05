import RealDefs
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_myers_extract

theorem rev_vals (l : List U32) : (vals l).reverse = vals l.reverse := by simp [vals, List.map_reverse]

theorem cpre_suffix (A' B' : List U32) (l : Nat) (hl : l ≤ min A'.length B'.length)
    (h2 : A'.drop (A'.length - l) = B'.drop (B'.length - l))
    (h3 : l = min A'.length B'.length ∨
      (l < min A'.length B'.length ∧ ∃ p q, A'[A'.length - 1 - l]? = some p ∧ B'[B'.length - 1 - l]? = some q ∧ p ≠ q)) :
    Myers.cpre (vals A').reverse (vals B').reverse = l := by
  apply Myers.cpre_char
  · simpa [vals] using hl
  · rw [List.take_reverse, List.take_reverse]
    have e1 : (vals A').length = A'.length := by simp [vals]
    have e2 : (vals B').length = B'.length := by simp [vals]
    rw [e1, e2]
    have := congrArg (fun t => (vals t).reverse) h2
    simp only [vals, List.map_drop] at this ⊢
    simpa using this
  · rcases h3 with h3 | ⟨hlt, p, q, hp, hq, hpq⟩
    · left; simpa [vals] using h3
    · right
      refine ⟨p.val, q.val, ?_, ?_, ?_⟩
      · rw [List.getElem?_reverse (by simp [vals]; omega)]; simp [vals, List.getElem?_map, hp]
      · rw [List.getElem?_reverse (by simp [vals]; omega)]; simp [vals, List.getElem?_map, hq]
      · intro e; exact hpq (UScalar.eq_of_val_eq e)

theorem snake_back_spec (a b : Slice U32) (x y : I32) (hx : 0 ≤ x.val) (hy : 0 ≤ y.val)
    (ha : a.val.length ≤ I32.max) (hb : b.val.length ≤ I32.max) :
    lines.snake_back a b x y ⦃ r => 0 ≤ r.val ∧ x.val + r.val ≤ max x.val a.val.length ∧
      y.val + r.val ≤ max y.val b.val.length ∧
      r.val = Myers.snake (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val ⦄ := by
  have hn := hlen a ha
  have hm := hlen b hb
  have hImax : (I32.max : Int) = 2147483647 := by scalar_tac
  have h1 := Myers.snake_le (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val
  have h2 := Myers.snake_le_y (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val
  simp only [List.length_reverse, vals, List.length_map] at h1 h2
  have hxn : (x.val.toNat : Int) = x.val := Int.toNat_of_nonneg hx
  unfold lines.snake_back
  have hal : (vals a.val).length = a.val.length := by simp [vals]
  have hbl : (vals b.val).length = b.val.length := by simp [vals]
  step*
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hxn' : n ≤ x := by assumption
    rw [IScalar.le_equiv] at hxn'
    have : Myers.snake (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val = 0 := by
      unfold Myers.snake; rw [if_pos (Or.inr (Or.inl (by simp [vals]; omega)))]
    rw [this]; simp <;> omega
  · have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hym' : m ≤ y := by assumption
    rw [IScalar.le_equiv] at hym'
    have : Myers.snake (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val = 0 := by
      unfold Myers.snake; rw [if_pos (Or.inr (Or.inr (by simp [vals]; omega)))]
    rw [this]; simp <;> omega
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hxl : ¬ (n ≤ x) := by assumption
    rw [IScalar.le_equiv] at hxl
    have := hus i3 (by omega)
    show i4.val < a.val.length
    rw [i4_post, this]; omega
  · have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hyl : ¬ (m ≤ y) := by assumption
    rw [IScalar.le_equiv] at hyl
    have := hus i7 (by omega)
    show i8.val < b.val.length
    rw [i8_post, this]; omega
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hxl : ¬ (n ≤ x) := by assumption
    have hyl : ¬ (m ≤ y) := by assumption
    rw [IScalar.le_equiv] at hxl hyl
    have e4 := hus i3 (by omega)
    have e8 := hus i7 (by omega)
    have hne : i5 ≠ i9 := by simpa using (by assumption : (i5 != i9) = true)
    have hc : ¬ (y.val < 0 ∨ ((vals a.val).reverse).length ≤ x.val.toNat ∨
        (((vals b.val).reverse).length : Int) ≤ y.val) := by simp [vals]; omega
    have hi4 : i4.val = a.val.length - 1 - x.val.toNat := by rw [i4_post, e4]; omega
    have hi8 : i8.val = b.val.length - 1 - y.val.toNat := by rw [i8_post, e8]; omega
    have hb4 : i4.val < a.val.length := by omega
    have hb8 : i8.val < b.val.length := by omega
    have ga : a.val[a.val.length - 1 - x.val.toNat]? = some i5 := by
      rw [i5_post, ← hi4]; exact List.getElem?_eq_getElem hb4
    have gb : b.val[b.val.length - 1 - y.val.toNat]? = some i9 := by
      rw [i9_post, ← hi8]; exact List.getElem?_eq_getElem hb8
    have key : Myers.snake (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val = 0 := by
      unfold Myers.snake; rw [if_neg hc]
      have ey : y.val.toNat = y.val.toNat := rfl
      apply Myers.cpre_char
      · simp
      · simp
      · right
        refine ⟨i5.val, i9.val, ?_, ?_, fun e => hne (UScalar.eq_of_val_eq e)⟩
        · rw [List.getElem?_drop, Nat.add_zero, List.getElem?_reverse (by simp [vals]; omega)]
          simp [vals, List.getElem?_map, ga]
        · rw [List.getElem?_drop, Nat.add_zero, List.getElem?_reverse (by simp [vals]; omega)]
          simp [vals, List.getElem?_map, gb]
    rw [key]; simp <;> omega
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hxl : ¬ (n ≤ x) := by assumption
    rw [IScalar.le_equiv] at hxl
    have := hus i10 (by omega)
    show i11.val ≤ a.val.length
    rw [i11_post, this]; omega
  · have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hyl : ¬ (m ≤ y) := by assumption
    rw [IScalar.le_equiv] at hyl
    have := hus i12 (by omega)
    show i13.val ≤ b.val.length
    rw [i13_post, this]; omega
  · have hnv : n.val = a.val.length := by rw [n_post]; exact hn
    have hmv : m.val = b.val.length := by rw [m_post]; exact hm
    have hxl : ¬ (n ≤ x) := by assumption
    have hyl : ¬ (m ≤ y) := by assumption
    rw [IScalar.le_equiv] at hxl hyl
    have e11 := hus i10 (by omega)
    have e13 := hus i12 (by omega)
    step with common_suffix_u32 s s1 as ⟨i14, h14a, h14b, h14c⟩
    have hs : s.val = a.val.take (a.val.length - x.val.toNat) := by
      rw [s_post]; simp [List.slice]; rw [i11_post, e11]; omega
    have hs1 : s1.val = b.val.take (b.val.length - y.val.toNat) := by
      rw [s1_post]; simp [List.slice]; rw [i13_post, e13]; omega
    have hc : ¬ (y.val < 0 ∨ ((vals a.val).reverse).length ≤ x.val.toNat ∨
        (((vals b.val).reverse).length : Int) ≤ y.val) := by simp [vals]; omega
    rw [hs, hs1] at h14a h14b h14c
    have hcs := cpre_suffix _ _ _ h14a h14b h14c
    have key : Myers.snake (vals a.val).reverse (vals b.val).reverse x.val.toNat y.val = i14.val := by
      unfold Myers.snake; rw [if_neg hc]
      rw [List.drop_reverse, List.drop_reverse]
      try simp only [List.length_map] at *
      rw [← hcs]
      simp only [vals, List.map_take, List.length_map]
    have hle : i14.val ≤ I32.max := by
      have := h14a
      simp only [List.length_take] at this
      omega
    rw [hcast32 i14 hle]
    have key' := key
    simp only [vals] at key'
    rw [key'] at h1 h2
    refine ⟨by omega, by omega, by omega, by rw [key]⟩

end difffold_myers_extract
