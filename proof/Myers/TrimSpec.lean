import Solve
/-! The specs of `common_prefix` and `common_suffix` (as the extraction proves them) give a `Trim`. -/
open scoped List
namespace Myers

theorem decomp (L : List Nat) (s e : Nat) (h : s + e ≤ L.length) :
    L = L.take s ++ (L.drop s).take (L.length - s - e) ++ L.drop (L.length - e) := by
  have h1 : L.drop (L.length - e) = (L.drop s).drop (L.length - s - e) := by
    rw [List.drop_drop]; congr 1; omega
  rw [h1, List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem trim_of_specs (A B : List Nat) (s e : Nat) (hs : s ≤ min A.length B.length)
    (hpre : A.take s = B.take s)
    (he : e ≤ min (A.length - s) (B.length - s))
    (hsuf : A.drop (A.length - e) = B.drop (B.length - e)) :
    (s = min A.length B.length ∨ ∃ x y, A[s]? = some x ∧ B[s]? = some y ∧ x ≠ y) →
    (e = min (A.length - s) (B.length - s) ∨ (e < min (A.length - s) (B.length - s) ∧
      ∃ x y, A[A.length - 1 - e]? = some x ∧ B[B.length - 1 - e]? = some y ∧ x ≠ y)) →
    Trim A B (A.take s) ((A.drop s).take (A.length - s - e)) ((B.drop s).take (B.length - s - e))
      (A.drop (A.length - e)) := by
  have hA := decomp A s e (by omega)
  have hB := decomp B s e (by omega)
  have nA : s + e ≤ A.length := by omega
  have nB : s + e ≤ B.length := by omega
  have nm : e ≤ A.length - s ∧ e ≤ B.length - s := ⟨by omega, by omega⟩
  intro hmax hemax
  rw [← hpre, ← hsuf] at hB
  have lenA : ((A.drop s).take (A.length - s - e)).length = A.length - s - e := by
    simp <;> omega
  have lenB : ((B.drop s).take (B.length - s - e)).length = B.length - s - e := by
    simp <;> omega
  refine ⟨hA, hB, ?_, ?_⟩
  · intro x u y v h1 h2
    have g1 : A[s]? = some x := by
      have : ((A.drop s).take (A.length - s - e))[0]? = some x := by rw [h1]; simp
      rw [List.getElem?_take, if_pos (by rw [h1] at lenA; simp at lenA; omega), List.getElem?_drop] at this; simpa using this
    have g2 : B[s]? = some y := by
      have : ((B.drop s).take (B.length - s - e))[0]? = some y := by rw [h2]; simp
      rw [List.getElem?_take, if_pos (by rw [h2] at lenB; simp at lenB; omega), List.getElem?_drop] at this; simpa using this
    rcases hmax with hm | ⟨p, q, hp, hq, hpq⟩
    · exfalso
      have h3 := (List.getElem?_eq_some_iff.mp g1).1
      have h4 := (List.getElem?_eq_some_iff.mp g2).1
      omega
    · rw [g1] at hp; rw [g2] at hq
      have := Option.some.inj hp; have := Option.some.inj hq
      subst_vars; exact hpq
  · intro x u y v h1 h2
    have l1 : 0 < ((A.drop s).take (A.length - s - e)).length := by
      have := congrArg List.length h1; simp at this; omega
    have l2 : 0 < ((B.drop s).take (B.length - s - e)).length := by
      have := congrArg List.length h2; simp at this; omega
    have g1 : A[A.length - 1 - e]? = some x := by
      have := congrArg (fun l => l[0]?) h1
      simp only [List.getElem?_cons_zero] at this
      rw [List.getElem?_reverse l1, lenA] at this
      rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop] at this
      have e1 : s + (A.length - s - e - 1) = A.length - 1 - e := by omega
      simp at this; rwa [e1] at this
    have g2 : B[B.length - 1 - e]? = some y := by
      have := congrArg (fun l => l[0]?) h2
      simp only [List.getElem?_cons_zero] at this
      rw [List.getElem?_reverse l2, lenB] at this
      rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop] at this
      have e1 : s + (B.length - s - e - 1) = B.length - 1 - e := by omega
      simp at this; rwa [e1] at this
    rcases hemax with hm | ⟨_, p, q, hp, hq, hpq⟩
    · exfalso; omega
    · rw [g1] at hp; rw [g2] at hq
      have := Option.some.inj hp; have := Option.some.inj hq
      subst_vars; exact hpq

end Myers
