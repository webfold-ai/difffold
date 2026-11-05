import TraceInv
import Wf
import Mirror
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! Ghost state of the traceback: the pairs recorded in the image table, and the live part of the stack. -/

def Pto (n : Nat) (tb : List Std.Usize) : List (Nat × Nat) :=
  (List.range' 1 n).filterMap (fun x => if (tb[x]!).val = 0 then none else some (x, (tb[x]!).val))

theorem mem_Pto {n : Nat} {tb : List Std.Usize} {x y : Nat} :
    (x, y) ∈ Pto n tb ↔ 1 ≤ x ∧ x ≤ n ∧ (tb[x]!).val = y ∧ y ≠ 0 := by
  unfold Pto
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hf⟩
    rw [List.mem_range'] at ha
    by_cases h0 : (tb[a]!).val = 0
    · rw [if_pos h0] at hf
      exact absurd hf (by simp)
    · rw [if_neg h0] at hf
      have := Option.some.inj hf
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
      obtain ⟨i, hi, hia⟩ := ha
      exact ⟨by omega, by omega, rfl, h0⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨x, ?_, ?_⟩
    · rw [List.mem_range']; exact ⟨x - 1, by omega, by omega⟩
    · have h4' : ¬ (tb[x]!).val = 0 := by rw [h3]; exact h4
      rw [if_neg h4', h3]

theorem nodup_Pto (n : Nat) (tb : List Std.Usize) : (Pto n tb).Nodup := by
  unfold Pto
  apply List.Nodup.filterMap _ List.nodup_range'
  intro a a' b hb hb'
  by_cases h0 : (tb[a]!).val = 0
  · rw [if_pos h0] at hb; exact absurd hb (by simp)
  · by_cases h0' : (tb[a']!).val = 0
    · rw [if_pos h0'] at hb'; exact absurd hb' (by simp)
    · rw [if_neg h0] at hb
      rw [if_neg h0'] at hb'
      have e1 := Option.mem_def.mp hb
      have e2 := Option.mem_def.mp hb'
      have := Option.some.inj (e1.trans e2.symm)
      exact (Prod.mk.inj this).1

theorem Pto_set {n : Nat} {tb : List Std.Usize} {x : Nat} (hx1 : 1 ≤ x) (hxn : x ≤ n) (hxl : x < tb.length)
    (h0 : (tb[x]!).val = 0) (y : Std.Usize) (hy : y.val ≠ 0) :
    (Pto n (tb.set x y)).Perm (Pto n tb ++ [(x, y.val)]) := by
  rw [List.perm_ext_iff_of_nodup (nodup_Pto _ _)]
  · intro ⟨a, b⟩
    rw [List.mem_append, mem_Pto, mem_Pto, List.mem_singleton, Prod.mk.injEq]
    by_cases hax : a = x
    · subst hax
      rw [getG_set_eq _ _ _ hxl]
      constructor
      · rintro ⟨_, _, h3, h4⟩; exact Or.inr ⟨rfl, h3.symm⟩
      · rintro (⟨_, _, h3, _⟩ | ⟨_, h2⟩)
        · rw [h0] at h3; exact absurd h3.symm (by omega)
        · exact ⟨hx1, hxn, h2.symm, by rw [h2]; exact hy⟩
    · rw [getG_set_ne _ _ _ _ hax]
      constructor
      · rintro h; exact Or.inl h
      · rintro (h | ⟨h, _⟩)
        · exact h
        · exact absurd h hax
  · rw [List.nodup_append]
    refine ⟨nodup_Pto _ _, List.nodup_singleton _, ?_⟩
    rintro ⟨a, b⟩ hp q hq e
    rw [List.mem_singleton] at hq
    subst hq
    have h := mem_Pto.mp hp
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rw [h0] at h
    exact h.2.2.2 h.2.2.1.symm

def stk (si sj : List Std.Usize) (top : Nat) : List (Nat × Nat) :=
  (List.range top).map (fun k => ((si[k]!).val, (sj[k]!).val))

theorem stk_push {si sj si' sj' : List Std.Usize} {top x y : Nat}
    (hp : ∀ k < top, si'[k]! = si[k]! ∧ sj'[k]! = sj[k]!) (hx : (si'[top]!).val = x) (hy : (sj'[top]!).val = y) :
    stk si' sj' (top + 1) = stk si sj top ++ [(x, y)] := by
  unfold stk
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    rw [(hp k hk).1, (hp k hk).2]
  · show [((si'[top]!).val, (sj'[top]!).val)] = [(x, y)]
    rw [hx, hy]

theorem stk_prefix {si sj si' sj' : List Std.Usize} {top : Nat}
    (hp : ∀ k < top, si'[k]! = si[k]! ∧ sj'[k]! = sj[k]!) : stk si' sj' top = stk si sj top := by
  unfold stk
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [(hp k hk).1, (hp k hk).2]

def ssum (la lb : Nat → Nat) (L : List (Nat × Nat)) : Nat :=
  (L.map (fun w => (w.1 - la w.1 + 1) + (w.2 - lb w.2 + 1))).sum

theorem solsOf_exists {la lb : Nat → Nat} {ren : Nat → Nat → Nat} (hA : WfL la) (hB : WfL lb) {n m : Nat} :
    ∀ L : List (Nat × Nat), (∀ w ∈ L, 1 ≤ w.1 ∧ w.1 ≤ n ∧ 1 ≤ w.2 ∧ w.2 ≤ m) → ∃ MS, SolsOf la lb ren L MS := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; exact ⟨[], SolsOf.nil⟩
  | append_singleton L w ih =>
    intro h
    obtain ⟨MS, hMS⟩ := ih (fun u hu => h u (List.mem_append_left _ hu))
    have hw := h w (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨M, hv, hr, hc⟩ := exists_map (ren := ren) hA hB _ (la w.1) w.1 (lb w.2) w.2
      (by have := (hA.1 w.1 hw.1).1; omega) (by have := (hB.1 w.2 hw.2.2.1).1; omega)
      (fun u h1 h2 => hA.2 w.1 u h1 h2) (fun u h1 h2 => hB.2 w.2 u h1 h2) rfl
    exact ⟨MS ++ M, SolsOf.snoc hMS ⟨hv, hr, hc⟩⟩

end difffold_lines_extract
