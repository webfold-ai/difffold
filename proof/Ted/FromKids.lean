import DifffoldTed
open Aeneas Aeneas.Std Result ControlFlow
namespace difffold_lines_extract

/-! Theorems over the Aeneas-extracted `ted_core::from_kids`, the copy of `PostTree::from_kids` of the real
`src/ted.rs` (tied to it by `tests/ted_core.rs`).

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

@[step] theorem from_kids_loop0_spec (n : Std.Usize) (lml : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (hi : i.val ≤ n.val) (hlen : lml.length = i.val) :
    ted_core.from_kids_loop0 n lml i ⦃ r => r.length = n.val ⦄ := by
  unfold ted_core.from_kids_loop0
  apply loop.spec_decr_nat
    (measure := fun p => n.val - p.2.val)
    (inv := fun p => p.2.val ≤ n.val ∧ p.1.length = p.2.val)
  · intro p hp
    obtain ⟨o, c⟩ := p
    obtain ⟨hc, hl⟩ := hp
    unfold ted_core.from_kids_loop0.body
    dsimp only at hc hl ⊢
    split
    · step*
      have hlen1 : lml1.length = o.length + 1 := by simp [alloc.vec.Vec.length, lml1_post]
      refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
    · rename_i hnot
      simp only [WP.spec_ok]
      scalar_tac
  · exact ⟨hi, hlen⟩

/-- Loop 1 fills `lml` in increasing order of node. -/
@[step] theorem from_kids_loop1_spec (kids : Slice (alloc.vec.Vec Std.U32)) (n : Std.Usize)
    (lml : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (hn : n.val < 2 ^ 31) (hk : n.val ≤ kids.val.length) (hlen : lml.length = n.val)
    (hvalid : ∀ j < n.val, ∀ k, FirstKid kids.val j = some k → k.val < j)
    (hi : i.val ≤ n.val)
    (hinv : ∀ j < i.val, LmlEq kids.val lml.val j ∧ 1 ≤ (lml.val[j]!).val ∧ (lml.val[j]!).val ≤ j + 1) :
    ted_core.from_kids_loop1 kids n lml i ⦃ r => r.length = n.val ∧
      ∀ j < n.val, LmlEq kids.val r.val j ∧ 1 ≤ (r.val[j]!).val ∧ (r.val[j]!).val ≤ j + 1 ⦄ := by
  unfold ted_core.from_kids_loop1
  apply loop.spec_decr_nat
    (measure := fun p => n.val - p.2.val)
    (inv := fun p => p.2.val ≤ n.val ∧ p.1.length = n.val ∧
      ∀ j < p.2.val, LmlEq kids.val p.1.val j ∧ 1 ≤ (p.1.val[j]!).val ∧ (p.1.val[j]!).val ≤ j + 1)
  · intro p hp
    obtain ⟨o, c⟩ := p
    obtain ⟨hc, hl, hinv'⟩ := hp
    unfold ted_core.from_kids_loop1.body
    dsimp only at hc hl hinv' ⊢
    split
    · rename_i hlt
      step*
      split
      · rename_i hleaf
        step*
        all_goals trace_state
        all_goals sorry
      · rename_i hnl
        step*
        all_goals trace_state
        all_goals sorry
    · rename_i hnot
      refine ⟨hl, fun j hj => hinv' j (by scalar_tac)⟩
  · exact ⟨hi, hlen, hinv⟩

end difffold_lines_extract
