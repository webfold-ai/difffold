import Oriented
import Bridge
import Par
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! Well formed trees, and the distance of two of them as computed by the real `ted_oriented`. -/

/-- The 1-based leftmost-leaf map of a tree (the identity beyond its last node). -/
def laOf (a : ted.PostTree) : Nat → Nat :=
  fun u => if 1 ≤ u ∧ u ≤ a.label.length then (a.lml.val[u - 1]!).val else u

/-- The 1-based children of the 1-based node `p`. -/
def kdOf (a : ted.PostTree) (p : Nat) : List Nat := (a.kids.val[p - 1]!).val.map (fun c => c.val + 1)

/-- A tree whose arrays describe one ordered tree in postorder: the leftmost-leaf map is well formed with the
last node as root, the child lists are the ascending lists of children, and the keyroots are as `from_kids`
computes them. -/
structure PT.Wf (a : ted.PostTree) : Prop where
  pos : 1 ≤ a.label.length
  n2 : a.lml.length = a.label.length
  n3 : a.kind.length = a.label.length
  n4 : a.kids.length = a.label.length
  wfl : WfL (laOf a)
  root : laOf a a.label.length = 1
  sorted : ∀ p, 1 ≤ p → p ≤ a.label.length → (kdOf a p).Pairwise (· < ·)
  par : ∀ p c, 1 ≤ p → p ≤ a.label.length → (c ∈ kdOf a p ↔ 1 ≤ c ∧ Par (laOf a) a.label.length c p)
  krs : a.keyroots.val.Pairwise (fun x y => x.val < y.val)
  krt : ∀ v, InKR a.keyroots.val v ↔ LastWithLml a.lml.val a.label.length v

/-- The distance between two trees by the textbook recursion. -/
def TED (a b : ted.PostTree) : Nat := D (laOf a) (laOf b) (rcost a b) 1 a.label.length 1 b.label.length

/-- The context of two trees at threshold `T`. -/
def mkCtx (a b : ted.PostTree) (T : Nat) : Ctx :=
  { la := laOf a, lb := laOf b, ren := rcost a b, t := T, li := 0, lj := 0,
    n := a.label.length, m := b.label.length, i0 := 0, j0 := 0 }

theorem mkCtx_ted (a b : ted.PostTree) (T : Nat) : (mkCtx a b T).ted = TED a b := rfl

theorem mkCtx_link (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (hna : a.label.length < 2 ^ 14)
    (hnb : b.label.length < 2 ^ 14) (T : Nat) (hT : T ≤ a.label.length + b.label.length) :
    (mkCtx a b T).Link a b := by
  have hw : (a.label.length + 1) * (2 * T + 1) < 2 ^ 32 := by
    have : (a.label.length + 1) * (2 * T + 1) ≤ 2 ^ 14 * 2 ^ 16 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  refine ⟨rfl, hA.n2, hA.n3, rfl, hB.n2, hB.n3, ?_, ?_, fun _ _ => rfl,
    show a.label.length < 2 ^ 31 by omega, show b.label.length < 2 ^ 31 by omega,
    show (a.label.length + 1) * (2 * T + 1) < 2 ^ 32 from hw, show 2 * T + 3 < 2 ^ 31 by omega⟩
  · intro u h1 h2
    simp only [mkCtx, laOf]
    rw [if_pos ⟨h1, h2⟩]
  · intro u h1 h2
    simp only [mkCtx, laOf]
    rw [if_pos ⟨h1, h2⟩]

theorem mkCtx_keys (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (T : Nat) : (mkCtx a b T).Keys a b := by
  have fa := keyroot_facts (mkCtx a b T) a hA.wfl hA.n2
    (fun u h1 h2 => by simp only [mkCtx, laOf]; rw [if_pos ⟨h1, h2⟩]) hA.krs (fun v => by rw [hA.n2]; exact hA.krt v)
  have fb := keyroot_facts (mkCtx b a T) b hB.wfl hB.n2
    (fun u h1 h2 => by simp only [mkCtx, laOf]; rw [if_pos ⟨h1, h2⟩]) hB.krs (fun v => by rw [hB.n2]; exact hB.krt v)
  exact ⟨hA.wfl, hB.wfl, fa.1, fb.1, fa.2.1, fb.2.1, fa.2.2, fb.2.2⟩

/-- `ted_oriented` on well formed trees returns the distance. -/
theorem ted_oriented_wf (a b : ted.PostTree) (hA : PT.Wf a) (hB : PT.Wf b) (hna : a.label.length < 2 ^ 14)
    (hnb : b.label.length < 2 ^ 14) (hla : ∀ j < a.label.length, (a.label.val[j]!).val < 2 ^ 31)
    (st : ted.Stats) :
    ted.ted_oriented a b st ⦃ r => r.1.val = TED a b ⦄ := by
  have hw : ∀ T, T ≤ a.label.length + b.label.length →
      (b.label.length + 1) * (2 * T + 1) < 2 ^ 32 := fun T hT => by
    have : (b.label.length + 1) * (2 * T + 1) ≤ 2 ^ 14 * 2 ^ 16 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have := ted_oriented_spec (mkCtx a b 0) a b (mkCtx_keys a b hA hB 0)
    (fun T hT => mkCtx_link a b hA hB hna hnb T hT)
    (fun T hT => hw T hT) hA.pos hB.pos
    (by simp only [mkCtx, laOf]; rw [if_pos ⟨hA.pos, Nat.le_refl _⟩]; exact (by simpa [laOf, hA.pos] using hA.root))
    (by simp only [mkCtx, laOf]; rw [if_pos ⟨hB.pos, Nat.le_refl _⟩]; exact (by simpa [laOf, hB.pos] using hB.root))
    hla st
  exact this

end difffold_lines_extract
