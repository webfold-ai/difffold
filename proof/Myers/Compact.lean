import Script
import Splice
/-! Sequential models of the three helpers of `diff_ids` (`compact_ids`, `mark_ids`, `scatter_flags`), which
the Rust code runs by halving, and the lemma that compaction followed by scattering is `expand`. -/
open scoped List
namespace Myers

/-- Positions (offset by `b`) of the elements of `xs` that pass `keep`. -/
def posOf (keep : Nat → Bool) : List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, b => if keep x then b :: posOf keep xs (b + 1) else posOf keep xs (b + 1)

/-- Flags `true` at the positions of the elements that fail `keep`. -/
def editOf (keep : Nat → Bool) : List Nat → Nat → List Bool → List Bool
  | [], _, e => e
  | x :: xs, b, e => editOf keep xs (b + 1) (if keep x then e else e.set b true)

/-- Copy `r[k]` to position `pos[k]`. -/
def scatterOf : List Bool → List Nat → List Bool → List Bool
  | r :: rs, p :: ps, out => scatterOf rs ps (out.set p r)
  | _, _, out => out

theorem posOf_append (keep) (xs ys : List Nat) (b : Nat) :
    posOf keep (xs ++ ys) b = posOf keep xs b ++ posOf keep ys (b + xs.length) := by
  induction xs generalizing b with
  | nil => simp [posOf]
  | cons x xs ih =>
    simp only [List.cons_append, posOf, List.length_cons]
    split
    · simp [ih, Nat.add_assoc, Nat.add_comm 1]
    · rw [ih]; simp [Nat.add_assoc, Nat.add_comm 1]

theorem editOf_append (keep) (xs ys : List Nat) (b : Nat) (e : List Bool) :
    editOf keep (xs ++ ys) b e = editOf keep ys (b + xs.length) (editOf keep xs b e) := by
  induction xs generalizing b e with
  | nil => simp [editOf]
  | cons x xs ih =>
    simp only [List.cons_append, editOf, List.length_cons]
    rw [ih]; congr 1; omega

theorem scatterOf_append (r1 r2 : List Bool) (p1 p2 : List Nat) (out : List Bool) (h : r1.length = p1.length) :
    scatterOf (r1 ++ r2) (p1 ++ p2) out = scatterOf r2 p2 (scatterOf r1 p1 out) := by
  induction r1 generalizing p1 out with
  | nil =>
    have : p1 = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
    subst this; simp [scatterOf]
  | cons r r1 ih =>
    cases p1 with
    | nil => simp at h
    | cons p p1 => simp only [List.cons_append, scatterOf]; exact ih _ _ (by simpa using h)

theorem length_scatterOf (r : List Bool) (p : List Nat) (out : List Bool) :
    (scatterOf r p out).length = out.length := by
  induction r generalizing p out with
  | nil => simp [scatterOf]
  | cons x r ih => cases p with
    | nil => simp [scatterOf]
    | cons q p => simp only [scatterOf]; rw [ih]; simp

theorem length_editOf (keep) (xs : List Nat) (b : Nat) (e : List Bool) :
    (editOf keep xs b e).length = e.length := by
  induction xs generalizing b e with
  | nil => simp [editOf]
  | cons x xs ih => simp only [editOf]; rw [ih]; split <;> simp

theorem mem_posOf (keep) (xs : List Nat) (b : Nat) : ∀ q ∈ posOf keep xs b, b ≤ q ∧ q < b + xs.length := by
  induction xs generalizing b with
  | nil => simp [posOf]
  | cons x xs ih =>
    intro q hq
    simp only [posOf] at hq
    split at hq
    · rcases List.mem_cons.mp hq with h | h
      · subst h; simp
      · have := ih (b + 1) q h; simp; omega
    · have := ih (b + 1) q hq; simp; omega

theorem splice_full (l d : List Bool) (h : d.length = l.length) : splice l 0 d = d := by
  unfold splice; simp [h]

theorem length_posOf (keep) (xs : List Nat) (b : Nat) : (posOf keep xs b).length = (xs.filter keep).length := by
  induction xs generalizing b with
  | nil => simp [posOf]
  | cons x xs ih =>
    simp only [posOf, List.filter_cons]
    split <;> simp [ih]

theorem set_mid (pre : List Bool) (y z : Bool) (rest : List Bool) :
    (pre ++ y :: rest).set pre.length z = pre ++ z :: rest := by
  induction pre with
  | nil => simp
  | cons a pre ih => simpa using ih

theorem editOf_set (keep) (xs : List Nat) (b i : Nat) (hi : i < b) (l : List Bool) (z : Bool) :
    editOf keep xs b (l.set i z) = (editOf keep xs b l).set i z := by
  induction xs generalizing b l with
  | nil => simp [editOf]
  | cons x xs ih =>
    simp only [editOf]
    by_cases hx : keep x = true
    · simp only [hx, if_true]; exact ih (b + 1) (by omega) l
    · simp only [hx, if_false]
      have : (l.set i z).set b true = (l.set b true).set i z := List.set_comm _ _ (by omega)
      rw [this]; exact ih (b + 1) (by omega) _

/-- Compacting the ids that pass `keep` and scattering the solved flags back is `expand`. -/
theorem compact_scatter (keep : Nat → Bool) : ∀ (xs : List Nat) (pre0 post0 r : List Bool),
    r.length = (xs.filter keep).length →
    scatterOf r (posOf keep xs pre0.length)
      (editOf keep xs pre0.length (pre0 ++ List.replicate xs.length false ++ post0)) =
    pre0 ++ expand keep xs r ++ post0 := by
  intro xs
  induction xs with
  | nil => intro pre0 post0 r h; simp [posOf, editOf, scatterOf, expand]
  | cons x xs ih =>
    intro pre0 post0 r h
    have hrep : pre0 ++ List.replicate (x :: xs).length false ++ post0 =
        pre0 ++ false :: (List.replicate xs.length false ++ post0) := by simp [List.replicate_succ]
    by_cases hx : keep x = true
    · simp only [List.filter_cons, hx, if_true, List.length_cons] at h
      cases r with
      | nil => simp at h
      | cons r0 rs =>
        simp only [posOf, editOf, hx, if_true, expand, List.headD_cons, List.tail_cons, scatterOf]
        rw [hrep, ← editOf_set keep xs (pre0.length + 1) pre0.length (by omega), set_mid pre0 false r0]
        have := ih (pre0 ++ [r0]) post0 rs (by simpa using h)
        simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at this ⊢
        exact this
    · have hx' : keep x = false := by simpa using hx
      simp only [List.filter_cons, hx', List.length_cons] at h
      simp only [posOf, editOf, hx', expand]
      simp only [Bool.false_eq_true, if_false]
      rw [hrep, set_mid pre0 false true]
      have := ih (pre0 ++ [true]) post0 r (by simpa using h)
      simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at this ⊢
      exact this

end Myers
