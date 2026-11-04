import Lcs
/-! Edit scripts as flag lists: soundness of the script representation (c), the greedy trims (a), the
dropping of lines that occur on one side only (b), and the divide step (d). Everything here is a
statement about the Lean model of `src/lines.rs`; see the status table in `proof/README.md`. -/
open scoped List
namespace Myers

/-- The elements whose flag is `false`, in order. A flag list shorter than the list keeps nothing past
its end; the scripts used below always have the right length. -/
def kept {α : Type} : List α → List Bool → List α
  | x :: xs, f :: fs => if f then kept xs fs else x :: kept xs fs
  | _, _ => []

theorem kept_nil_right {α : Type} (xs : List α) : kept xs [] = [] := by cases xs <;> simp [kept]

theorem kept_sublist {α : Type} : ∀ (xs : List α) (fs : List Bool), kept xs fs <+ xs := by
  intro xs
  induction xs with
  | nil => intro fs; simp [kept]
  | cons x xs ih =>
    intro fs
    cases fs with
    | nil => simp [kept]
    | cons f fs =>
      cases f
      · simpa [kept] using (ih fs).cons_cons x
      · simpa [kept] using (ih fs).cons x

theorem kept_append {α : Type} : ∀ (xs1 xs2 : List α) (fs1 fs2 : List Bool), fs1.length = xs1.length →
    kept (xs1 ++ xs2) (fs1 ++ fs2) = kept xs1 fs1 ++ kept xs2 fs2 := by
  intro xs1 xs2
  induction xs1 with
  | nil => intro fs1 fs2 h; have : fs1 = [] := List.length_eq_zero_iff.mp (by simpa using h)
           subst this; simp [kept]
  | cons x xs ih =>
    intro fs1 fs2 h
    cases fs1 with
    | nil => simp at h
    | cons f fs1 =>
      have h' : fs1.length = xs.length := by simpa using h
      cases f <;> simp [kept, ih fs1 fs2 h']

theorem kept_rep_false {α : Type} : ∀ xs : List α, kept xs (List.replicate xs.length false) = xs := by
  intro xs; induction xs with
  | nil => simp [kept]
  | cons x xs ih => simp [List.replicate_succ, kept, ih]

theorem kept_rep_true {α : Type} : ∀ xs : List α, kept xs (List.replicate xs.length true) = [] := by
  intro xs; induction xs with
  | nil => simp [kept]
  | cons x xs ih => simp [List.replicate_succ, kept, ih]

theorem length_kept {α : Type} : ∀ (xs : List α) (fs : List Bool), fs.length = xs.length →
    (kept xs fs).length + fs.count true = xs.length := by
  intro xs
  induction xs with
  | nil => intro fs h; have : fs = [] := List.length_eq_zero_iff.mp (by simpa using h)
           subst this; simp [kept]
  | cons x xs ih =>
    intro fs h
    cases fs with
    | nil => simp at h
    | cons f fs =>
      have h' : fs.length = xs.length := by simpa using h
      have := ih fs h'
      cases f <;> simp [kept] <;> omega

/-- Every sublist is the kept part of some script. -/
theorem exists_flags {α : Type} {c xs : List α} (h : c <+ xs) :
    ∃ fs : List Bool, fs.length = xs.length ∧ kept xs fs = c := by
  induction h with
  | slnil => exact ⟨[], rfl, by simp [kept]⟩
  | cons x h ih =>
    obtain ⟨fs, h1, h2⟩ := ih
    exact ⟨true :: fs, by simp [h1], by simp [kept, h2]⟩
  | cons_cons x h ih =>
    obtain ⟨fs, h1, h2⟩ := ih
    exact ⟨false :: fs, by simp [h1], by simp [kept, h2]⟩

/-! ### (c) the script representation -/

/-- A script is valid when the lines kept on the two sides are equal lists. -/
def Valid (a b : List Nat) (da di : List Bool) : Prop :=
  da.length = a.length ∧ di.length = b.length ∧ kept a da = kept b di

/-- Number of deleted plus inserted lines. -/
def cost (da di : List Bool) : Nat := da.count true + di.count true

def Optimal (a b : List Nat) (da di : List Bool) : Prop :=
  Valid a b da di ∧ (kept a da).length = lcs a b

theorem valid_le {a b da di} (h : Valid a b da di) : (kept a da).length ≤ lcs a b :=
  lcs_le a b _ (kept_sublist a da) (h.2.2 ▸ kept_sublist b di)

/-- The cost of a valid script is `|a| + |b| - 2 * kept`. -/
theorem cost_eq {a b da di} (h : Valid a b da di) :
    cost da di + 2 * (kept a da).length = a.length + b.length := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := length_kept a da h1
  have e2 := length_kept b di h2
  rw [← h3] at e2
  unfold cost; omega

/-- No valid script is cheaper than `|a| + |b| - 2 * lcs`. -/
theorem cost_ge {a b da di} (h : Valid a b da di) : a.length + b.length ≤ cost da di + 2 * lcs a b := by
  have := cost_eq h; have := valid_le h; omega

theorem optimal_cost {a b da di} (h : Optimal a b da di) :
    cost da di + 2 * lcs a b = a.length + b.length := by
  have := cost_eq h.1; rw [h.2] at this; exact this

/-- Optimal means cost `|a| + |b| - 2 * lcs`, and conversely. -/
theorem optimal_iff {a b da di} (h : Valid a b da di) :
    Optimal a b da di ↔ cost da di + 2 * lcs a b = a.length + b.length := by
  constructor
  · intro ho; exact optimal_cost ho
  · intro hc; refine ⟨h, ?_⟩
    have := cost_eq h; have := valid_le h; omega

/-- A valid script with the optimal cost exists. -/
theorem exists_optimal (a b : List Nat) : ∃ da di, Optimal a b da di := by
  obtain ⟨c, h1, h2, h3⟩ := lcs_ex a b
  obtain ⟨da, e1, e2⟩ := exists_flags h1
  obtain ⟨di, f1, f2⟩ := exists_flags h2
  exact ⟨da, di, ⟨e1, f1, by rw [e2, f2]⟩, by rw [e2, h3]⟩

/-- An optimal script is at most as expensive as any valid script. -/
theorem optimal_min {a b da di da' di'} (ho : Optimal a b da di) (hv : Valid a b da' di') :
    cost da di ≤ cost da' di' := by
  have := optimal_cost ho; have := cost_ge hv; omega

/-! ### (a) greedy trimming of equal ends -/

theorem opt_trim {p a b s : List Nat} {d e : List Bool} (h : Optimal a b d e) :
    Optimal (p ++ a ++ s) (p ++ b ++ s)
      (List.replicate p.length false ++ d ++ List.replicate s.length false)
      (List.replicate p.length false ++ e ++ List.replicate s.length false) := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  have ka : kept (p ++ a ++ s) (List.replicate p.length false ++ d ++ List.replicate s.length false)
      = p ++ kept a d ++ s := by
    rw [List.append_assoc, List.append_assoc, kept_append _ _ _ _ (by simp), kept_append _ _ _ _ h1,
      kept_rep_false, kept_rep_false]; simp
  have kb : kept (p ++ b ++ s) (List.replicate p.length false ++ e ++ List.replicate s.length false)
      = p ++ kept b e ++ s := by
    rw [List.append_assoc, List.append_assoc, kept_append _ _ _ _ (by simp), kept_append _ _ _ _ h2,
      kept_rep_false, kept_rep_false]; simp
  refine ⟨⟨by simp [h1], by simp [h2], by rw [ka, kb, h3]⟩, ?_⟩
  rw [ka, lcs_trim, ← h4]; simp; omega

/-! ### (b) lines whose id occurs on one side only -/

/-- Scatter the flags of the compacted list back: lines failing `keep` are certain edits (`true`). -/
def expand (keep : Nat → Bool) : List Nat → List Bool → List Bool
  | [], _ => []
  | x :: a, r => if keep x then r.headD true :: expand keep a r.tail else true :: expand keep a r

theorem length_expand (keep : Nat → Bool) : ∀ (a : List Nat) (r : List Bool), (expand keep a r).length = a.length := by
  intro a; induction a with
  | nil => intro r; simp [expand]
  | cons x a ih => intro r; unfold expand; split <;> simp [ih]

theorem kept_expand (keep : Nat → Bool) : ∀ (a : List Nat) (r : List Bool),
    kept a (expand keep a r) = kept (a.filter keep) r := by
  intro a; induction a with
  | nil => intro r; simp [expand, kept]
  | cons x a ih =>
    intro r
    by_cases hx : keep x = true
    · rw [List.filter_cons_of_pos hx]
      cases r with
      | nil => simp only [expand, hx, if_true]; simp [kept]; rw [ih []]; exact kept_nil_right _
      | cons f r => cases f <;> simp [expand, hx, kept, ih]
    · have hx' : keep x = false := by simpa using hx
      rw [List.filter_cons_of_neg hx]
      simp [expand, hx', kept, ih]

theorem lcs_filter (a b : List Nat) :
    lcs (a.filter (fun x => decide (x ∈ b))) (b.filter (fun x => decide (x ∈ a))) = lcs a b := by
  apply Nat.le_antisymm
  · exact lcs_mono _ _ _ _ (List.filter_sublist) (List.filter_sublist)
  · obtain ⟨c, h1, h2, h3⟩ := lcs_ex a b
    have ca : c.filter (fun x => decide (x ∈ b)) = c :=
      List.filter_eq_self.mpr (fun x hx => by simpa using h2.subset hx)
    have cb : c.filter (fun x => decide (x ∈ a)) = c :=
      List.filter_eq_self.mpr (fun x hx => by simpa using h1.subset hx)
    have s1 : c <+ a.filter (fun x => decide (x ∈ b)) := by simpa [ca] using h1.filter (fun x => decide (x ∈ b))
    have s2 : c <+ b.filter (fun x => decide (x ∈ a)) := by simpa [cb] using h2.filter (fun x => decide (x ∈ a))
    rw [← h3]; exact lcs_le _ _ c s1 s2

/-- An optimal script for the compacted lists, scattered back, is optimal for the originals. -/
theorem filter_optimal {a b : List Nat} {r s : List Bool}
    (h : Optimal (a.filter (fun x => decide (x ∈ b))) (b.filter (fun x => decide (x ∈ a))) r s) :
    Optimal a b (expand (fun x => decide (x ∈ b)) a r) (expand (fun x => decide (x ∈ a)) b s) := by
  obtain ⟨⟨_, _, h3⟩, h4⟩ := h
  refine ⟨⟨length_expand _ _ _, length_expand _ _ _, ?_⟩, ?_⟩
  · rw [kept_expand, kept_expand, h3]
  · rw [kept_expand, h4, lcs_filter]

/-! ### (d) the divide step -/

/-- The point `(x, y)` lies on an optimal path. -/
def Split (a b : List Nat) (x y : Nat) : Prop :=
  lcs a b = lcs (a.take x) (b.take y) + lcs (a.drop x) (b.drop y)

theorem split_ge (a b : List Nat) (x y : Nat) :
    lcs (a.take x) (b.take y) + lcs (a.drop x) (b.drop y) ≤ lcs a b := by
  have := lcs_append_ge (a.take x) (a.drop x) (b.take y) (b.drop y)
  simpa using this

/-- Solving both halves optimally gives an optimal whole. -/
theorem optimal_append {a b : List Nat} {x y : Nat} (hs : Split a b x y) {d1 e1 d2 e2 : List Bool}
    (h1 : Optimal (a.take x) (b.take y) d1 e1) (h2 : Optimal (a.drop x) (b.drop y) d2 e2) :
    Optimal a b (d1 ++ d2) (e1 ++ e2) := by
  obtain ⟨⟨l1, l2, k1⟩, o1⟩ := h1
  obtain ⟨⟨m1, m2, k2⟩, o2⟩ := h2
  have ka : kept a (d1 ++ d2) = kept (a.take x) d1 ++ kept (a.drop x) d2 := by
    have := kept_append (a.take x) (a.drop x) d1 d2 l1
    rwa [List.take_append_drop] at this
  have kb : kept b (e1 ++ e2) = kept (b.take y) e1 ++ kept (b.drop y) e2 := by
    have := kept_append (b.take y) (b.drop y) e1 e2 l2
    rwa [List.take_append_drop] at this
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [l1, m1]; omega
  · simp [l2, m2]; omega
  · rw [ka, kb, k1, k2]
  · rw [ka]; simp [o1, o2]; unfold Split at hs; omega

end Myers
