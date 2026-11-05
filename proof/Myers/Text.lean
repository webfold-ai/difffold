import Script
/-! The text layer of the line differ, as a Lean model: the decomposition of a byte text into lines, the
application of a flag script to two line lists, and minimality of a script at line granularity (transported
from the id model of `Script.lean`, then through the trimming of equal leading and trailing lines).
Bytes are natural numbers; newline is `10`. Everything here is about the Lean model; the theorems over the
extracted Rust are in `Myers2/Real*.lean`. -/
open scoped List
namespace Myers

/-! ### Lines of a text -/

/-- The lines of a text, each keeping its terminator. The last line has none if the text does not end in a
newline, and there is never an empty line (so no empty trailing line). -/
def lines : List Nat → List (List Nat)
  | [] => []
  | x :: xs =>
    if x = 10 then [10] :: lines xs
    else match lines xs with
      | [] => [[x]]
      | l :: ls => (x :: l) :: ls

theorem lines_nl (xs : List Nat) : lines (10 :: xs) = [10] :: lines xs := by simp [lines]

theorem lines_ne_nil' (x : Nat) (hx : x ≠ 10) (xs : List Nat) (h : lines xs = []) : lines (x :: xs) = [[x]] := by
  simp [lines, hx, h]

theorem lines_ne_cons (x : Nat) (hx : x ≠ 10) (xs : List Nat) (l : List Nat) (ls : List (List Nat))
    (h : lines xs = l :: ls) : lines (x :: xs) = (x :: l) :: ls := by
  simp [lines, hx, h]

theorem lines_flatten : ∀ t : List Nat, (lines t).flatten = t
  | [] => by simp [lines]
  | x :: xs => by
    have ih := lines_flatten xs
    by_cases hx : x = 10
    · subst hx; rw [lines_nl]; simp [ih]
    · cases h : lines xs with
      | nil => rw [h] at ih; simp at ih; subst ih; rw [lines_ne_nil' x hx _ h]; simp
      | cons l ls => rw [h] at ih; rw [lines_ne_cons x hx _ _ _ h]; simp at ih ⊢; simp [← ih]

theorem lines_ne_nil : ∀ (t : List Nat), ∀ l ∈ lines t, l ≠ []
  | [] => by simp [lines]
  | x :: xs => by
    have ih := lines_ne_nil xs
    intro l hl
    by_cases hx : x = 10
    · subst hx; rw [lines_nl] at hl; simp at hl; rcases hl with h | h
      · simp [h]
      · exact ih l h
    · cases h : lines xs with
      | nil => rw [lines_ne_nil' x hx _ h] at hl; simp at hl; simp [hl]
      | cons l' ls =>
        rw [lines_ne_cons x hx _ _ _ h] at hl
        simp at hl; rcases hl with h' | h'
        · simp [h']
        · exact ih l (by rw [h]; simp [h'])

/-- Decomposing at a line boundary decomposes the lines. -/
theorem lines_append : ∀ (u v : List Nat), (u = [] ∨ u.getLast? = some 10) →
    lines (u ++ v) = lines u ++ lines v
  | [], v, _ => by simp [lines]
  | x :: u, v, h => by
    by_cases hx : x = 10
    · subst hx
      have hu : u = [] ∨ u.getLast? = some 10 := by
        rcases h with h | h
        · simp at h
        · cases u with
          | nil => simp
          | cons y u' => right; simpa [List.getLast?_cons_cons] using h
      have ih := lines_append u v hu
      rw [List.cons_append, lines_nl, lines_nl, ih]; rfl
    · have hne : u ≠ [] := by
        intro hu; subst hu
        rcases h with h | h
        · simp at h
        · simp at h; exact hx h
      have hu : u.getLast? = some 10 := by
        rcases h with h | h
        · simp at h
        · cases u with
          | nil => exact absurd rfl hne
          | cons y u' => simpa [List.getLast?_cons_cons] using h
      have ih := lines_append u v (Or.inr hu)
      obtain ⟨l, ls, hl⟩ : ∃ l ls, lines u = l :: ls := by
        cases h : lines u with
        | nil =>
          have := lines_flatten u; rw [h] at this; simp at this; exact absurd this hne
        | cons l ls => exact ⟨l, ls, rfl⟩
      have e1 : lines (x :: (u ++ v)) = (x :: l) :: (ls ++ lines v) := by
        have : lines (u ++ v) = l :: (ls ++ lines v) := by rw [ih, hl]; rfl
        exact lines_ne_cons x hx _ _ _ this
      have e2 : lines (x :: u) = (x :: l) :: ls := lines_ne_cons x hx _ _ _ hl
      rw [List.cons_append, e1, e2]; rfl

theorem lines_no_nl (t : List Nat) (h : 10 ∉ t) (ht : t ≠ []) : lines t = [t] := by
  induction t with
  | nil => exact absurd rfl ht
  | cons x xs ih =>
    have hx : x ≠ 10 := fun e => h (by simp [e])
    cases xs with
    | nil => exact lines_ne_nil' x hx _ (by simp [lines])
    | cons y ys =>
      have := ih (fun e => h (List.mem_cons_of_mem _ e)) (by simp)
      exact lines_ne_cons x hx _ _ _ this

/-- A text that is one line with its terminator. -/
theorem lines_one (u : List Nat) (hu : u ≠ []) (hl : u.getLast? = some 10) (hn : 10 ∉ u.dropLast) :
    lines u = [u] := by
  induction u with
  | nil => exact absurd rfl hu
  | cons x xs ih =>
    cases xs with
    | nil => simp at hl; subst hl; simp [lines]
    | cons y ys =>
      have hx : x ≠ 10 := fun e => hn (by simp [e, List.dropLast_cons_of_ne_nil])
      have h1 : (y :: ys).getLast? = some 10 := by simpa [List.getLast?_cons_cons] using hl
      have h2 : 10 ∉ (y :: ys).dropLast := fun e => hn (by simp [List.dropLast_cons_of_ne_nil, e])
      have := ih (by simp) h1 h2
      exact lines_ne_cons x hx _ _ _ this

/-- Peeling off the first line. -/
theorem lines_first (u v : List Nat) (hu : u ≠ []) (hl : u.getLast? = some 10) (hn : 10 ∉ u.dropLast) :
    lines (u ++ v) = u :: lines v := by
  rw [lines_append u v (Or.inr hl), lines_one u hu hl hn]; rfl

/-- The number of lines. -/
def nlines (t : List Nat) : Nat :=
  t.count 10 + (if t ≠ [] ∧ t.getLast? ≠ some 10 then 1 else 0)

theorem lines_length : ∀ t : List Nat, (lines t).length = nlines t
  | [] => by simp [lines, nlines]
  | x :: xs => by
    have ih := lines_length xs
    by_cases hx : x = 10
    · subst hx
      rw [lines_nl, List.length_cons, ih]
      cases xs with
      | nil => simp [nlines]
      | cons y ys =>
        simp [nlines, List.count_cons, List.getLast?_cons_cons]; omega
    · cases xs with
      | nil => rw [lines_ne_nil' x hx _ (by simp [lines])]; simp [nlines, hx]
      | cons y ys =>
        obtain ⟨l, ls, hl⟩ : ∃ l ls, lines (y :: ys) = l :: ls := by
          cases h : lines (y :: ys) with
          | nil => have := lines_flatten (y :: ys); rw [h] at this; simp at this
          | cons l ls => exact ⟨l, ls, rfl⟩
        rw [lines_ne_cons x hx _ _ _ hl]
        have : (l :: ls).length = nlines (y :: ys) := by rw [← hl]; exact ih
        simp only [List.length_cons] at this ⊢
        rw [this]
        simp [nlines, List.count_cons, hx, List.getLast?_cons_cons]

/-- What `lines t` is: chunks that concatenate to `t`, are nonempty, contain a newline only as their last
byte, and all end in a newline except possibly the last. These properties determine the list. -/
theorem lines_spec : ∀ t : List Nat,
    (lines t).flatten = t ∧ (∀ l ∈ lines t, l ≠ [] ∧ 10 ∉ l.dropLast) ∧
      (∀ l ∈ (lines t).dropLast, l.getLast? = some 10)
  | [] => by simp [lines]
  | x :: xs => by
    obtain ⟨i1, i2, i3⟩ := lines_spec xs
    refine ⟨lines_flatten _, ?_, ?_⟩
    · intro l hl
      refine ⟨lines_ne_nil _ l hl, ?_⟩
      by_cases hx : x = 10
      · subst hx; rw [lines_nl] at hl; simp at hl; rcases hl with h | h
        · simp [h]
        · exact (i2 l h).2
      · cases hls : lines xs with
        | nil => rw [lines_ne_nil' x hx _ hls] at hl; simp at hl; simp [hl]
        | cons l' ls =>
          rw [lines_ne_cons x hx _ _ _ hls] at hl
          simp at hl; rcases hl with h | h
          · have hl' := i2 l' (by rw [hls]; simp)
            subst h
            simp [List.dropLast_cons_of_ne_nil hl'.1, Ne.symm hx, hl'.2]
          · exact (i2 l (by rw [hls]; simp [h])).2
    · intro l hl
      by_cases hx : x = 10
      · subst hx; rw [lines_nl] at hl
        cases hls : lines xs with
        | nil => rw [hls] at hl; simp at hl
        | cons l' ls =>
          rw [hls] at hl i3
          rw [List.dropLast_cons_of_ne_nil (by simp)] at hl
          simp at hl; rcases hl with h | h
          · simp [h]
          · exact i3 l (by simpa using h)
      · cases hls : lines xs with
        | nil => rw [lines_ne_nil' x hx _ hls] at hl; simp at hl
        | cons l' ls =>
          rw [lines_ne_cons x hx _ _ _ hls] at hl
          rw [hls] at i3
          cases ls with
          | nil => simp at hl
          | cons l'' ls' =>
            simp [List.dropLast_cons_of_ne_nil] at hl
            rcases hl with h | h
            · subst h
              have := i3 l' (by simp)
              have hl'' := (i2 l' (by rw [hls]; simp)).1
              cases l' with
              | nil => exact absurd rfl hl''
              | cons a b => simpa [List.getLast?_cons_cons] using this
            · exact i3 l (by rw [List.dropLast_cons_of_ne_nil (by simp)]; simp [h])

/-! ### Applying a script to two line lists -/

/-- A script is valid for two lists when the lines kept on the two sides are equal. -/
def VL {α : Type} (a b : List α) (da di : List Bool) : Prop :=
  da.length = a.length ∧ di.length = b.length ∧ kept a da = kept b di

/-- Apply a flag script: deleted lines of `a` are dropped, inserted lines are taken from `b`, kept lines
are copied from `a`. -/
def applyS {α : Type} : List α → List α → List Bool → List Bool → List α
  | _ :: a, b, true :: da, di => applyS a b da di
  | a, y :: b, da, true :: di => y :: applyS a b da di
  | x :: a, _ :: b, false :: da, false :: di => x :: applyS a b da di
  | _, _, _, _ => []
termination_by a b _ _ => a.length + b.length

theorem applyS_eq {α : Type} : ∀ (a b : List α) (da di : List Bool), VL a b da di → applyS a b da di = b := by
  intro a b da di
  induction a, b, da, di using applyS.induct with
  | case1 x a b da di ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    rw [applyS]
    exact ih ⟨by simpa using h1, h2, by simpa [kept] using h3⟩
  | case2 a y b da di hn ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    rw [applyS]
    · rw [ih ⟨h1, by simpa using h2, by simpa [kept] using h3⟩]
    · exact hn
  | case3 x a y b da di ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    rw [applyS]
    have h3' : x :: kept a da = y :: kept b di := by simpa [kept] using h3
    obtain ⟨hxy, h4⟩ := List.cons.inj h3'
    subst hxy
    rw [ih ⟨by simpa using h1, by simpa using h2, h4⟩]
    all_goals (intros; simp_all)
  | case4 a b da di n1 n2 n3 =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    rcases a with _ | ⟨x, a'⟩ <;> rcases b with _ | ⟨y, b'⟩ <;> rcases da with _ | ⟨f, da'⟩ <;>
      rcases di with _ | ⟨g, di'⟩ <;> (try cases f) <;> (try cases g) <;>
      first | exact (n3 _ _ _ _ _ _ rfl rfl rfl rfl).elim | (simp_all [kept]; done) | simp [applyS]

/-! ### Minimal scripts on lists of lines

`Optimal` of `Script.lean` is stated for lists of natural numbers (line ids). A script is *minimal* for
arbitrary elements when it is valid and no valid script costs less. Both notions agree on the image of any
map that is injective on the elements involved. -/

def MinL {α : Type} (a b : List α) (da di : List Bool) : Prop :=
  VL a b da di ∧ ∀ da' di', VL a b da' di' → cost da di ≤ cost da' di'

theorem kept_map {α β : Type} (f : α → β) : ∀ (xs : List α) (fs : List Bool),
    kept (xs.map f) fs = (kept xs fs).map f := by
  intro xs
  induction xs with
  | nil => intro fs; simp [kept]
  | cons x xs ih =>
    intro fs
    cases fs with
    | nil => simp [kept]
    | cons g fs => cases g <;> simp [kept, ih]

theorem map_inj_of {α : Type} (f : α → Nat) : ∀ (l1 l2 : List α),
    (∀ x ∈ l1, ∀ y ∈ l2, f x = f y → x = y) → l1.map f = l2.map f → l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _ h; cases l2 with | nil => rfl | cons _ _ => simp at h
  | cons x xs ih =>
    intro l2 hinj h
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hxy : x = y := hinj x (by simp) y (by simp) h.1
      subst hxy
      rw [ih ys (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) h.2]

theorem VL_map {α : Type} (f : α → Nat) (a b : List α)
    (hinj : ∀ x ∈ a ++ b, ∀ y ∈ a ++ b, f x = f y → x = y) (da di : List Bool) :
    VL a b da di ↔ Valid (a.map f) (b.map f) da di := by
  unfold VL Valid
  rw [kept_map, kept_map]
  simp only [List.length_map]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h3]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, map_inj_of f _ _ ?_ h3⟩
    intro x hx y hy
    exact hinj x (by simpa using Or.inl ((kept_sublist a da).subset hx)) y
      (by simpa using Or.inr ((kept_sublist b di).subset hy))

theorem minL_of_optimal {α : Type} (f : α → Nat) (a b : List α)
    (hinj : ∀ x ∈ a ++ b, ∀ y ∈ a ++ b, f x = f y → x = y) {da di : List Bool}
    (h : Optimal (a.map f) (b.map f) da di) : MinL a b da di := by
  refine ⟨(VL_map f a b hinj da di).mpr h.1, ?_⟩
  intro da' di' hv
  exact optimal_min h ((VL_map f a b hinj da' di').mp hv)

theorem optimal_of_minL {α : Type} (f : α → Nat) (a b : List α)
    (hinj : ∀ x ∈ a ++ b, ∀ y ∈ a ++ b, f x = f y → x = y) {da di : List Bool}
    (h : MinL a b da di) : Optimal (a.map f) (b.map f) da di := by
  have hv := (VL_map f a b hinj da di).mp h.1
  obtain ⟨da', di', ho⟩ := exists_optimal (a.map f) (b.map f)
  have h1 : cost da di ≤ cost da' di' := h.2 da' di' ((VL_map f a b hinj da' di').mpr ho.1)
  have h2 := optimal_cost ho
  have h3 := cost_ge hv
  simp only [List.length_map] at h2 h3
  rw [optimal_iff hv]
  simp only [List.length_map]
  omega

theorem getElem?_idxOf {α : Type} [BEq α] [LawfulBEq α] : ∀ (l : List α) (x : α), x ∈ l →
    l[l.idxOf x]? = some x
  | [], x, h => by simp at h
  | y :: l, x, h => by
    by_cases hxy : x = y
    · subst hxy; simp
    · have hx : x ∈ l := by simpa [hxy] using h
      have := getElem?_idxOf l x hx
      rw [List.idxOf_cons]
      have : (y == x) = false := by simpa using Ne.symm hxy
      simp [this, getElem?_idxOf l x hx]

theorem idxOf_inj {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x y : α) (hx : x ∈ l) (hy : y ∈ l)
    (h : l.idxOf x = l.idxOf y) : x = y := by
  have h1 := getElem?_idxOf l x hx
  have h2 := getElem?_idxOf l y hy
  rw [h] at h1; rw [h1] at h2; exact Option.some.inj h2

/-- Equal leading and trailing lines may be set aside: a minimal script for the middle, padded with
`false`, is minimal for the whole. -/
theorem minL_trim (P la lb S : List (List Nat)) {da di : List Bool} (h : MinL la lb da di) :
    MinL (P ++ la ++ S) (P ++ lb ++ S)
      (List.replicate P.length false ++ da ++ List.replicate S.length false)
      (List.replicate P.length false ++ di ++ List.replicate S.length false) := by
  let f : List Nat → Nat := fun l => (P ++ la ++ lb ++ S).idxOf l
  have hf : ∀ x ∈ P ++ la ++ lb ++ S, ∀ y ∈ P ++ la ++ lb ++ S, f x = f y → x = y :=
    fun x hx y hy e => idxOf_inj _ x y hx hy e
  have h1 : ∀ x ∈ la ++ lb, ∀ y ∈ la ++ lb, f x = f y → x = y := by
    intro x hx y hy e
    refine hf x ?_ y ?_ e
    · simp at hx ⊢; rcases hx with h | h <;> simp [h]
    · simp at hy ⊢; rcases hy with h | h <;> simp [h]
  have h2 : ∀ x ∈ (P ++ la ++ S) ++ (P ++ lb ++ S), ∀ y ∈ (P ++ la ++ S) ++ (P ++ lb ++ S), f x = f y → x = y := by
    intro x hx y hy e
    refine hf x ?_ y ?_ e
    · simp at hx ⊢; grind
    · simp at hy ⊢; grind
  have ho := opt_trim (p := P.map f) (s := S.map f) (optimal_of_minL f la lb h1 h)
  have e1 : (P ++ la ++ S).map f = P.map f ++ la.map f ++ S.map f := by simp
  have e2 : (P ++ lb ++ S).map f = P.map f ++ lb.map f ++ S.map f := by simp
  simp only [List.length_map] at ho
  apply minL_of_optimal f _ _ h2
  rw [e1, e2]; exact ho

/-! ### Exact numbering of lines -/

/-- `ia` and `ib` number the lines `la` and `lb` exactly: two positions carry the same id if and only if
they carry the same line, across both sides. -/
def IdsExact {α : Type} (la lb : List α) (ia ib : List Nat) : Prop :=
  ia.length = la.length ∧ ib.length = lb.length ∧
  ∀ (i j : Nat) (x y : α) (u v : Nat), (la ++ lb)[i]? = some x → (la ++ lb)[j]? = some y →
    (ia ++ ib)[i]? = some u → (ia ++ ib)[j]? = some v → (u = v ↔ x = y)

theorem idsExact_map {α : Type} [DecidableEq α] {la lb : List α} {ia ib : List Nat}
    (h : IdsExact la lb ia ib) :
    ∃ g : α → Nat, ia = la.map g ∧ ib = lb.map g ∧ ∀ x ∈ la ++ lb, ∀ y ∈ la ++ lb, g x = g y → x = y := by
  obtain ⟨hla, hlb, hex⟩ := h
  have hlen : (ia ++ ib).length = (la ++ lb).length := by simp [hla, hlb]
  let g : α → Nat := fun x => (ia ++ ib).getD ((la ++ lb).idxOf x) 0
  have hg : ∀ x ∈ la ++ lb, (la ++ lb)[(la ++ lb).idxOf x]? = some x ∧
      (ia ++ ib)[(la ++ lb).idxOf x]? = some (g x) := by
    intro x hx
    have hk := List.idxOf_lt_length_of_mem hx
    refine ⟨getElem?_idxOf _ x hx, ?_⟩
    have : (la ++ lb).idxOf x < (ia ++ ib).length := by omega
    simp [g, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
  have hA : ∀ (i : Nat) (x : α) (u : Nat), (la ++ lb)[i]? = some x → (ia ++ ib)[i]? = some u → g x = u := by
    intro i x u hx hu
    have hmem : x ∈ la ++ lb := List.mem_of_getElem? hx
    obtain ⟨h1, h2⟩ := hg x hmem
    exact ((hex _ _ _ _ _ _ h1 hx h2 hu).mpr rfl) ▸ rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · apply List.ext_getElem?
    intro i
    rw [List.getElem?_map]
    by_cases hi : i < la.length
    · have e1 : (la ++ lb)[i]? = la[i]? := List.getElem?_append_left hi
      have e2 : (ia ++ ib)[i]? = ia[i]? := List.getElem?_append_left (by omega)
      obtain ⟨x, hx⟩ : ∃ x, la[i]? = some x := ⟨la[i], List.getElem?_eq_getElem hi⟩
      obtain ⟨u, hu⟩ : ∃ u, ia[i]? = some u := ⟨ia[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      rw [hx, hu]
      simp [hA i x u (by rw [e1, hx]) (by rw [e2, hu])]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl
  · apply List.ext_getElem?
    intro i
    rw [List.getElem?_map]
    by_cases hi : i < lb.length
    · have e1 : (la ++ lb)[la.length + i]? = lb[i]? := by
        rw [List.getElem?_append_right (by omega)]; simp
      have e2 : (ia ++ ib)[la.length + i]? = ib[i]? := by
        rw [List.getElem?_append_right (by omega)]; simp [hla]
      obtain ⟨x, hx⟩ : ∃ x, lb[i]? = some x := ⟨lb[i], List.getElem?_eq_getElem hi⟩
      obtain ⟨u, hu⟩ : ∃ u, ib[i]? = some u := ⟨ib[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      rw [hx, hu]
      simp [hA (la.length + i) x u (by rw [e1, hx]) (by rw [e2, hu])]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl
  · intro x hx y hy e
    obtain ⟨h1, h2⟩ := hg x hx
    obtain ⟨h3, h4⟩ := hg y hy
    exact (hex _ _ _ _ _ _ h1 h3 h2 h4).mp e

end Myers
