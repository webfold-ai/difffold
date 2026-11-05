import Sol
/-! The invariant of the traceback: the pairs found so far, the subtrees still to be traced and the forest
being walked can be completed, in every way, to an optimal mapping of the two trees. -/
namespace Ted
section
variable {la lb : Nat → Nat} {ren : Nat → Nat → Nat}

theorem sol_perm {l x l' y : Nat} {M M' : List (Nat × Nat)} (hp : M.Perm M') (h : Sol la lb ren l x l' y M) :
    Sol la lb ren l x l' y M' := by
  obtain ⟨hv, hr, hc⟩ := h
  refine ⟨⟨hp.nodup_iff.mp hv.1, fun p hp' q hq => hv.2 p (hp.mem_iff.mpr hp') q (hp.mem_iff.mpr hq)⟩,
    fun p hp' => hr p (hp.mem_iff.mpr hp'), ?_⟩
  unfold Cost at hc ⊢
  have h1 := hp.length_eq
  have h2 : (M.map (fun p => ren p.1 p.2)).sum = (M'.map (fun p => ren p.1 p.2)).sum :=
    (hp.map _).sum_nat
  rw [← h1, ← h2]; exact hc

/-- The subtrees on the stack, each solved. -/
inductive SolsOf (la lb : Nat → Nat) (ren : Nat → Nat → Nat) : List (Nat × Nat) → List (Nat × Nat) → Prop
  | nil : SolsOf la lb ren [] []
  | snoc {S MS : List (Nat × Nat)} {x y : Nat} {M : List (Nat × Nat)} :
      SolsOf la lb ren S MS → Sol la lb ren (la x) x (lb y) y M →
      SolsOf la lb ren (S ++ [(x, y)]) (MS ++ M)

/-- Every way of solving the stack and the current forest completes `P` to a solution of the root task. -/
def TInv (la lb : Nat → Nat) (ren : Nat → Nat → Nat) (n m : Nat) (P : List (Nat × Nat))
    (S : List (Nat × Nat)) (l x l' y : Nat) : Prop :=
  ∀ MS Mc, SolsOf la lb ren S MS → Sol la lb ren l x l' y Mc → Sol la lb ren 1 n 1 m (P ++ MS ++ Mc)

theorem tinv_perm {n m : Nat} {P P' S : List (Nat × Nat)} {l x l' y : Nat} (hp : P.Perm P')
    (h : TInv la lb ren n m P S l x l' y) : TInv la lb ren n m P' S l x l' y := by
  intro MS Mc hS hc
  exact sol_perm ((hp.append_right MS).append_right Mc) (h MS Mc hS hc)

theorem perm_snoc_mid (P MS Mc : List (Nat × Nat)) (q : Nat × Nat) :
    (P ++ [q] ++ MS ++ Mc).Perm (P ++ MS ++ q :: Mc) := by
  rw [List.perm_iff_count]; intro a
  simp only [List.count_append, List.count_cons, List.count_nil]
  omega

theorem perm_swap_mid (P MS M Mc : List (Nat × Nat)) :
    (P ++ MS ++ (Mc ++ M)).Perm (P ++ (MS ++ M) ++ Mc) := by
  rw [List.perm_iff_count]; intro a
  simp only [List.count_append]
  omega

theorem tinv_del {n m : Nat} {P S : List (Nat × Nat)} {l x l' y : Nat} (h1 : ¬ (x < l ∨ x = 0))
    (hd : D la lb ren l x l' y = D la lb ren l (x - 1) l' y + 1)
    (h : TInv la lb ren n m P S l x l' y) : TInv la lb ren n m P S l (x - 1) l' y :=
  fun MS Mc hS hc => h MS Mc hS (sol_del h1 hd hc)

theorem tinv_ins {n m : Nat} {P S : List (Nat × Nat)} {l x l' y : Nat} (h2 : ¬ (y < l' ∨ y = 0))
    (hd : D la lb ren l x l' y = D la lb ren l x l' (y - 1) + 1)
    (h : TInv la lb ren n m P S l x l' y) : TInv la lb ren n m P S l x l' (y - 1) :=
  fun MS Mc hS hc => h MS Mc hS (sol_ins h2 hd hc)

theorem tinv_leaf {n m : Nat} {P S : List (Nat × Nat)} {l x l' y : Nat} (hA : WfL la) (hB : WfL lb)
    (hl : 1 ≤ l) (hl' : 1 ≤ l') (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0))
    (hlx : la x = l) (hly : lb y = l')
    (hd : D la lb ren l x l' y = D la lb ren l (x - 1) l' (y - 1) + ren x y)
    (h : TInv la lb ren n m P S l x l' y) : TInv la lb ren n m (P ++ [(x, y)]) S l (x - 1) l' (y - 1) := by
  intro MS Mc hS hc
  have := h MS ((x, y) :: Mc) hS (sol_leaf hA hB hl hl' h1 h2 hlx hly hd hc)
  refine sol_perm ?_ this
  exact (perm_snoc_mid P MS Mc (x, y)).symm

theorem solsOf_inv {S' MS : List (Nat × Nat)} (h : SolsOf la lb ren S' MS) :
    (S' = [] ∧ MS = []) ∨ ∃ S MS0 x y M, S' = S ++ [(x, y)] ∧ SolsOf la lb ren S MS0 ∧
      Sol la lb ren (la x) x (lb y) y M ∧ MS = MS0 ++ M := by
  cases h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | snoc h1 h2 => exact Or.inr ⟨_, _, _, _, _, rfl, h1, h2, rfl⟩

theorem solsOf_snoc_inv {S MS : List (Nat × Nat)} {x y : Nat}
    (h : SolsOf la lb ren (S ++ [(x, y)]) MS) :
    ∃ MS0 M, SolsOf la lb ren S MS0 ∧ Sol la lb ren (la x) x (lb y) y M ∧ MS = MS0 ++ M := by
  rcases solsOf_inv h with ⟨h0, _⟩ | ⟨S1, MS1, x1, y1, M1, e, h1, h2, h3⟩
  · simp at h0
  · obtain ⟨e1, e2⟩ := List.append_inj' e rfl
    simp only [List.cons.injEq, and_true] at e2
    obtain ⟨rfl, rfl⟩ := e2
    subst e1
    exact ⟨MS1, M1, h1, h2, h3⟩

theorem tinv_push {n m : Nat} {P S : List (Nat × Nat)} {l x l' y : Nat} (hA : WfL la) (hB : WfL lb)
    (hl : 1 ≤ l) (hl' : 1 ≤ l') (h1 : ¬ (x < l ∨ x = 0)) (h2 : ¬ (y < l' ∨ y = 0))
    (hcA : Closed la l x) (hcB : Closed lb l' y)
    (hd : D la lb ren l x l' y = D la lb ren l (la x - 1) l' (lb y - 1) + D la lb ren (la x) x (lb y) y)
    (h : TInv la lb ren n m P S l x l' y) :
    TInv la lb ren n m P (S ++ [(x, y)]) l (la x - 1) l' (lb y - 1) := by
  intro MS' Mc hS hc
  obtain ⟨MS, M, hS0, hM, rfl⟩ := solsOf_snoc_inv hS
  have := h MS (Mc ++ M) hS0 (sol_split hA hB hl hl' h1 h2 hcA hcB hd hc hM)
  exact sol_perm (perm_swap_mid P MS M Mc) this

/-- The state between two windows: only the stack remains. -/
def OInv (la lb : Nat → Nat) (ren : Nat → Nat → Nat) (n m : Nat) (P S : List (Nat × Nat)) : Prop :=
  ∀ MS, SolsOf la lb ren S MS → Sol la lb ren 1 n 1 m (P ++ MS)

theorem tinv_of_oinv {n m : Nat} {P S : List (Nat × Nat)} {l x l' y : Nat} (hx : x < l ∨ x = 0)
    (hy : y < l' ∨ y = 0) (hl : 1 ≤ l) (hl' : 1 ≤ l') (h : OInv la lb ren n m P S) :
    TInv la lb ren n m P S l x l' y := by
  intro MS Mc hS hc
  have hn : Mc = [] := by
    obtain ⟨_, hr, _⟩ := hc
    cases Mc with
    | nil => rfl
    | cons p r =>
      have := hr p (List.mem_cons_self ..)
      omega
  subst hn
  simpa using h MS hS

theorem oinv_of_tinv {n m : Nat} {P S : List (Nat × Nat)} {l x l' y : Nat} (hx : x < l ∨ x = 0)
    (hy : y < l' ∨ y = 0) (hl : 1 ≤ l) (hl' : 1 ≤ l') (h : TInv la lb ren n m P S l x l' y) :
    OInv la lb ren n m P S := by
  intro MS hS
  simpa using h MS [] hS (sol_nil hx hy hl hl')

theorem tinv_pop {n m : Nat} {P S : List (Nat × Nat)} {x y : Nat} (h : OInv la lb ren n m P (S ++ [(x, y)])) :
    TInv la lb ren n m P S (la x) x (lb y) y := by
  intro MS Mc hS hc
  have := h (MS ++ Mc) (SolsOf.snoc hS hc)
  simpa using this

theorem oinv_init {n m : Nat} (hln : la n = 1) (hlm : lb m = 1) : OInv la lb ren n m [] [(n, m)] := by
  intro MS hS
  have : ([(n, m)] : List (Nat × Nat)) = [] ++ [(n, m)] := rfl
  rw [this] at hS
  obtain ⟨MS0, M, h0, hM, rfl⟩ := solsOf_snoc_inv hS
  have h00 : MS0 = [] := by
    rcases solsOf_inv h0 with ⟨_, h⟩ | ⟨S1, _, x1, y1, _, e, _, _, _⟩
    · exact h
    · simp at e
  subst h00
  rw [hln, hlm] at hM
  simpa using hM

theorem oinv_final {n m : Nat} {P : List (Nat × Nat)} (h : OInv la lb ren n m P []) :
    Sol la lb ren 1 n 1 m P := by
  simpa using h [] SolsOf.nil

end
end Ted
