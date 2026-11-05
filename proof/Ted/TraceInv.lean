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

end
end Ted
