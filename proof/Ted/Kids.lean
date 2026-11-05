import Par
/-! Well formedness from the child lists.

A tree is given by the leftmost-leaf map `la` and the ascending child lists `kd`. The conditions below are what
`PostTree::from_kids` needs from its input: the children of `p` are smaller than `p`, ascending, they end with
`p - 1`, the subtrees of consecutive children tile (`la` of the next child is one past the previous child), `la p`
is the `la` of the first child (`p` itself for a leaf), and the last node is the root. From them the leftmost-leaf
map is well formed (`WfL`) and the child lists are exactly the parent relation `Par`. -/
namespace Ted

structure KidsOK (n : Nat) (la : Nat → Nat) (kd : Nat → List Nat) : Prop where
  sorted : ∀ p, 1 ≤ p → p ≤ n → (kd p).Pairwise (· < ·)
  lt : ∀ p, 1 ≤ p → p ≤ n → ∀ c ∈ kd p, 1 ≤ c ∧ c < p
  leaf : ∀ p, 1 ≤ p → p ≤ n → kd p = [] → la p = p
  first : ∀ p c cs, 1 ≤ p → p ≤ n → kd p = c :: cs → la p = la c
  last : ∀ p, 1 ≤ p → p ≤ n → kd p ≠ [] → p - 1 ∈ kd p
  adj : ∀ p, 1 ≤ p → p ≤ n → ∀ pre c c' post, kd p = pre ++ c :: c' :: post → la c' = c + 1
  bnd : ∀ u, 1 ≤ u → u ≤ n → 1 ≤ la u ∧ la u ≤ u
  big : ∀ u, n < u → la u = u
  root : la n = 1

theorem tile_cover (la : Nat → Nat) :
    ∀ (ks : List Nat) (lo hi : Nat),
    (∀ k cs, ks = k :: cs → la k = lo) →
    (∀ pre c c' post, ks = pre ++ c :: c' :: post → la c' = c + 1) →
    (ks ≠ [] → hi ∈ ks) → ks.Pairwise (· < ·) → (∀ k ∈ ks, k ≤ hi) →
    ∀ v, lo ≤ v → v ≤ hi → ks ≠ [] → ∃ k ∈ ks, la k ≤ v ∧ v ≤ k := by
  intro ks
  induction ks with
  | nil => intro _ _ _ _ _ _ _ _ _ _ h; exact absurd rfl h
  | cons k rest ih =>
    intro lo hi hf hadj hlast hs hle' v hlo hhi _
    have hlk : la k = lo := hf k rest rfl
    by_cases hv : v ≤ k
    · exact ⟨k, List.mem_cons_self .., by omega, hv⟩
    · -- the rest is nonempty, since `hi` is the last element
      have hrest : rest ≠ [] := by
        intro h0
        have := hlast (by simp)
        rw [h0] at this
        simp at this
        omega
      obtain ⟨k', rest', hk'⟩ := List.exists_cons_of_ne_nil hrest
      subst hk'
      have hla' : la k' = k + 1 := hadj [] k k' rest' rfl
      have hs' := (List.pairwise_cons.mp hs).2
      obtain ⟨k2, hk2, h1, h2⟩ := ih (k + 1) hi
        (fun k'' cs h => by
          have : k'' = k' := (List.cons.inj h).1.symm
          subst this; exact hla')
        (fun pre c c' post h => hadj (k :: pre) c c' post (by simp [h]))
        (fun _ => by
          have := hlast (by simp)
          rcases List.mem_cons.mp this with h | h
          · rw [h] at hhi; omega
          · exact h)
        hs' (fun x hx => hle' x (List.mem_cons_of_mem _ hx)) v (by omega) hhi (by simp)
      exact ⟨k2, List.mem_cons_of_mem _ hk2, h1, h2⟩

theorem mem_cases : ∀ (ks : List Nat) (k : Nat), k ∈ ks →
    (∃ cs, ks = k :: cs) ∨ ∃ pre c post, ks = pre ++ c :: k :: post := by
  intro ks
  induction ks with
  | nil => intro k h; simp at h
  | cons x rest ih =>
    intro k hk
    rcases List.mem_cons.mp hk with h | h
    · left; exact ⟨rest, by rw [h]⟩
    · rcases ih k h with ⟨cs, hcs⟩ | ⟨pre, c, post, hp⟩
      · right; exact ⟨[], x, cs, by rw [hcs]; rfl⟩
      · right; exact ⟨x :: pre, c, post, by rw [hp]; rfl⟩

theorem pred_ge {ks : List Nat} (hs : ks.Pairwise (· < ·)) {pre post : List Nat} {c'' k c : Nat}
    (h : ks = pre ++ c'' :: k :: post) (hc : c ∈ ks) (hck : c < k) : c ≤ c'' := by
  rw [h] at hs hc
  rw [List.pairwise_append] at hs
  rw [List.mem_append] at hc
  rcases hc with hc | hc
  · have := hs.2.2 c hc c'' (by simp); omega
  · rcases List.mem_cons.mp hc with e | hc
    · omega
    · rcases List.mem_cons.mp hc with e | hc
      · omega
      · have := (List.pairwise_cons.mp (List.pairwise_cons.mp hs.2.1).2).1 c hc
        omega

namespace KidsOK
variable {n : Nat} {la : Nat → Nat} {kd : Nat → List Nat}

theorem cover (h : KidsOK n la kd) {p : Nat} (hp : 1 ≤ p) (hpn : p ≤ n) (hne : kd p ≠ [])
    {v : Nat} (hv1 : la p ≤ v) (hv2 : v ≤ p - 1) : ∃ k ∈ kd p, la k ≤ v ∧ v ≤ k := by
  exact tile_cover la (kd p) (la p) (p - 1)
    (fun k cs hk => (h.first p k cs hp hpn hk).symm)
    (fun pre c c' post hh => h.adj p hp hpn pre c c' post hh)
    (fun _ => h.last p hp hpn hne) (h.sorted p hp hpn)
    (fun k hk => by have := (h.lt p hp hpn k hk).2; omega) v hv1 hv2 hne

theorem first_le (h : KidsOK n la kd) {u : Nat} (hu : 1 ≤ u) (hun : u ≤ n) {k : Nat} (hk : k ∈ kd u) :
    la u ≤ la k := by
  rcases mem_cases (kd u) k hk with ⟨cs, hcs⟩ | ⟨pre, c, post, hp⟩
  · exact Nat.le_of_eq (h.first u k cs hu hun hcs)
  · have hadj := h.adj u hu hun pre c k post hp
    have hne : kd u ≠ [] := by rw [hp]; simp
    obtain ⟨f, fs, hf⟩ := List.exists_cons_of_ne_nil hne
    have hla := h.first u f fs hu hun hf
    have hfn : f ∈ kd u := by rw [hf]; simp
    have hfb := h.lt u hu hun f hfn
    have hfn' : f ≤ n := by omega
    have hfle := (h.bnd f hfb.1 hfn').2
    have hcm : c ∈ kd u := by rw [hp]; simp
    have hfc : f ≤ c := by
      have hs := h.sorted u hu hun
      rw [hf] at hs hcm
      rcases List.mem_cons.mp hcm with e | e
      · omega
      · have := (List.pairwise_cons.mp hs).1 c e; omega
    omega

theorem nest (h : KidsOK n la kd) : ∀ u, u ≤ n → ∀ v, la u ≤ v → v ≤ u → la u ≤ la v := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro hun v h1 h2
    by_cases hvu : v = u
    · rw [hvu]; exact Nat.le_refl _
    · have hu1 : 1 ≤ u := by omega
      have hne : kd u ≠ [] := by
        intro h0
        have := h.leaf u hu1 hun h0
        omega
      obtain ⟨k, hk, hk1, hk2⟩ := h.cover hu1 hun hne h1 (by omega)
      have hkb := h.lt u hu1 hun k hk
      have := ih k hkb.2 (by omega) v hk1 hk2
      have := h.first_le hu1 hun hk
      omega

theorem wfl (h : KidsOK n la kd) : WfL la := by
  refine ⟨fun u hu => ?_, fun u v h1 h2 => ?_⟩
  · by_cases hun : u ≤ n
    · exact h.bnd u hu hun
    · rw [h.big u (by omega)]; omega
  · by_cases hun : u ≤ n
    · exact h.nest u hun v h1 h2
    · rw [h.big u (by omega)] at h1
      have : v = u := by omega
      subst this; exact Nat.le_refl _

theorem par_iff (h : KidsOK n la kd) {p : Nat} (hp : 1 ≤ p) (hpn : p ≤ n) (c : Nat) :
    c ∈ kd p ↔ 1 ≤ c ∧ Par la n c p := by
  constructor
  · intro hc
    have hcb := h.lt p hp hpn c hc
    have hne : kd p ≠ [] := by intro h0; rw [h0] at hc; simp at hc
    obtain ⟨f, fs, hf⟩ := List.exists_cons_of_ne_nil hne
    have hla := h.first p f fs hp hpn hf
    have hfn : f ∈ kd p := by rw [hf]; simp
    have hfb := h.lt p hp hpn f hfn
    have hfle := (h.bnd f hfb.1 (by omega)).2
    have hfc : f ≤ c := by
      have hs := h.sorted p hp hpn
      rw [hf] at hs hc
      rcases List.mem_cons.mp hc with e | e
      · omega
      · have := (List.pairwise_cons.mp hs).1 c e; omega
    refine ⟨hcb.1, ⟨hcb.2, by omega⟩, hpn, fun w hw => ?_⟩
    refine Classical.byContradiction fun hwp => ?_
    have hw1 : c < w := hw.1
    have hw2 : la w ≤ c := hw.2
    have hwn : w ≤ n := by omega
    obtain ⟨k, hk, hk1, hk2⟩ := h.cover hp hpn hne (v := w) (by omega) (by omega)
    have hkb := h.lt p hp hpn k hk
    rcases mem_cases (kd p) k hk with ⟨cs, hcs⟩ | ⟨pre, c'', post, hpp⟩
    · -- `k` is the first child, so `k <= c`, but `w <= k` and `c < w`
      have : f = k := by rw [hf] at hcs; exact (List.cons.inj hcs).1
      omega
    · have hadj := h.adj p hp hpn pre c'' k post hpp
      have hge := pred_ge (h.sorted p hp hpn) hpp hc (by omega)
      have := h.nest k (by omega) w hk1 hk2
      omega
  · rintro ⟨hc1, hlp, _, hmin⟩
    have hne : kd p ≠ [] := by
      intro h0
      have := h.leaf p hp hpn h0
      have := hlp.2; have := hlp.1
      omega
    obtain ⟨k, hk, hk1, hk2⟩ := h.cover hp hpn hne (v := c) hlp.2 (by have := hlp.1; omega)
    have hkb := h.lt p hp hpn k hk
    by_cases hkc : k = c
    · rw [← hkc]; exact hk
    · exfalso
      have := hmin k ⟨by omega, hk1⟩
      omega

end KidsOK
end Ted
