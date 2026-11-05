import Pre
/-! The distance does not change when both trees are mirrored.

The mirror image of a tree sends node `x` to `pi x = n + 1 - pre x`: the postorder of the mirror is the reverse
of the preorder of the original. A tree edit mapping is exactly a one to one map that preserves the
preorder and the descendant relation, so it is also a mapping of the mirrors. -/
namespace Ted

def Rng (n m : Nat) (M : List (Nat × Nat)) : Prop :=
  ∀ p ∈ M, 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m

def ValidQ (la lb : Nat → Nat) (n m : Nat) (M : List (Nat × Nat)) : Prop :=
  M.Nodup ∧ ∀ p ∈ M, ∀ q ∈ M, (p.1 = q.1 ↔ p.2 = q.2) ∧
    (pre la n p.1 < pre la n q.1 ↔ pre lb m p.2 < pre lb m q.2) ∧ (Anc la p.1 q.1 ↔ Anc lb p.2 q.2)

section
variable {la lb : Nat → Nat} {n m : Nat}

theorem pre_iff_of_lt (hA : WfL la) (hB : WfL lb) {u v u2 v2 : Nat} (hu : 1 ≤ u) (hun : u ≤ n) (hvn : v ≤ n)
    (hu2 : 1 ≤ u2) (hv2n : v2 ≤ m) (hlt : u < v) (hlt2 : u2 < v2)
    (hanc : Anc la u v ↔ Anc lb u2 v2) :
    (pre la n u < pre la n v ↔ pre lb m u2 < pre lb m v2) := by
  by_cases ha : la v ≤ u
  · have h1 := P_anc hA hu hlt hvn ha
    have hb := hanc.mp ⟨hlt, ha⟩
    have h2 := P_anc hB hu2 hlt2 hv2n hb.2
    constructor <;> intro h <;> omega
  · have h1 := P_un hA hu hlt hvn (by omega)
    have h1' := pre_le_Qp hA hu (n := n)
    have hb : ¬ lb v2 ≤ u2 := fun h => ha (hanc.mpr ⟨hlt2, h⟩).2
    have h2 := P_un hB hu2 hlt2 hv2n (by omega)
    have h2' := pre_le_Qp hB hu2 (n := m)
    constructor <;> intro h <;> omega

theorem valid_to_validQ (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M)
    (hv : Valid la lb M) : ValidQ la lb n m M := by
  refine ⟨hv.1, fun p hp q hq => ?_⟩
  obtain ⟨e, o, a⟩ := hv.2 p hp q hq
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hr p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hr q hq
  refine ⟨e, ?_, a⟩
  rcases Nat.lt_trichotomy p.1 q.1 with h | h | h
  · exact pre_iff_of_lt hA hB hp1 hp2 hq2 hp3 hq4 h (o.mp h) a
  · have h2 := e.mp h
    rw [h, h2]; simp
  · obtain ⟨e', o', a'⟩ := hv.2 q hq p hp
    have := pre_iff_of_lt hA hB hq1 hq2 hp2 hq3 hp4 h (o'.mp h) a'
    have i1 : pre la n p.1 ≠ pre la n q.1 := fun hh => by
      have := pre_inj hA hp1 hp2 hq1 hq2 hh; omega
    have i2 : pre lb m p.2 ≠ pre lb m q.2 := fun hh => by
      have := pre_inj hB hp3 hp4 hq3 hq4 hh
      have := e.mpr this; omega
    omega

theorem order_of_validQ (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M)
    (hq : ValidQ la lb n m M) : ∀ p ∈ M, ∀ q ∈ M, p.1 < q.1 → p.2 < q.2 := by
  intro p hp q hqq hlt
  obtain ⟨e, o, a⟩ := hq.2 p hp q hqq
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hr p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hr q hqq
  by_cases ha : la q.1 ≤ p.1
  · exact (a.mp ⟨hlt, ha⟩).1
  · have h1 := P_un hA hp1 hlt hq2 (by omega)
    have h1' := pre_le_Qp hA hp1 (n := n)
    have h2 : pre lb m p.2 < pre lb m q.2 := o.mp (by omega)
    rcases Nat.lt_trichotomy p.2 q.2 with h | h | h
    · exact h
    · have := e.mpr h; omega
    · by_cases hb : lb p.2 ≤ q.2
      · have := ((hq.2 q hqq p hp).2.2).mpr ⟨h, hb⟩
        have := this.1; omega
      · have := P_un hB hq3 h hp4 (by omega)
        have := pre_le_Qp hB hq3 (n := m); omega

theorem validQ_to_valid (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M)
    (hq : ValidQ la lb n m M) : Valid la lb M := by
  refine ⟨hq.1, fun p hp q hqq => ?_⟩
  obtain ⟨e, o, a⟩ := hq.2 p hp q hqq
  refine ⟨e, ⟨order_of_validQ hA hB hr hq p hp q hqq, fun h => ?_⟩, a⟩
  rcases Nat.lt_trichotomy p.1 q.1 with h' | h' | h'
  · exact h'
  · have := e.mpr (by omega); omega
  · have := order_of_validQ hA hB hr hq q hqq p hp h'; omega

theorem valid_iff_validQ (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M) :
    Valid la lb M ↔ ValidQ la lb n m M :=
  ⟨valid_to_validQ hA hB hr, validQ_to_valid hA hB hr⟩

theorem nodup_map_inj {α β : Type} (f : α → β) : ∀ (l : List α), l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => by simp
  | p :: M, hnd, hinj => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, nodup_map_inj f M hnd'.2 (fun a ha b hb e => hinj a (by simp [ha]) b (by simp [hb]) e)⟩
    rintro ⟨q, hq, e⟩
    have := hinj q (by simp [hq]) p (by simp) e
    exact hnd'.1 (this ▸ hq)

/-- The postorder index of the mirror image of node `x`. -/
def pim (la : Nat → Nat) (n x : Nat) : Nat := n + 1 - pre la n x

theorem pim_mem (hA : WfL la) {x : Nat} (hx : 1 ≤ x) (hxn : x ≤ n) : 1 ≤ pim la n x ∧ pim la n x ≤ n := by
  have := pre_pos hA hx (n := n); have := pre_le_n hA hx hxn; unfold pim; omega

theorem pim_inj (hA : WfL la) {x y : Nat} (hx : 1 ≤ x) (hxn : x ≤ n) (hy : 1 ≤ y) (hyn : y ≤ n)
    (h : pim la n x = pim la n y) : x = y := by
  have := pre_le_n hA hx hxn; have := pre_le_n hA hy hyn
  unfold pim at h
  exact pre_inj hA hx hxn hy hyn (by omega)

theorem pim_surj (hA : WfL la) {y : Nat} (hy : 1 ≤ y) (hyn : y ≤ n) : ∃ x, 1 ≤ x ∧ x ≤ n ∧ pim la n x = y := by
  refine Classical.byContradiction fun hcon => ?_
  have hnc : ∀ x, 1 ≤ x → x ≤ n → pim la n x ≠ y := fun x h1 h2 h3 => hcon ⟨x, h1, h2, h3⟩
  let L := (List.range' 1 n).map (pim la n)
  have hL1 : L.Nodup := by
    apply nodup_map_inj _ _ List.nodup_range'
    intro a ha b hb e
    rw [List.mem_range'] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    exact pim_inj hA (by omega) (by omega) (by omega) (by omega) e
  have hL2 : y ∉ L := by
    intro h
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
    rw [List.mem_range'] at hx
    exact hnc x (by omega) (by omega) hxe
  have hnd : (y :: L).Nodup := List.nodup_cons.mpr ⟨hL2, hL1⟩
  have hsub : (y :: L) ⊆ List.range' 1 n := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · rw [List.mem_range']; exact ⟨z - 1, by omega, by omega⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      rw [List.mem_range'] at hx
      have := pim_mem hA (n := n) (x := x) (by omega) (by omega)
      rw [List.mem_range']; exact ⟨pim la n x - 1, by omega, by omega⟩
  have := nodup_length_le _ _ hnd hsub
  simp [L] at this
  omega

theorem anc_mirror (hA : WfL la) {la' : Nat → Nat}
    (hla' : ∀ x, 1 ≤ x → x ≤ n → la' (pim la n x) = n + 1 - Qp la n x)
    {u v : Nat} (hu : 1 ≤ u) (hun : u ≤ n) (hv : 1 ≤ v) (hvn : v ≤ n) :
    Anc la' (pim la n u) (pim la n v) ↔ Anc la u v := by
  rw [anc_iff_pre hA hu hun hv hvn]
  unfold Anc
  rw [hla' v hv hvn]
  have := pre_le_n hA hu hun; have := pre_le_n hA hv hvn
  have := Qp_le (la := la) hvn
  have := pre_pos hA hu (n := n); have := pre_pos hA hv (n := n)
  unfold pim; omega

theorem wfl_mirror (hA : WfL la) {la' : Nat → Nat}
    (hla' : ∀ x, 1 ≤ x → x ≤ n → la' (pim la n x) = n + 1 - Qp la n x)
    (hbig : ∀ u, n < u → la' u = u) : WfL la' := by
  have hle : ∀ x, 1 ≤ x → x ≤ n → Qp la n x ≤ n := fun x _ h => Qp_le h
  have hq1 : ∀ x, 1 ≤ x → pre la n x ≤ Qp la n x := fun x h => pre_le_Qp hA h
  refine ⟨fun u hu => ?_, fun u v h1 h2 => ?_⟩
  · by_cases hun : u ≤ n
    · obtain ⟨x, hx1, hx2, hx3⟩ := pim_surj hA hu hun
      subst hx3
      rw [hla' x hx1 hx2]
      have := hle x hx1 hx2; have := hq1 x hx1
      have := pre_pos hA hx1 (n := n)
      unfold pim; omega
    · rw [hbig u (by omega)]; omega
  · by_cases hu0 : u = v
    · subst hu0; exact Nat.le_refl _
    · have hvu : v < u := by omega
      have hu1 : 1 ≤ u := by omega
      by_cases hun : u ≤ n
      · obtain ⟨x, hx1, hx2, hx3⟩ := pim_surj hA hu1 hun
        have hv1 : 1 ≤ v := by
          subst hx3; rw [hla' x hx1 hx2] at h1
          have := hle x hx1 hx2; omega
        obtain ⟨y, hy1, hy2, hy3⟩ := pim_surj hA (n := n) (y := v) hv1 (by omega)
        subst hx3; subst hy3
        rw [hla' x hx1 hx2] at h1 ⊢
        rw [hla' y hy1 hy2]
        have hy_le := pre_le_n hA hy1 hy2
        have hx_le := pre_le_n hA hx1 hx2
        have hanc : Anc la y x := by
          rw [anc_iff_pre hA hy1 hy2 hx1 hx2]
          unfold pim at h1 hvu h2
          have := pre_pos hA hx1 (n := n); have := pre_pos hA hy1 (n := n)
          omega
        have := P_anc hA hy1 hanc.1 hx2 hanc.2
        omega
      · rw [hbig u (by omega)] at h1
        omega

def mpair (la lb : Nat → Nat) (n m : Nat) (p : Nat × Nat) : Nat × Nat := (pim la n p.1, pim lb m p.2)

theorem rng_mp (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M) :
    Rng n m (M.map (mpair la lb n m)) := by
  intro p' hp'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
  obtain ⟨h1, h2, h3, h4⟩ := hr p hp
  have := pim_mem hA (n := n) h1 h2
  have := pim_mem hB (n := m) h3 h4
  simp only [mpair]; omega

theorem mp_inj (hA : WfL la) (hB : WfL lb) {M : List (Nat × Nat)} (hr : Rng n m M) :
    ∀ a ∈ M, ∀ b ∈ M, mpair la lb n m a = mpair la lb n m b → a = b := by
  intro a ha b hb e
  obtain ⟨a1, a2, a3, a4⟩ := hr a ha
  obtain ⟨b1, b2, b3, b4⟩ := hr b hb
  simp only [mpair, Prod.mk.injEq] at e
  exact Prod.ext (pim_inj hA a1 a2 b1 b2 e.1) (pim_inj hB a3 a4 b3 b4 e.2)

theorem pim_eq_iff (hA : WfL la) {x y : Nat} (hx : 1 ≤ x) (hxn : x ≤ n) (hy : 1 ≤ y) (hyn : y ≤ n) :
    pim la n x = pim la n y ↔ x = y :=
  ⟨pim_inj hA hx hxn hy hyn, fun h => by rw [h]⟩

theorem pim_lt_iff (hA : WfL la) {x y : Nat} (hxn : x ≤ n) (hyn : y ≤ n) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    pim la n x < pim la n y ↔ pre la n y < pre la n x := by
  have := pre_le_n hA hx hxn; have := pre_le_n hA hy hyn
  unfold pim; omega

theorem valid_mp_iff (hA : WfL la) (hB : WfL lb) {la' lb' : Nat → Nat}
    (hla' : ∀ x, 1 ≤ x → x ≤ n → la' (pim la n x) = n + 1 - Qp la n x)
    (hlb' : ∀ y, 1 ≤ y → y ≤ m → lb' (pim lb m y) = m + 1 - Qp lb m y)
    {M : List (Nat × Nat)} (hr : Rng n m M) :
    Valid la' lb' (M.map (mpair la lb n m)) ↔ ValidQ la lb n m M := by
  have hnd : (M.map (mpair la lb n m)).Nodup ↔ M.Nodup :=
    ⟨fun h => (List.pairwise_map.mp h).imp (fun h e => h (congrArg _ e)), fun h => nodup_map_inj _ _ h (mp_inj hA hB hr)⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hnd.mp h1, fun p hp q hq => ?_⟩
    obtain ⟨e, o, a⟩ := h2 _ (List.mem_map_of_mem hp) _ (List.mem_map_of_mem hq)
    obtain ⟨_, o', _⟩ := h2 _ (List.mem_map_of_mem hq) _ (List.mem_map_of_mem hp)
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hr p hp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hr q hq
    simp only [mpair] at e o a o'
    rw [pim_eq_iff hA hp1 hp2 hq1 hq2, pim_eq_iff hB hp3 hp4 hq3 hq4] at e
    rw [pim_lt_iff hA hq2 hp2 hq1 hp1, pim_lt_iff hB hq4 hp4 hq3 hp3] at o'
    rw [anc_mirror hA hla' hp1 hp2 hq1 hq2, anc_mirror hB hlb' hp3 hp4 hq3 hq4] at a
    exact ⟨e, o', a⟩
  · intro hq
    refine ⟨hnd.mpr hq.1, fun p' hp' q' hq' => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
    obtain ⟨q, hqq, rfl⟩ := List.mem_map.mp hq'
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hr p hp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hr q hqq
    obtain ⟨e, o, a⟩ := hq.2 p hp q hqq
    obtain ⟨_, o', _⟩ := hq.2 q hqq p hp
    simp only [mpair]
    rw [pim_eq_iff hA hp1 hp2 hq1 hq2, pim_eq_iff hB hp3 hp4 hq3 hq4,
      pim_lt_iff hA hp2 hq2 hp1 hq1, pim_lt_iff hB hp4 hq4 hp3 hq3,
      anc_mirror hA hla' hp1 hp2 hq1 hq2, anc_mirror hB hlb' hp3 hp4 hq3 hq4]
    exact ⟨e, o', a⟩

theorem cost_mp {ren ren' : Nat → Nat → Nat}
    (hren : ∀ x y, 1 ≤ x → x ≤ n → 1 ≤ y → y ≤ m → ren' (pim la n x) (pim lb m y) = ren x y)
    {M : List (Nat × Nat)} (hr : Rng n m M) :
    Cost ren' 1 n 1 m (M.map (mpair la lb n m)) = Cost ren 1 n 1 m M := by
  have h : (M.map (mpair la lb n m)).map (fun p => ren' p.1 p.2) = M.map (fun p => ren p.1 p.2) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hr p hp
    simp only [Function.comp, mpair]
    exact hren _ _ h1 h2 h3 h4
  unfold Cost
  rw [List.length_map, h]

theorem exists_preimage (hA : WfL la) (hB : WfL lb) {M' : List (Nat × Nat)} (hr : Rng n m M') :
    ∃ M, Rng n m M ∧ M.map (mpair la lb n m) = M' := by
  induction M' with
  | nil => exact ⟨[], fun _ h => by simp at h, rfl⟩
  | cons p' rest ih =>
    have hr' : Rng n m rest := fun q hq => hr q (List.mem_cons_of_mem _ hq)
    obtain ⟨M, hM, hMe⟩ := ih hr'
    obtain ⟨h1, h2, h3, h4⟩ := hr p' (List.mem_cons_self ..)
    obtain ⟨x, hx1, hx2, hx3⟩ := pim_surj hA (n := n) h1 h2
    obtain ⟨y, hy1, hy2, hy3⟩ := pim_surj hB (n := m) h3 h4
    refine ⟨(x, y) :: M, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hx1, hx2, hy1, hy2⟩
      · exact hM q hq
    · simp only [List.map_cons, hMe, mpair, hx3, hy3]

/-- The distance of two trees equals the distance of their mirror images. -/
theorem D_mirror (hA : WfL la) (hB : WfL lb) {la' lb' : Nat → Nat} {ren ren' : Nat → Nat → Nat}
    (hA' : WfL la') (hB' : WfL lb')
    (hla' : ∀ x, 1 ≤ x → x ≤ n → la' (pim la n x) = n + 1 - Qp la n x)
    (hlb' : ∀ y, 1 ≤ y → y ≤ m → lb' (pim lb m y) = m + 1 - Qp lb m y)
    (hren : ∀ x y, 1 ≤ x → x ≤ n → 1 ≤ y → y ≤ m → ren' (pim la n x) (pim lb m y) = ren x y) :
    D la lb ren 1 n 1 m = D la' lb' ren' 1 n 1 m := by
  have hcA : Closed la 1 n := fun u hu _ => (hA.1 u hu).1
  have hcB : Closed lb 1 m := fun u hu _ => (hB.1 u hu).1
  have hcA' : Closed la' 1 n := fun u hu _ => (hA'.1 u hu).1
  have hcB' : Closed lb' 1 m := fun u hu _ => (hB'.1 u hu).1
  have hrng : ∀ M, InRange 1 n 1 m M → Rng n m M := fun M h p hp => by
    have := h p hp; omega
  have hrng' : ∀ M, Rng n m M → InRange 1 n 1 m M := fun M h p hp => by
    have := h p hp; omega
  symm
  apply Nat.le_antisymm
  · obtain ⟨M, hv, hr, hc⟩ := exists_map (ren := ren) hA hB _ 1 n 1 m (Nat.le_refl _) (Nat.le_refl _) hcA hcB rfl
    have hR := hrng M hr
    have hv' : Valid la' lb' (M.map (mpair la lb n m)) :=
      (valid_mp_iff hA hB hla' hlb' hR).mpr ((valid_iff_validQ hA hB hR).mp hv)
    have := D_le_cost (ren := ren') hA' hB' _ 1 n 1 m _ (Nat.le_refl _) (Nat.le_refl _) hcA' hcB' rfl hv'
      (hrng' _ (rng_mp hA hB hR))
    rw [cost_mp hren hR, hc] at this
    exact this
  · obtain ⟨M', hv', hr', hc'⟩ := exists_map (ren := ren') hA' hB' _ 1 n 1 m (Nat.le_refl _) (Nat.le_refl _) hcA' hcB' rfl
    have hR' := hrng M' hr'
    obtain ⟨M, hM, rfl⟩ := exists_preimage hA hB hR'
    have hv : Valid la lb M :=
      (valid_iff_validQ hA hB hM).mpr ((valid_mp_iff hA hB hla' hlb' hM).mp hv')
    have := D_le_cost (ren := ren) hA hB _ 1 n 1 m _ (Nat.le_refl _) (Nat.le_refl _) hcA hcB rfl hv (hrng' _ hM)
    rw [← cost_mp hren hM, hc'] at this
    exact this

end
end Ted
