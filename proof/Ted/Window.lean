import DifffoldTed
import Basic
import Cell
import Truth
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! The invariants of the forest-distance table of one window of `fill_window`, as plain statements about the
true distance `Ted.D` and the stored values read through `rd`. -/

structure Ctx where
  la : Nat → Nat
  lb : Nat → Nat
  ren : Nat → Nat → Nat
  t : Nat
  li : Nat
  lj : Nat
  n : Nat
  m : Nat
  i0 : Nat
  j0 : Nat

theorem rd_set_eq (L : List Std.U32) (w t inf x y : Nat) (v : Std.U32) (hb : InBand t x y)
    (hlen : bandIdx w t x y < L.length) :
    rd (L.set (bandIdx w t x y) v) w t inf x y = v.val := by
  simp [rd, hb, getU_set_eq _ _ _ hlen]

theorem rd_set_ne (L : List Std.U32) (w t inf x y x' y' : Nat) (v : Std.U32) (hw : w = 2 * t + 1)
    (hb : InBand t x y) (hne : ¬ (x = x' ∧ y = y')) :
    rd (L.set (bandIdx w t x y) v) w t inf x' y' = rd L w t inf x' y' := by
  unfold rd
  by_cases hb' : InBand t x' y'
  · have : bandIdx w t x' y' ≠ bandIdx w t x y := fun e => hne (by
      have := bandIdx_inj w t x' y' x y hw hb' hb e; omega)
    simp [hb', getU_set_ne _ _ _ _ this]
  · simp [hb']

namespace Ctx
def inf (C : Ctx) : Nat := C.t + 1
def w (C : Ctx) : Nat := 2 * C.t + 1
def δ (C : Ctx) : Nat := adf C.li C.lj
def si (C : Ctx) : Nat := C.i0 - C.li + 1
def sj (C : Ctx) : Nat := C.j0 - C.lj + 1

/-- Shape facts of a window: well formed trees and the window of a node of each. -/
structure Good (C : Ctx) : Prop where
  wa : WfL C.la
  wb : WfL C.lb
  i0a : 1 ≤ C.i0
  i0b : C.i0 ≤ C.n
  j0a : 1 ≤ C.j0
  j0b : C.j0 ≤ C.m
  li_eq : C.li = C.la C.i0
  lj_eq : C.lj = C.lb C.j0

/-- A cell of the window table holds an ok value. -/
def OkF (C : Ctx) (fd : List Std.U32) (p q : Nat) : Prop :=
  FOK C.t C.δ (Dw C.la C.lb C.ren C.li C.lj p q) (rd fd C.w C.t C.inf p q)

/-- An entry of the subtree-distance table holds an ok value. -/
def OkT (C : Ctx) (td : List Std.U32) (x y : Nat) : Prop :=
  min (TD C.la C.lb C.ren x y) C.inf ≤ rd td C.w C.t C.inf x y ∧ rd td C.w C.t C.inf x y ≤ C.inf ∧
    (TD C.la C.lb C.ren x y + adf (C.la x) (C.lb y) ≤ C.t → rd td C.w C.t C.inf x y = TD C.la C.lb C.ren x y)

theorem rd_out (L : List Std.U32) (w t inf x y : Nat) (h : ¬ InBand t x y) : rd L w t inf x y = inf := by
  simp [rd, h]

theorem okF_out (C : Ctx) (fd : List Std.U32) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) (p q : Nat)
    (h : ¬ InBand C.t p q) : C.OkF fd p q := by
  unfold OkF
  rw [rd_out _ _ _ _ _ _ h]
  exact fok_out hli hlj (by unfold InBand at h; exact h)

/-- For subtree pairs, being out of the band leaves the stored `inf` ok. -/
theorem okT_out (C : Ctx) (td : List Std.U32) {x y : Nat} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hA : WfL C.la) (hB : WfL C.lb) (h : ¬ InBand C.t x y) : C.OkT td x y := by
  unfold OkT
  rw [rd_out _ _ _ _ _ _ h]
  have hs := D_size C.la C.lb C.ren _ (C.la x) x (C.lb y) y (by have := (hA.1 x hx).1; omega)
    (by have := (hB.1 y hy).1; omega) rfl
  have h1 := (hA.1 x hx); have h2 := (hB.1 y hy)
  unfold InBand at h
  unfold TD
  unfold adf
  refine ⟨by omega, by unfold inf; omega, ?_⟩
  intro hh
  split at hh <;> omega


def LeafPair (C : Ctx) (x y : Nat) : Prop := C.la x = C.li ∧ C.lb y = C.lj

/-- Pairs whose subtree-distance entry is final once the window cells before `(p, q)` are done. -/
def Done (C : Ctx) (p q x y : Nat) : Prop :=
  x ≤ C.i0 ∧ y ≤ C.j0 ∧ (¬ C.LeafPair x y ∨
    (C.LeafPair x y ∧ (x < C.li + p - 1 ∨ (x = C.li + p - 1 ∧ y < C.lj + q - 1))))

/-- The subtree-distance table: never below the capped truth, never above `inf`, exact for done pairs. -/
def TdInv (C : Ctx) (td : List Std.U32) (p q : Nat) : Prop :=
  ∀ x y, 1 ≤ x → x ≤ C.n → 1 ≤ y → y ≤ C.m →
    (min (TD C.la C.lb C.ren x y) C.inf ≤ rd td C.w C.t C.inf x y ∧ rd td C.w C.t C.inf x y ≤ C.inf) ∧
    (C.Done p q x y → TD C.la C.lb C.ren x y + adf (C.la x) (C.lb y) ≤ C.t →
      rd td C.w C.t C.inf x y = TD C.la C.lb C.ren x y)

/-- The window cells that are complete when row `p` is at column `q`. -/
def RowsInv (C : Ctx) (fd : List Std.U32) (p q : Nat) : Prop :=
  ∀ p' q', p' ≤ C.si → q' ≤ C.sj → (p' < p ∨ p' = 0 ∨ q' = 0 ∨ (p' = p ∧ q' < q)) → C.OkF fd p' q'

theorem closed_win (C : Ctx) (hG : C.Good) {x : Nat} (hx : x ≤ C.i0) : Closed C.la C.li x := by
  intro u hu hu'
  have := hG.wa.2 C.i0 u (by rw [← hG.li_eq]; exact hu) (by omega)
  rw [← hG.li_eq] at this; exact this

theorem closed_winB (C : Ctx) (hG : C.Good) {y : Nat} (hy : y ≤ C.j0) : Closed C.lb C.lj y := by
  intro u hu hu'
  have := hG.wb.2 C.j0 u (by rw [← hG.lj_eq]; exact hu) (by omega)
  rw [← hG.lj_eq] at this; exact this


theorem cellNew_fok (C : Ctx) (hG : C.Good) (fd td : List Std.U32) {p q : Nat} (hli : 1 ≤ C.li)
    (hlj : 1 ≤ C.lj) (hp : 1 ≤ p) (hq : 1 ≤ q) (hps : p ≤ C.si) (hqs : q ≤ C.sj)
    (hR : C.RowsInv fd p q) (hT : C.TdInv td p q) :
    FOK C.t C.δ (Dw C.la C.lb C.ren C.li C.lj p q)
      (cellNew fd td C.w C.t C.inf C.li C.lj p q (C.li + p - 1) (C.la (C.li + p - 1))
        (C.lb (C.lj + q - 1)) (C.ren (C.li + p - 1) (C.lj + q - 1))) := by
  have hlile : C.li ≤ C.i0 := by have := (hG.wa.1 C.i0 hG.i0a).2; rw [← hG.li_eq] at this; exact this
  have hljle : C.lj ≤ C.j0 := by have := (hG.wb.1 C.j0 hG.j0a).2; rw [← hG.lj_eq] at this; exact this
  have hps2 : p ≤ C.i0 - C.li + 1 := hps
  have hqs2 : q ≤ C.j0 - C.lj + 1 := hqs
  have hxi : C.li + p - 1 ≤ C.i0 := by have := hG.i0a; omega
  have hyj : C.lj + q - 1 ≤ C.j0 := by have := hG.j0a; omega
  have hcA := closed_win C hG hxi
  have hcB := closed_winB C hG hyj
  have hlx2 : C.la (C.li + p - 1) ≤ C.li + p - 1 := (hG.wa.1 _ (by omega)).2
  have hly2 : C.lb (C.lj + q - 1) ≤ C.lj + q - 1 := (hG.wb.1 _ (by omega)).2
  have hlx1 : C.li ≤ C.la (C.li + p - 1) := hcA _ (by omega) (Nat.le_refl _)
  have hly1 : C.lj ≤ C.lb (C.lj + q - 1) := hcB _ (by omega) (Nat.le_refl _)
  have hF1 := hR (p - 1) q (by omega) hqs (Or.inl (by omega))
  have hF2 := hR p (q - 1) hps (by omega) (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩)))
  unfold OkF at hF1 hF2
  unfold cellNew cellX
  by_cases hl : C.la (C.li + p - 1) = C.li ∧ C.lb (C.lj + q - 1) = C.lj
  · rw [if_pos hl]
    have hF3 := hR (p - 1) (q - 1) (by omega) (by omega) (Or.inl (by omega))
    unfold OkF at hF3
    exact cell_truth_leaf hG.wa hG.wb hli hlj hp hq hl.1 hl.2 hF1 hF2 hF3
  · rw [if_neg hl]
    have hF3 := hR (C.la (C.li + p - 1) - C.li) (C.lb (C.lj + q - 1) - C.lj) (by show _ ≤ C.i0 - C.li + 1; omega)
      (by show _ ≤ C.j0 - C.lj + 1; omega) (Or.inl (by omega))
    unfold OkF at hF3
    have hTx := hT (C.li + p - 1) (C.lj + q - 1) (by omega) (by have := hG.i0b; omega) (by omega)
      (by have := hG.j0b; omega)
    refine cell_truth_nonleaf hG.wa hG.wb hli hlj hp hq hcA hcB hl hF1 hF2 hF3 ⟨hTx.1.1, hTx.1.2, ?_⟩
    intro hb
    refine hTx.2 ⟨hxi, hyj, Or.inl hl⟩ hb


/-- A pair whose subtree distance fits the remaining budget lies in the band `|x - y| <= t`. -/
theorem band_of_budget (C : Ctx) (hA : WfL C.la) (hB : WfL C.lb) {x y : Nat} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : TD C.la C.lb C.ren x y + adf (C.la x) (C.lb y) ≤ C.t) : InBand C.t x y := by
  have hs := D_size C.la C.lb C.ren _ (C.la x) x (C.lb y) y (by have := (hA.1 x hx).1; omega)
    (by have := (hB.1 y hy).1; omega) rfl
  have h1 := (hA.1 x hx); have h2 := (hB.1 y hy)
  unfold TD at h
  unfold adf at h
  unfold InBand
  split at h <;> omega

def FdB (L : List Std.U32) (inf : Nat) : Prop := ∀ k < L.length, (L[k]!).val ≤ inf

theorem FdB_set {L : List Std.U32} {inf : Nat} (h : FdB L inf) (i : Nat) (v : Std.U32) (hv : v.val ≤ inf) :
    FdB (L.set i v) inf := by
  intro k hk
  rw [List.length_set] at hk
  by_cases e : k = i
  · subst e; rw [getU_set_eq _ _ _ hk]; exact hv
  · rw [getU_set_ne _ _ _ _ e]; exact h k hk

/-- The row minimum covers the cells of the row computed so far. -/
def RowMin (C : Ctx) (fd : List Std.U32) (p q qlo rm : Nat) : Prop :=
  rm ≤ C.inf ∧ ∀ q', q' ≤ C.sj → (q' = 0 ∨ (qlo ≤ q' ∧ q' < q)) → InBand C.t p q' →
    rm ≤ rd fd C.w C.t C.inf p q'


/-- The values a leaf pair of the window hold, as the subtree distance and as the window cell agree. -/
theorem TD_eq_Dw (C : Ctx) {p q : Nat} (hp : 1 ≤ p) (hq : 1 ≤ q) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj)
    (hlx : C.la (C.li + p - 1) = C.li) (hly : C.lb (C.lj + q - 1) = C.lj) :
    TD C.la C.lb C.ren (C.li + p - 1) (C.lj + q - 1) = Dw C.la C.lb C.ren C.li C.lj p q := by
  unfold TD Dw; rw [hlx, hly]

theorem done_succ (C : Ctx) {p q x y : Nat} (hq : 1 ≤ q) (h : C.Done p (q + 1) x y) :
    C.Done p q x y ∨ (x = C.li + p - 1 ∧ y = C.lj + q - 1 ∧ C.LeafPair x y) := by
  unfold Done at *
  obtain ⟨h1, h2, h3⟩ := h
  rcases h3 with h3 | ⟨h3, h4 | ⟨h4, h5⟩⟩
  · exact Or.inl ⟨h1, h2, Or.inl h3⟩
  · exact Or.inl ⟨h1, h2, Or.inr ⟨h3, Or.inl h4⟩⟩
  · by_cases e : y = C.lj + q - 1
    · exact Or.inr ⟨h4, e, h3⟩
    · exact Or.inl ⟨h1, h2, Or.inr ⟨h3, Or.inr ⟨h4, by omega⟩⟩⟩

theorem inner_step (C : Ctx) (hG : C.Good) (hw : C.w = 2 * C.t + 1) (fd td fd' td' : List Std.U32)
    (v : Std.U32) {p q qlo rm : Nat} (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hps : p ≤ C.si) (hqs : q ≤ C.sj) (hband : InBand C.t p q)
    (hR : C.RowsInv fd p q) (hT : C.TdInv td p q) (hFB : FdB fd C.inf) (hTB : FdB td C.inf)
    (hM : C.RowMin fd p q qlo rm)
    (hv : v.val = cellNew fd td C.w C.t C.inf C.li C.lj p q (C.li + p - 1) (C.la (C.li + p - 1))
        (C.lb (C.lj + q - 1)) (C.ren (C.li + p - 1) (C.lj + q - 1)))
    (hfd' : fd' = fd.set (bandIdx C.w C.t p q) v) (hidx : bandIdx C.w C.t p q < fd.length)
    (htd1 : (C.LeafPair (C.li + p - 1) (C.lj + q - 1) ∧ InBand C.t (C.li + p - 1) (C.lj + q - 1)) →
      td' = td.set (bandIdx C.w C.t (C.li + p - 1) (C.lj + q - 1)) v ∧
        bandIdx C.w C.t (C.li + p - 1) (C.lj + q - 1) < td.length)
    (htd2 : ¬ (C.LeafPair (C.li + p - 1) (C.lj + q - 1) ∧ InBand C.t (C.li + p - 1) (C.lj + q - 1)) →
      td' = td) :
    C.RowsInv fd' p (q + 1) ∧ C.TdInv td' p (q + 1) ∧ FdB fd' C.inf ∧ FdB td' C.inf ∧
      C.RowMin fd' p (q + 1) qlo (min rm v.val) := by
  have hfok := cellNew_fok C hG fd td hli hlj hp hq hps hqs hR hT
  rw [← hv] at hfok
  have hvle : v.val ≤ C.inf := by have := hfok.2.1; unfold Ctx.inf; exact this
  have hlen' : fd'.length = fd.length := by rw [hfd']; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p' q' hp' hq' hc
    by_cases e : p' = p ∧ q' = q
    · obtain ⟨rfl, rfl⟩ := e
      unfold Ctx.OkF
      rw [hfd', rd_set_eq _ _ _ _ _ _ _ hband hidx]
      exact hfok
    · have := rd_set_ne fd C.w C.t C.inf p q p' q' v hw hband (fun h => e ⟨h.1.symm, h.2.symm⟩)
      unfold Ctx.OkF
      rw [hfd', this]
      apply hR p' q' hp' hq'
      rcases hc with h | h | h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, by
          by_cases e2 : q' = q
          · exact absurd ⟨h1, e2⟩ e
          · omega⟩))
  · intro x' y' hx1 hx2 hy1 hy2
    have hxi : C.li + p - 1 ≤ C.i0 := by
      have hlile : C.li ≤ C.i0 := by have := (hG.wa.1 C.i0 hG.i0a).2; rw [← hG.li_eq] at this; exact this
      have hps2 : p ≤ C.i0 - C.li + 1 := hps
      omega
    have hyj : C.lj + q - 1 ≤ C.j0 := by
      have hljle : C.lj ≤ C.j0 := by have := (hG.wb.1 C.j0 hG.j0a).2; rw [← hG.lj_eq] at this; exact this
      have hqs2 : q ≤ C.j0 - C.lj + 1 := hqs
      omega
    have hold := hT x' y' hx1 hx2 hy1 hy2
    by_cases hc : C.LeafPair (C.li + p - 1) (C.lj + q - 1) ∧ InBand C.t (C.li + p - 1) (C.lj + q - 1)
    · obtain ⟨hteq, hidT⟩ := htd1 hc
      by_cases e : x' = C.li + p - 1 ∧ y' = C.lj + q - 1
      · obtain ⟨rfl, rfl⟩ := e
        have hrd : rd td' C.w C.t C.inf (C.li + p - 1) (C.lj + q - 1) = v.val := by
          rw [hteq, rd_set_eq _ _ _ _ _ _ _ hc.2 hidT]
        have htd := TD_eq_Dw C hp hq hli hlj hc.1.1 hc.1.2
        rw [hrd, htd]
        refine ⟨⟨hfok.1, by unfold Ctx.inf; exact hfok.2.1⟩, ?_⟩
        intro _ hb
        have e1 : adf (C.la (C.li + p - 1)) (C.lb (C.lj + q - 1)) = C.δ := by
          unfold Ctx.δ; rw [hc.1.1, hc.1.2]
        rw [e1] at hb
        exact hfok.2.2 hb
      · have hne := rd_set_ne td C.w C.t C.inf (C.li + p - 1) (C.lj + q - 1) x' y' v hw hc.2
          (fun h => e ⟨h.1.symm, h.2.symm⟩)
        rw [hteq, hne]
        refine ⟨hold.1, ?_⟩
        intro hd hb
        rcases done_succ C hq hd with hd' | ⟨h1, h2, h3⟩
        · exact hold.2 hd' hb
        · exact absurd ⟨h1, h2⟩ e
    · rw [htd2 hc]
      refine ⟨hold.1, ?_⟩
      intro hd hb
      rcases done_succ C hq hd with hd' | ⟨h1, h2, h3⟩
      · exact hold.2 hd' hb
      · subst h1; subst h2
        exact absurd (band_of_budget C hG.wa hG.wb (by omega) (by omega) hb) (fun hb' => hc ⟨h3, hb'⟩)
  · rw [hfd']; exact FdB_set hFB _ _ hvle
  · by_cases hc : C.LeafPair (C.li + p - 1) (C.lj + q - 1) ∧ InBand C.t (C.li + p - 1) (C.lj + q - 1)
    · rw [(htd1 hc).1]; exact FdB_set hTB _ _ hvle
    · rw [htd2 hc]; exact hTB
  · refine ⟨by omega, ?_⟩
    intro q' hq' hc hb
    by_cases e : q' = q
    · subst e
      rw [hfd', rd_set_eq _ _ _ _ _ _ _ hband hidx]
      omega
    · have := rd_set_ne fd C.w C.t C.inf p q p q' v hw hband (fun h => e h.2.symm)
      rw [hfd', this]
      have := hM.2 q' hq' (by
        rcases hc with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by omega⟩) hb
      omega

end Ctx


end difffold_lines_extract
