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
  have hcA := Ctx.closed_win C hG hxi
  have hcB := Ctx.closed_winB C hG hyj
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

/-- Entries of the subtree-distance table that are not leaf pairs of this window are never touched. -/
def Frame (C : Ctx) (td0 td : List Std.U32) : Prop :=
  ∀ x y, ¬ (C.LeafPair x y ∧ x ≤ C.i0 ∧ y ≤ C.j0) → rd td C.w C.t C.inf x y = rd td0 C.w C.t C.inf x y

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
    (hM : C.RowMin fd p q qlo rm) (td0 : List Std.U32) (hFr : C.Frame td0 td)
    (hv : v.val = cellNew fd td C.w C.t C.inf C.li C.lj p q (C.li + p - 1) (C.la (C.li + p - 1))
        (C.lb (C.lj + q - 1)) (C.ren (C.li + p - 1) (C.lj + q - 1)))
    (hfd' : fd' = fd.set (bandIdx C.w C.t p q) v) (hidx : bandIdx C.w C.t p q < fd.length)
    (htd1 : (C.LeafPair (C.li + p - 1) (C.lj + q - 1) ∧ InBand C.t (C.li + p - 1) (C.lj + q - 1)) →
      td' = td.set (bandIdx C.w C.t (C.li + p - 1) (C.lj + q - 1)) v ∧
        bandIdx C.w C.t (C.li + p - 1) (C.lj + q - 1) < td.length)
    (htd2 : ¬ (C.LeafPair (C.li + p - 1) (C.lj + q - 1) ∧ InBand C.t (C.li + p - 1) (C.lj + q - 1)) →
      td' = td) :
    C.RowsInv fd' p (q + 1) ∧ C.TdInv td' p (q + 1) ∧ FdB fd' C.inf ∧ FdB td' C.inf ∧
      C.RowMin fd' p (q + 1) qlo (min rm v.val) ∧ C.Frame td0 td' := by
  have hfok := cellNew_fok C hG fd td hli hlj hp hq hps hqs hR hT
  rw [← hv] at hfok
  have hvle : v.val ≤ C.inf := by have := hfok.2.1; unfold Ctx.inf; exact this
  have hlen' : fd'.length = fd.length := by rw [hfd']; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro x' y' hn
    have hxi : C.li + p - 1 ≤ C.i0 := by
      have hlile : C.li ≤ C.i0 := by have := (hG.wa.1 C.i0 hG.i0a).2; rw [← hG.li_eq] at this; exact this
      have hps2 : p ≤ C.i0 - C.li + 1 := hps
      omega
    have hyj : C.lj + q - 1 ≤ C.j0 := by
      have hljle : C.lj ≤ C.j0 := by have := (hG.wb.1 C.j0 hG.j0a).2; rw [← hG.lj_eq] at this; exact this
      have hqs2 : q ≤ C.j0 - C.lj + 1 := hqs
      omega
    by_cases hc : C.LeafPair (C.li + p - 1) (C.lj + q - 1) ∧ InBand C.t (C.li + p - 1) (C.lj + q - 1)
    · obtain ⟨hteq, hidT⟩ := htd1 hc
      have hne : ¬ (x' = C.li + p - 1 ∧ y' = C.lj + q - 1) := fun h => hn (by
        obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact ⟨hc.1, hxi, hyj⟩)
      rw [hteq, rd_set_ne td C.w C.t C.inf (C.li + p - 1) (C.lj + q - 1) x' y' v hw hc.2
        (fun h => hne ⟨h.1.symm, h.2.symm⟩)]
      exact hFr x' y' hn
    · rw [htd2 hc]; exact hFr x' y' hn

end Ctx



/-- Connection of a context to two concrete trees. -/
structure Ctx.Link (C : Ctx) (a b : ted.PostTree) : Prop where
  n1 : a.label.length = C.n
  n2 : a.lml.length = C.n
  n3 : a.kind.length = C.n
  m1 : b.label.length = C.m
  m2 : b.lml.length = C.m
  m3 : b.kind.length = C.m
  la_eq : ∀ u, 1 ≤ u → u ≤ C.n → C.la u = (a.lml.val[u - 1]!).val
  lb_eq : ∀ u, 1 ≤ u → u ≤ C.m → C.lb u = (b.lml.val[u - 1]!).val
  ren_eq : ∀ x y, C.ren x y = rcost a b x y
  nbig : C.n < 2 ^ 31
  mbig : C.m < 2 ^ 31
  wbig : (C.n + 1) * C.w < 2 ^ 32
  tbig : 2 * C.t + 3 < 2 ^ 31

/-- One run of the column loop of a row. -/
theorem fill_inner_loop_spec (C : Ctx) (hG : C.Good) (a b : ted.PostTree) (hK : C.Link a b) (hw : C.w = 2 * C.t + 1) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj)
    (t : Std.Usize) (inf : Std.U32) (w li lj p qhi x lx : Std.Usize) (td fd : Slice Std.U32)
    (st : ted.Stats) (q : Std.Usize) (row_min : Std.U32) (qlo : Nat)
    (ht : t.val = C.t) (hinf : inf.val = C.inf) (hww : w.val = C.w) (hlii : li.val = C.li)
    (hljj : lj.val = C.lj) (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ C.si)
    (hqhi : qhi.val = min C.sj (p.val + C.t)) (hx : x.val = C.li + p.val - 1)
    (hlx : lx.val = C.la x.val)
    (hq1 : 1 ≤ q.val) (hqlo : p.val ≤ qlo + C.t) (hqq : qlo ≤ q.val) (hqle : q.val ≤ qhi.val + 1)
    (hfdlen : (C.si + 1) * C.w ≤ fd.val.length) (htdlen : (C.n + 1) * C.w ≤ td.val.length)
    (hR : C.RowsInv fd.val p.val q.val) (hT : C.TdInv td.val p.val q.val)
    (hFB : Ctx.FdB fd.val C.inf) (hTB : Ctx.FdB td.val C.inf) (hM : C.RowMin fd.val p.val q.val qlo row_min.val)
    (td0 : List Std.U32) (hFr : C.Frame td0 td.val) :
    ted.fill_window_loop2_loop0 a.label a.lml a.keyroots a.kids a.kind b.label b.lml b.keyroots b.kids b.kind
      td fd st t inf w li lj q p qhi x lx row_min ⦃ r =>
      r.2.2.2.1.val = qhi.val + 1 ∧ r.1.val.length = td.val.length ∧ r.2.1.val.length = fd.val.length ∧
      C.RowsInv r.2.1.val p.val (qhi.val + 1) ∧ C.TdInv r.1.val p.val (qhi.val + 1) ∧
      Ctx.FdB r.2.1.val C.inf ∧ Ctx.FdB r.1.val C.inf ∧ C.RowMin r.2.1.val p.val (qhi.val + 1) qlo r.2.2.2.2.val ∧
      C.Frame td0 r.1.val ⦄ := by
  unfold ted.fill_window_loop2_loop0
  apply loop.spec_decr_nat
    (measure := fun s => qhi.val + 1 - s.2.2.2.1.val)
    (inv := fun s => 1 ≤ s.2.2.2.1.val ∧ qlo ≤ s.2.2.2.1.val ∧ s.2.2.2.1.val ≤ qhi.val + 1 ∧
      s.1.val.length = td.val.length ∧ s.2.1.val.length = fd.val.length ∧
      C.RowsInv s.2.1.val p.val s.2.2.2.1.val ∧ C.TdInv s.1.val p.val s.2.2.2.1.val ∧
      Ctx.FdB s.2.1.val C.inf ∧ Ctx.FdB s.1.val C.inf ∧ C.RowMin s.2.1.val p.val s.2.2.2.1.val qlo s.2.2.2.2.val ∧
      C.Frame td0 s.1.val)
  · intro s hs
    obtain ⟨td1, fd1, st1, q1, rm1⟩ := s
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hs
    dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⊢
    have hsi : C.si = C.i0 - C.li + 1 := rfl
    have hsj : C.sj = C.j0 - C.lj + 1 := rfl
    have hlile : C.li ≤ C.i0 := by have := (hG.wa.1 C.i0 hG.i0a).2; rw [← hG.li_eq] at this; exact this
    have hljle : C.lj ≤ C.j0 := by have := (hG.wb.1 C.j0 hG.j0a).2; rw [← hG.lj_eq] at this; exact this
    have hxi : C.li + p.val - 1 ≤ C.i0 := by omega
    have hxn : C.li + p.val - 1 ≤ C.n := by have := hG.i0b; omega
    by_cases hqq' : q1 ≤ qhi
    · have hqle2 : q1.val ≤ qhi.val := hqq'
      have hqs : q1.val ≤ C.sj := by omega
      have hyj : C.lj + q1.val - 1 ≤ C.j0 := by omega
      have hym : C.lj + q1.val - 1 ≤ C.m := by have := hG.j0b; omega
      have hband : InBand C.t p.val q1.val := by unfold InBand; omega
      have hcA := Ctx.closed_win C hG hxi
      have hcB := Ctx.closed_winB C hG hyj
      have hlx1 : C.li ≤ C.la (C.li + p.val - 1) := hcA _ (by omega) (Nat.le_refl _)
      have hlx2 : C.la (C.li + p.val - 1) ≤ C.li + p.val - 1 := (hG.wa.1 _ (by omega)).2
      have hly1 : C.lj ≤ C.lb (C.lj + q1.val - 1) := hcB _ (by omega) (Nat.le_refl _)
      have hlb' : C.lb (C.lj + q1.val - 1) = (b.lml.val[C.lj + q1.val - 2]!).val := by
        have := hK.lb_eq (C.lj + q1.val - 1) (by omega) hym
        have e : C.lj + q1.val - 1 - 1 = C.lj + q1.val - 2 := by omega
        rw [e] at this; exact this
      have hlx' : lx.val = C.la (C.li + p.val - 1) := by rw [hlx, hx]
      have hmul1 : ∀ r, r ≤ C.si → (r + 1) * C.w ≤ (C.si + 1) * C.w := fun r hr => Nat.mul_le_mul_right _ (by omega)
      have hmul2 : ∀ r, r ≤ C.n → (r + 1) * C.w ≤ (C.n + 1) * C.w := fun r hr => Nat.mul_le_mul_right _ (by omega)
      have hsi_n : C.si ≤ C.n := by have := hG.i0b; omega
      have hmul3 := Nat.mul_le_mul_right C.w (show C.si + 1 ≤ C.n + 1 by omega)
      have hc := cell_step a b t inf w li lj p qhi x lx td1 fd1 st1 q1 rm1
        (by rw [hww, ht]; exact hw) (by rw [hinf, ht]; rfl) hqle2 h1 hp1
        (by rw [ht]; exact hband) (by omega) (by omega) (by omega)
        (by rw [hK.n1]; omega) (by rw [hK.m1]; omega) (by rw [hK.m2]; omega)
        (by omega) (by omega) (by rw [hK.n3]; omega) (by rw [hK.m3]; omega)
        (by have := hK.mbig; have := hG.j0b; omega)
        (by rw [hljj, ← hlb']; omega)
        (by rw [hww, h5]; have := hmul1 p.val hp2; omega)
        (by rw [hww]; have := hmul1 p.val hp2; have := hK.wbig; omega)
        (by rw [hww, h4, hx]; have := hmul2 (C.li + p.val - 1) hxn; omega)
        (by rw [hww, hx]; have := hmul2 (C.li + p.val - 1) hxn; have := hK.wbig; omega)
        (by rw [hinf]; exact h8) (by rw [hinf]; exact h9)
        (by rw [hinf]; unfold Ctx.inf; have := hK.tbig; omega)
      refine WP.spec_mono hc ?_
      intro r hr
      cases r with
      | done y => exact absurd hr (by simp)
      | cont s' =>
        obtain ⟨td2, fd2, st2, q2, rm2⟩ := s'
        dsimp only at hr ⊢
        obtain ⟨vv, hv1, hfd1', htd1', hq', hrm'⟩ := hr
        rw [hww, ht, hinf, hlii, hljj, hx, hlx', ← hlb'] at hv1
        rw [← hK.ren_eq] at hv1
        have hxy_band : InBand C.t (C.li + p.val - 1) (C.lj + q1.val - 1) →
            bandIdx C.w C.t (C.li + p.val - 1) (C.lj + q1.val - 1) < td1.val.length := by
          intro hb
          have := bandIdx_lt C.w C.t _ _ hw hb
          have := hmul2 (C.li + p.val - 1) hxn
          omega
        have hidx : bandIdx C.w C.t p.val q1.val < fd1.val.length := by
          have := bandIdx_lt C.w C.t _ _ hw hband
          have := hmul1 p.val hp2
          omega
        have hfd'' : fd2.val = fd1.val.set (bandIdx C.w C.t p.val q1.val) vv := by
          rw [hfd1', hww, ht]
        have hleaf : (lx.val = li.val ∧ (b.lml.val[lj.val + q1.val - 2]!).val = lj.val ∧
            InBand t.val (x.val) (lj.val + q1.val - 1)) ↔
            (C.LeafPair (C.li + p.val - 1) (C.lj + q1.val - 1) ∧
              InBand C.t (C.li + p.val - 1) (C.lj + q1.val - 1)) := by
          rw [hlx', hlii, hljj, hx, ht, ← hlb']
          unfold Ctx.LeafPair
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
        have htd1c : (lx.val = li.val ∧ (b.lml.val[lj.val + q1.val - 2]!).val = lj.val ∧
            InBand t.val (x.val) (lj.val + q1.val - 1)) →
            td2.val = td1.val.set (bandIdx w.val t.val x.val (lj.val + q1.val - 1)) vv := by
          intro hc; rw [htd1', if_pos hc]
        have htd2c : ¬ (lx.val = li.val ∧ (b.lml.val[lj.val + q1.val - 2]!).val = lj.val ∧
            InBand t.val (x.val) (lj.val + q1.val - 1)) → td2.val = td1.val := by
          intro hc; rw [htd1', if_neg hc]
        have hstep := Ctx.inner_step C hG hw fd1.val td1.val fd2.val td2.val vv (qlo := qlo)
          (rm := rm1.val) hli hlj hp1 h1 hp2 hqs hband h6 h7 h8 h9 h10 td0 h11 hv1 hfd'' hidx
          (by
            intro hc'
            have := htd1c (hleaf.mpr hc')
            rw [hww, ht, hx, hljj] at this
            exact ⟨this, hxy_band hc'.2⟩)
          (fun hc' => htd2c (fun h => hc' (hleaf.mp h)))
        obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hstep
        have hq'' : q2.val = q1.val + 1 := hq'
        have hrm2 : rm2.val = min rm1.val vv.val := hrm'
        rw [hrm2]
        refine ⟨⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
        · by_cases hc3 : (lx.val = li.val ∧ (b.lml.val[lj.val + q1.val - 2]!).val = lj.val ∧
              InBand t.val (x.val) (lj.val + q1.val - 1))
          · rw [htd1c hc3]; simp [h4]
          · rw [htd2c hc3]; exact h4
        · rw [hfd'']; simp [h5]
        · rw [hq'']; exact k1
        · rw [hq'']; exact k2
        · exact k3
        · exact k4
        · rw [hq'']; exact k5
        · exact k6
    · -- the loop is over
      have hq3 : q1.val = qhi.val + 1 := by
        have : ¬ q1.val ≤ qhi.val := hqq'
        omega
      unfold ted.fill_window_loop2_loop0.body
      rw [if_neg hqq']
      simp only [WP.spec_ok]
      rw [hq3] at h6 h7 h10
      exact ⟨hq3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · exact ⟨hq1, hqq, hqle, rfl, rfl, hR, hT, hFB, hTB, hM, hFr⟩


namespace Ctx

theorem rows_start' (C : Ctx) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) {fd : List Std.U32} {p : Nat}
    (hR : C.RowsInv fd p 1) : C.RowsInv fd p (max (p - C.t) 1) := by
  intro p' q' hp' hq' hc
  rcases hc with h | h | h | ⟨h1, h2⟩
  · exact hR p' q' hp' hq' (Or.inl h)
  · exact hR p' q' hp' hq' (Or.inr (Or.inl h))
  · exact hR p' q' hp' hq' (Or.inr (Or.inr (Or.inl h)))
  · by_cases e : q' = 0
    · exact hR p' q' hp' hq' (Or.inr (Or.inr (Or.inl e)))
    · subst h1
      apply okF_out C fd hli hlj
      intro hb
      unfold InBand at hb
      omega

/-- A leaf pair of the window whose window cell is out of the band cannot meet the budget. -/
theorem leaf_budget_false (C : Ctx) (hG : C.Good) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) {x y p q : Nat}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hx : x = C.li + p - 1) (hy : y = C.lj + q - 1) (hl : C.LeafPair x y)
    (hout : ¬ (p ≤ q + C.t ∧ q ≤ p + C.t)) :
    ¬ (TD C.la C.lb C.ren x y + adf (C.la x) (C.lb y) ≤ C.t) := by
  have := TD_eq_Dw C hp hq hli hlj (by rw [← hx]; exact hl.1) (by rw [← hy]; exact hl.2)
  rw [← hx, ← hy] at this
  rw [this]
  have hs := Dw_size (la := C.la) (lb := C.lb) (ren := C.ren) hli hlj p q
  omega

theorem td_start (C : Ctx) (hG : C.Good) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) {td : List Std.U32} {p : Nat}
    (hp : 1 ≤ p) (hT : C.TdInv td p 1) : C.TdInv td p (max (p - C.t) 1) := by
  intro x y hx1 hx2 hy1 hy2
  have hold := hT x y hx1 hx2 hy1 hy2
  refine ⟨hold.1, fun hd hb => ?_⟩
  by_cases hd1 : C.Done p 1 x y
  · exact hold.2 hd1 hb
  · exfalso
    obtain ⟨h1, h2, h3⟩ := hd
    unfold Ctx.Done at hd1
    rcases h3 with h3 | ⟨h3, h4 | ⟨h4, h5⟩⟩
    · exact hd1 ⟨h1, h2, Or.inl h3⟩
    · exact hd1 ⟨h1, h2, Or.inr ⟨h3, Or.inl h4⟩⟩
    · have hly := (hG.wb.1 y hy1).2
      have : C.lb y = C.lj := h3.2
      have hq : 1 ≤ y - C.lj + 1 := by omega
      by_cases hy : y < C.lj
      · omega
      refine leaf_budget_false C hG hli hlj hp hq (by omega) (by omega) h3 ?_ hb
      omega

theorem rows_end (C : Ctx) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) {fd : List Std.U32} {p qhi : Nat}
    (hqhi : qhi = min C.sj (p + C.t)) (hR : C.RowsInv fd p (qhi + 1)) : C.RowsInv fd (p + 1) 1 := by
  intro p' q' hp' hq' hc
  by_cases e : p' = p
  · subst e
    by_cases h0 : q' = 0
    · exact hR p' q' hp' hq' (Or.inr (Or.inr (Or.inl h0)))
    · by_cases hlt : q' < qhi + 1
      · exact hR p' q' hp' hq' (Or.inr (Or.inr (Or.inr ⟨rfl, hlt⟩)))
      · apply okF_out C fd hli hlj
        intro hb; unfold InBand at hb; omega
  · apply hR p' q' hp' hq'
    rcases hc with h | h | h | ⟨h1, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl (by omega)))

theorem td_end (C : Ctx) (hG : C.Good) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) {td : List Std.U32} {p qhi : Nat}
    (hp : 1 ≤ p) (hqhi : qhi = min C.sj (p + C.t)) (hT : C.TdInv td p (qhi + 1)) :
    C.TdInv td (p + 1) 1 := by
  intro x y hx1 hx2 hy1 hy2
  have hold := hT x y hx1 hx2 hy1 hy2
  refine ⟨hold.1, fun hd hb => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hd
  by_cases hdn : C.Done p (qhi + 1) x y
  · exact hold.2 hdn hb
  · exfalso
    unfold Ctx.Done at hdn
    rcases h3 with h3 | ⟨h3, h4⟩
    · exact hdn ⟨h1, h2, Or.inl h3⟩
    · have hly := (hG.wb.1 y hy1).2
      have : C.lb y = C.lj := h3.2
      have hq : 1 ≤ y - C.lj + 1 := by omega
      have hyl : C.lj ≤ y := by omega
      have hxx : x < C.li + p - 1 ∨ x = C.li + p - 1 := by
        rcases h4 with h4 | ⟨h4, h5⟩
        · omega
        · exfalso; omega
      rcases hxx with hxx | hxx
      · exact hdn ⟨h1, h2, Or.inr ⟨h3, Or.inl hxx⟩⟩
      by_cases hy3 : y < C.lj + (qhi + 1) - 1
      · exact hdn ⟨h1, h2, Or.inr ⟨h3, Or.inr ⟨hxx, hy3⟩⟩⟩
      · refine leaf_budget_false C hG hli hlj hp hq (by omega) (by omega) h3 ?_ hb
        have hsj : y - C.lj + 1 ≤ C.sj := by
          have := h2; simp only [Ctx.sj]; omega
        omega

theorem hall_of_small (C : Ctx) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) {p : Nat} (hbig : C.sj + C.t < p) :
    ∀ q', q' ≤ C.sj → C.t < Dw C.la C.lb C.ren C.li C.lj p q' + C.δ := by
  intro q' hq'
  have := Dw_size (la := C.la) (lb := C.lb) (ren := C.ren) hli hlj p q'
  omega

theorem hall_of_rowmin (C : Ctx) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) {fd : List Std.U32} {p qhi qlo rm : Nat}
    (hR : C.RowsInv fd p (qhi + 1)) (hM : C.RowMin fd p (qhi + 1) qlo rm) (hps : p ≤ C.si)
    (hqhi : qhi = min C.sj (p + C.t)) (hqlo : qlo = max (p - C.t) 1) (hrm : C.t < rm) :
    ∀ q', q' ≤ C.sj → C.t < Dw C.la C.lb C.ren C.li C.lj p q' + C.δ := by
  intro q' hq'
  have hs := Dw_size (la := C.la) (lb := C.lb) (ren := C.ren) hli hlj p q'
  by_cases hb : InBand C.t p q'
  · have hcond : q' = 0 ∨ (qlo ≤ q' ∧ q' < qhi + 1) := by
      by_cases h0 : q' = 0
      · exact Or.inl h0
      · unfold InBand at hb; exact Or.inr ⟨by omega, by omega⟩
    have h1 := hM.2 q' hq' hcond hb
    have h2 := hR p q' hps hq' (by
      rcases hcond with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h.2⟩)))
    unfold Ctx.OkF FOK at h2
    by_cases hle : Dw C.la C.lb C.ren C.li C.lj p q' + C.δ ≤ C.t
    · have := h2.2.2 hle
      omega
    · omega
  · unfold InBand at hb; omega

theorem exit_final (C : Ctx) (hG : C.Good) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) {td : List Std.U32}
    {p qhi : Nat} (hp1 : 1 ≤ p) (hps : p ≤ C.si)
    (hall : ∀ q', q' ≤ C.sj → C.t < Dw C.la C.lb C.ren C.li C.lj p q' + C.δ)
    (hT : C.TdInv td p (qhi + 1)) : C.TdInv td (C.si + 1) 1 := by
  intro x y hx1 hx2 hy1 hy2
  have hold := hT x y hx1 hx2 hy1 hy2
  refine ⟨hold.1, fun hd hb => ?_⟩
  by_cases hdn : C.Done p (qhi + 1) x y
  · exact hold.2 hdn hb
  · exfalso
    obtain ⟨h1, h2, h3⟩ := hd
    unfold Ctx.Done at hdn
    rcases h3 with h3 | ⟨h3, h4⟩
    · exact hdn ⟨h1, h2, Or.inl h3⟩
    · have hly := (hG.wb.1 y hy1).2
      have hlx := (hG.wa.1 x hx1).2
      have hlbj : C.lb y = C.lj := h3.2
      have hlai : C.la x = C.li := h3.1
      have hyl : C.lj ≤ y := by omega
      have hxl : C.li ≤ x := by omega
      -- the row of x is at least p, otherwise the pair is done
      have hrow : p ≤ x - C.li + 1 := by
        by_cases e : x < C.li + p - 1
        · exact absurd ⟨h1, h2, Or.inr ⟨h3, Or.inl e⟩⟩ hdn
        · omega
      have hsj : y - C.lj + 1 ≤ C.sj := by simp only [Ctx.sj]; omega
      have hcA := closed_win C hG h1
      have hcB := closed_winB C hG h2
      obtain ⟨y₀, hy0a, hy0b, hy0c⟩ := D_row_mono (ren := C.ren) hG.wa hG.wb hli hlj
        (x - C.li + 1 - p) (C.li + p - 1) x y (by omega) (by omega) hcA hcB (by omega)
      have hq0 := hall (y₀ + 1 - C.lj) (by omega)
      have e1 : C.lj + (y₀ + 1 - C.lj) - 1 = y₀ := by omega
      unfold Dw at hq0
      rw [e1] at hq0
      have hTDeq := TD_eq_Dw C (p := x - C.li + 1) (q := y - C.lj + 1) (by omega) (by omega) hli hlj
        (by have : C.li + (x - C.li + 1) - 1 = x := by omega
            rw [this]; exact hlai)
        (by have : C.lj + (y - C.lj + 1) - 1 = y := by omega
            rw [this]; exact hlbj)
      have e2 : C.li + (x - C.li + 1) - 1 = x := by omega
      have e3 : C.lj + (y - C.lj + 1) - 1 = y := by omega
      rw [e2, e3] at hTDeq
      unfold Dw at hTDeq
      rw [e2, e3] at hTDeq
      have e4 : adf (C.la x) (C.lb y) = C.δ := by unfold Ctx.δ; rw [hlai, hlbj]
      rw [hTDeq, e4] at hb
      omega

end Ctx


/-- A column loop that does not start returns its state. -/
theorem inner_loop_empty (a b : ted.PostTree) (t : Std.Usize) (inf : Std.U32) (w li lj p qhi x lx : Std.Usize)
    (td fd : Slice Std.U32) (st : ted.Stats) (q : Std.Usize) (row_min : Std.U32) (h : ¬ q ≤ qhi) :
    ted.fill_window_loop2_loop0 a.label a.lml a.keyroots a.kids a.kind b.label b.lml b.keyroots b.kids b.kind
      td fd st t inf w li lj q p qhi x lx row_min ⦃ r => r = (td, fd, st, q, row_min) ⦄ := by
  unfold ted.fill_window_loop2_loop0
  apply loop.spec_decr_nat
    (measure := fun _ => 0)
    (inv := fun s => s = (td, fd, st, q, row_min))
  · intro s hs
    subst hs
    unfold ted.fill_window_loop2_loop0.body
    dsimp only
    rw [if_neg h]
    simp only [WP.spec_ok]
  · rfl


/-- The initial row minimum of a row: the first cell of the row when it is inside the band. -/
theorem rowmin_if_spec (fd : Slice Std.U32) (w t : Std.Usize) (inf : Std.U32) (p : Std.Usize)
    (hw : w.val = 2 * t.val + 1) (hlen : (p.val + 1) * w.val ≤ fd.val.length)
    (hbig : (p.val + 1) * w.val < 2 ^ 32) :
    (if p ≤ t then (do let i5 ← ted.bidx w t p 0#usize; Slice.index_usize fd i5) else ok inf) ⦃ r =>
      r.val = if p.val ≤ t.val then rd fd.val w.val t.val inf.val p.val 0 else inf.val ⦄ := by
  split
  · rename_i h
    have hp : p.val ≤ t.val := h
    have hb : InBand t.val p.val 0 := by unfold InBand; omega
    have hlt := bandIdx_lt w.val t.val p.val 0 hw hb
    step as ⟨i, hi⟩
    have hil : i.val < fd.val.length := by omega
    step as ⟨r, hr⟩
    simp only [hp, ↓reduceIte, rd, hb]
    rw [hr, ← hi, getU_eq _ _ hil]
  · rename_i h
    have hp : ¬ p.val ≤ t.val := h
    simp only [WP.spec_ok, hp, ↓reduceIte]

/-- The row loop of `fill_window`. -/
theorem fill_rows_loop_spec (C : Ctx) (hG : C.Good) (a b : ted.PostTree) (hK : C.Link a b)
    (hw : C.w = 2 * C.t + 1) (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj)
    (tau : Std.U32) (t : Std.Usize) (inf : Std.U32) (w li lj si sj : Std.Usize)
    (td fd : Slice Std.U32) (st : ted.Stats) (q p : Std.Usize) (td0 : List Std.U32)
    (htau : tau.val = C.t) (ht : t.val = C.t) (hinf : inf.val = C.inf) (hww : w.val = C.w)
    (hlii : li.val = C.li) (hljj : lj.val = C.lj) (hsi : si.val = C.si) (hsj : sj.val = C.sj)
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ C.si + 1)
    (hfdlen : (C.si + 1) * C.w ≤ fd.val.length) (htdlen : (C.n + 1) * C.w ≤ td.val.length)
    (hR : C.RowsInv fd.val p.val 1) (hT : C.TdInv td.val p.val 1)
    (hFB : Ctx.FdB fd.val C.inf) (hTB : Ctx.FdB td.val C.inf) (hFr : C.Frame td0 td.val) :
    ted.fill_window_loop2 a.label a.lml a.keyroots a.kids a.kind b.label b.lml b.keyroots b.kids b.kind
      td fd tau st t inf w li lj si sj q p ⦃ r =>
      r.1.val.length = td.val.length ∧ Ctx.FdB r.1.val C.inf ∧ C.TdInv r.1.val (C.si + 1) 1 ∧
        C.Frame td0 r.1.val ⦄ := by
  unfold ted.fill_window_loop2
  apply loop.spec_decr_nat
    (measure := fun s => C.si + 1 - s.2.2.2.2.val)
    (inv := fun s => 1 ≤ s.2.2.2.2.val ∧ s.2.2.2.2.val ≤ C.si + 1 ∧
      s.1.val.length = td.val.length ∧ s.2.1.val.length = fd.val.length ∧
      C.RowsInv s.2.1.val s.2.2.2.2.val 1 ∧ C.TdInv s.1.val s.2.2.2.2.val 1 ∧
      Ctx.FdB s.2.1.val C.inf ∧ Ctx.FdB s.1.val C.inf ∧ C.Frame td0 s.1.val)
  · intro s hs
    obtain ⟨td1, fd1, st1, q1, p1⟩ := s
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
    dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
    unfold ted.fill_window_loop2.body
    by_cases hpp : p1 ≤ si
    · rw [if_pos hpp]
      have hpps : p1.val ≤ C.si := by have : p1.val ≤ si.val := hpp; omega
      have hlile : C.li ≤ C.i0 := by have := (hG.wa.1 C.i0 hG.i0a).2; rw [← hG.li_eq] at this; exact this
      have hsi' : C.si = C.i0 - C.li + 1 := rfl
      have hxi : C.li + p1.val - 1 ≤ C.i0 := by omega
      have hxn : C.li + p1.val - 1 ≤ C.n := by have := hG.i0b; omega
      have hsin : C.si ≤ C.n := by have := hG.i0b; omega
      have hmulw : (p1.val + 1) * C.w ≤ (C.si + 1) * C.w := Nat.mul_le_mul_right _ (by omega)
      have hmulw2 : (C.si + 1) * C.w ≤ (C.n + 1) * C.w := Nat.mul_le_mul_right _ (by omega)
      have hbigw := hK.wbig
      obtain ⟨i, hi, hiv⟩ : ∃ i, core.num.Usize.saturating_sub p1 t = i ∧ i.val = p1.val - t.val :=
        ⟨_, rfl, usize_sat_sub_val _ _⟩
      simp only [lift, bind_tc_ok]
      rw [hi]
      have hpt : p1.val + t.val < 2 ^ 32 := by have := hK.nbig; have := hK.tbig; omega
      have hlp : li.val + p1.val < 2 ^ 32 := by have := hK.nbig; omega
      step as ⟨qlo, hqlo⟩
      step as ⟨i1, hi1⟩
      step as ⟨qhi, hqhi⟩
      step as ⟨i2, hi2⟩
      step as ⟨x, hx⟩
      step as ⟨i3, hi3⟩
      have hxv : x.val = C.li + p1.val - 1 := by omega
      have hi3b : i3.val < a.lml.val.length := by
        have := hK.n2; have h2 : a.lml.length = C.n := this
        have : a.lml.val.length = C.n := h2
        omega
      step as ⟨i4, hi4⟩
      have hwt : w.val = 2 * t.val + 1 := by rw [hww, ht]; exact hw
      step with rowmin_if_spec fd1 w t inf p1 hwt (by rw [hww]; have := hmulw; omega)
        (by rw [hww]; have := hmulw; omega) as ⟨rm0, hrm0⟩
      -- facts about the quantities just computed
      have hlxv : (UScalar.cast .Usize i4).val = C.la (C.li + p1.val - 1) := by
        have e : C.li + p1.val - 1 - 1 = i3.val := by omega
        rw [U32.cast_Usize_val_eq, hi4, hK.la_eq _ (by omega) hxn, e, getU_eq _ _ hi3b]
      have hqlov : qlo.val = max (p1.val - C.t) 1 := by rw [hqlo, hiv, ht]
      have hqhiv : qhi.val = min C.sj (p1.val + C.t) := by
        rw [hqhi, hsj, hi1, ht]
      have hqlo1 : 1 ≤ qlo.val := by omega
      have hrm0v : rm0.val = if p1.val ≤ C.t then rd fd1.val C.w C.t C.inf p1.val 0 else C.inf := by
        rw [hrm0, ht, hww, hinf]
      by_cases hne : qlo ≤ qhi
      · have hnev : qlo.val ≤ qhi.val := hne
        have hM0 : C.RowMin fd1.val p1.val qlo.val qlo.val rm0.val := by
          refine ⟨?_, ?_⟩
          · rw [hrm0v]
            split
            · exact rd_le _ _ _ _ _ _ hw (by rw [h4]; have := hmulw; omega) h7
            · exact Nat.le_refl _
          · intro q' hq' hc hb
            have h0 : q' = 0 := by
              rcases hc with h | ⟨h, h'⟩
              · exact h
              · omega
            subst h0
            have hpt2 : p1.val ≤ C.t := by unfold InBand at hb; omega
            rw [hrm0v]; simp [hpt2]
        have hqle : qlo.val ≤ qhi.val + 1 := by omega
        have hR2 : C.RowsInv fd1.val p1.val qlo.val := by rw [hqlov]; exact Ctx.rows_start' C hli hlj h5
        have hT2 : C.TdInv td1.val p1.val qlo.val := by rw [hqlov]; exact Ctx.td_start C hG hli hlj h1 h6
        have hlxv' : (UScalar.cast .Usize i4).val = C.la x.val := by rw [hlxv, hxv]
        refine WP.spec_bind (fill_inner_loop_spec C hG a b hK hw hli hlj t inf w li lj p1 qhi x
            (UScalar.cast .Usize i4) td1 fd1 st1 qlo rm0 qlo.val ht hinf hww hlii hljj h1 hpps hqhiv hxv hlxv' hqlo1
            (by omega) (Nat.le_refl _) hqle (by rw [h4]; exact hfdlen) (by rw [h3]; exact htdlen)
            hR2 hT2 h7 h8 hM0 td0 h9) ?_
        rintro ⟨td2, fd2, st2, q2, rm2⟩ ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩
        dsimp only at k1 k2 k3 k4 k5 k6 k7 k8 k9
        have hnq : ¬ qlo > qhi := by have : qlo.val ≤ qhi.val := hnev; intro h; have : qhi.val < qlo.val := h; omega
        show (if qlo > qhi then ok (done (td2, fd2, st2)) else
          (if rm2 > tau then ok (done (td2, fd2, st2))
          else (do let p1' ← p1 + 1#usize; ok (cont (td2, fd2, st2, q2, p1'))))) ⦃ _ ⦄
        simp only [if_neg hnq]
        show (if rm2 > tau then ok (done (td2, fd2, st2))
          else (do let p1' ← p1 + 1#usize; ok (cont (td2, fd2, st2, q2, p1')))) ⦃ _ ⦄
        by_cases hrm : rm2 > tau
        · simp only [if_pos hrm]
          simp only [WP.spec_ok]
          have hrmv : C.t < rm2.val := by have : tau.val < rm2.val := hrm; omega
          have hall := Ctx.hall_of_rowmin C hli hlj k4 k8 hpps hqhiv hqlov hrmv
          exact ⟨by rw [k2, h3], k7, Ctx.exit_final C hG hli hlj h1 hpps hall k5, k9⟩
        · simp only [if_neg hrm]
          step as ⟨p2, hp2'⟩
          refine ⟨by omega, by omega, by rw [k2, h3], by rw [k3, h4], ?_, ?_, k6, k7, k9, by omega⟩
          · have := Ctx.rows_end C hli hlj hqhiv k4
            rw [hp2']; exact this
          · have := Ctx.td_end C hG hli hlj h1 hqhiv k5
            rw [hp2']; exact this
      · -- the column range is empty, so the row is out of reach of the band
        have hemp : ¬ qlo ≤ qhi := hne
        have hbig : C.sj + C.t < p1.val := by
          have : ¬ qlo.val ≤ qhi.val := hemp
          have hsj1 : 1 ≤ C.sj := by simp only [Ctx.sj]; have := (hG.wb.1 C.j0 hG.j0a).2; rw [← hG.lj_eq] at this; omega
          omega
        refine WP.spec_bind (inner_loop_empty a b t inf w li lj p1 qhi x (UScalar.cast .Usize i4) td1 fd1 st1 qlo rm0 hemp) ?_
        rintro ⟨td2, fd2, st2, q2, rm2⟩ hr2
        simp only [Prod.mk.injEq] at hr2
        obtain ⟨e1, e2, e3, e4, e5⟩ := hr2
        subst e1 e2
        have hqq : qlo > qhi := by have : ¬ qlo.val ≤ qhi.val := hemp; show qhi.val < qlo.val; omega
        show (if qlo > qhi then ok (done (td2, fd2, st2)) else
          (if rm2 > tau then ok (done (td2, fd2, st2))
          else (do let p1' ← p1 + 1#usize; ok (cont (td2, fd2, st2, q2, p1'))))) ⦃ _ ⦄
        simp only [if_pos hqq]
        simp only [WP.spec_ok]
        have hall := Ctx.hall_of_small C hli hlj hbig
        exact ⟨h3, h8, Ctx.exit_final C hG hli hlj h1 hpps hall (qhi := 0) h6, h9⟩
    · rw [if_neg hpp]
      simp only [WP.spec_ok]
      have : p1.val = C.si + 1 := by
        have : ¬ p1.val ≤ si.val := hpp
        omega
      rw [this] at h6
      exact ⟨h3, h8, h6, h9⟩
  · exact ⟨hp1, hp2, rfl, rfl, hR, hT, hFB, hTB, hFr⟩


theorem cast_u32_usize (q : Std.Usize) (h : q.val < 2 ^ 32) : (UScalar.cast .U32 q).val = q.val := by
  rw [UScalar.cast_val_eq]
  simp only [UScalarTy.numBits]
  exact Nat.mod_eq_of_lt h

/-- The first row of the window table: the cell `(0, q)` holds `q`. -/
theorem fill_row0_spec (t w lim_q : Std.Usize) (fd : Slice Std.U32) (q : Std.Usize) (T W : Nat)
    (hq : q.val = 1) (ht : t.val = T) (hw : w.val = W) (hW : W = 2 * T + 1) (hlim : lim_q.val ≤ T)
    (hlen : W ≤ fd.val.length) (hbig : W < 2 ^ 32) (hb : Ctx.FdB fd.val (T + 1)) :
    ted.fill_window_loop0 fd t w lim_q q ⦃ r =>
      r.1.val.length = fd.val.length ∧ Ctx.FdB r.1.val (T + 1) ∧
      (∀ k, 1 ≤ k → k ≤ lim_q.val → rd r.1.val W T (T + 1) 0 k = k) ∧
      (∀ x y, ¬ (x = 0 ∧ 1 ≤ y ∧ y ≤ lim_q.val) → rd r.1.val W T (T + 1) x y = rd fd.val W T (T + 1) x y) ⦄ := by
  unfold ted.fill_window_loop0
  apply loop.spec_decr_nat
    (measure := fun s => lim_q.val + 1 - s.2.val)
    (inv := fun s => 1 ≤ s.2.val ∧ s.2.val ≤ lim_q.val + 1 ∧ s.1.val.length = fd.val.length ∧
      Ctx.FdB s.1.val (T + 1) ∧ (∀ k, 1 ≤ k → k < s.2.val → rd s.1.val W T (T + 1) 0 k = k) ∧
      (∀ x y, ¬ (x = 0 ∧ 1 ≤ y ∧ y < s.2.val) → rd s.1.val W T (T + 1) x y = rd fd.val W T (T + 1) x y))
  · intro s hs
    obtain ⟨fd1, q1⟩ := s
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    dsimp only at h1 h2 h3 h4 h5 h6 ⊢
    unfold ted.fill_window_loop0.body
    by_cases hqq : q1 ≤ lim_q
    · rw [if_pos hqq]
      have hq1 : q1.val ≤ lim_q.val := hqq
      have hband : InBand T 0 q1.val := by unfold InBand; omega
      have hlt := bandIdx_lt W T 0 q1.val hW hband
      have hbi : bandIdx W T 0 q1.val = q1.val + T := by unfold bandIdx; omega
      have hwt : w.val = 2 * t.val + 1 := by rw [hw, ht]; exact hW
      have hq32 : q1.val < 2 ^ 32 := by omega
      have hidx : bandIdx W T 0 q1.val < fd1.val.length := by rw [h3]; omega
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      step as ⟨s, hs⟩
      step as ⟨q2, hq2⟩
      have hi1v : i1.val = q1.val := by rw [hi1]; exact cast_u32_usize q1 hq32
      have hiv : i.val = bandIdx W T 0 q1.val := by rw [hi, hw, ht]
      have hsv : s.val = fd1.val.set (bandIdx W T 0 q1.val) i1 := by
        rw [hs, Slice.set_val_eq, hiv]
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, by omega⟩
      · rw [hsv]; simp [h3]
      · rw [hsv]; exact Ctx.FdB_set h4 _ _ (by omega)
      · intro k hk1 hk2
        by_cases e : k = q1.val
        · subst e; rw [hsv, rd_set_eq _ _ _ _ _ _ _ hband hidx, hi1v]
        · rw [hsv, rd_set_ne _ _ _ _ _ _ _ _ _ hW hband (fun h => e h.2.symm)]
          exact h5 k hk1 (by omega)
      · intro x y hn
        rw [hsv, rd_set_ne _ _ _ _ _ _ _ _ _ hW hband (fun h => hn ⟨h.1.symm, by omega, by omega⟩)]
        exact h6 x y (fun h => hn ⟨h.1, h.2.1, by omega⟩)
    · rw [if_neg hqq]
      simp only [WP.spec_ok]
      have : q1.val = lim_q.val + 1 := by have : ¬ q1.val ≤ lim_q.val := hqq; omega
      rw [this] at h5 h6
      refine ⟨h3, h4, fun k hk1 hk2 => h5 k hk1 (by omega), fun x y hn => h6 x y (by intro h; exact hn ⟨h.1, h.2.1, by omega⟩)⟩
  · refine ⟨by show 1 ≤ q.val; omega, by show q.val ≤ lim_q.val + 1; omega, rfl, hb, ?_, ?_⟩
    · intro k hk1 hk2; exfalso; have : k < q.val := hk2; omega
    · intro x y _; rfl

/-- The first column of the window table: the cell `(p, 0)` holds `p`. -/
theorem fill_col0_spec (t w lim_p : Std.Usize) (fd : Slice Std.U32) (q : Std.Usize) (T W : Nat)
    (hq : q.val = 1) (ht : t.val = T) (hw : w.val = W) (hW : W = 2 * T + 1) (hlim : lim_p.val ≤ T)
    (hlen : (lim_p.val + 1) * W ≤ fd.val.length) (hbig : (lim_p.val + 1) * W < 2 ^ 32) (hb : Ctx.FdB fd.val (T + 1)) :
    ted.fill_window_loop1 fd t w lim_p q ⦃ r =>
      r.val.length = fd.val.length ∧ Ctx.FdB r.val (T + 1) ∧
      (∀ k, 1 ≤ k → k ≤ lim_p.val → rd r.val W T (T + 1) k 0 = k) ∧
      (∀ x y, ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ lim_p.val) → rd r.val W T (T + 1) x y = rd fd.val W T (T + 1) x y) ⦄ := by
  unfold ted.fill_window_loop1
  apply loop.spec_decr_nat
    (measure := fun s => lim_p.val + 1 - s.2.val)
    (inv := fun s => 1 ≤ s.2.val ∧ s.2.val ≤ lim_p.val + 1 ∧ s.1.val.length = fd.val.length ∧
      Ctx.FdB s.1.val (T + 1) ∧ (∀ k, 1 ≤ k → k < s.2.val → rd s.1.val W T (T + 1) k 0 = k) ∧
      (∀ x y, ¬ (y = 0 ∧ 1 ≤ x ∧ x < s.2.val) → rd s.1.val W T (T + 1) x y = rd fd.val W T (T + 1) x y))
  · intro s hs
    obtain ⟨fd1, q1⟩ := s
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    dsimp only at h1 h2 h3 h4 h5 h6 ⊢
    unfold ted.fill_window_loop1.body
    by_cases hqq : q1 ≤ lim_p
    · rw [if_pos hqq]
      have hq1 : q1.val ≤ lim_p.val := hqq
      have hband : InBand T q1.val 0 := by unfold InBand; omega
      have hlt := bandIdx_lt W T q1.val 0 hW hband
      have hmul : (q1.val + 1) * W ≤ (lim_p.val + 1) * W := Nat.mul_le_mul_right _ (by omega)
      have hwt : w.val = 2 * t.val + 1 := by rw [hw, ht]; exact hW
      have hq32 : q1.val < 2 ^ 32 := by
        have := Nat.le_mul_of_pos_right (lim_p.val + 1) (show 0 < W by omega)
        omega
      have hidx : bandIdx W T q1.val 0 < fd1.val.length := by rw [h3]; omega
      have hexp : (q1.val + 1) * W = q1.val * W + W := by ring
      have htot : q1.val * W + (0 + T - q1.val) < 2 ^ 32 := by
        have := hlt; unfold bandIdx at this; omega
      step as ⟨i, hi⟩
      have hiv : i.val = bandIdx W T q1.val 0 := by rw [hi, hw, ht]
      step as ⟨i1, hi1⟩
      step as ⟨s, hs⟩
      step as ⟨q2, hq2⟩
      have hi1v : i1.val = q1.val := by rw [hi1]; exact cast_u32_usize q1 hq32
      have hsv : s.val = fd1.val.set (bandIdx W T q1.val 0) i1 := by
        rw [hs, Slice.set_val_eq, hiv]
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, by omega⟩
      · rw [hsv]; simp [h3]
      · rw [hsv]; exact Ctx.FdB_set h4 _ _ (by omega)
      · intro k hk1 hk2
        by_cases e : k = q1.val
        · subst e; rw [hsv, rd_set_eq _ _ _ _ _ _ _ hband hidx, hi1v]
        · rw [hsv, rd_set_ne _ _ _ _ _ _ _ _ _ hW hband (fun h => e h.1.symm)]
          exact h5 k hk1 (by omega)
      · intro x y hn
        rw [hsv, rd_set_ne _ _ _ _ _ _ _ _ _ hW hband (fun h => hn ⟨h.2.symm, by omega, by omega⟩)]
        exact h6 x y (fun h => hn ⟨h.1, h.2.1, by omega⟩)
    · rw [if_neg hqq]
      simp only [WP.spec_ok]
      have : q1.val = lim_p.val + 1 := by have : ¬ q1.val ≤ lim_p.val := hqq; omega
      rw [this] at h5 h6
      refine ⟨h3, h4, fun k hk1 hk2 => h5 k hk1 (by omega), fun x y hn => h6 x y (by intro h; exact hn ⟨h.1, h.2.1, by omega⟩)⟩
  · refine ⟨by show 1 ≤ q.val; omega, by show q.val ≤ lim_p.val + 1; omega, rfl, hb, ?_, ?_⟩
    · intro k hk1 hk2; exfalso; have : k < q.val := hk2; omega
    · intro x y _; rfl

end difffold_lines_extract
