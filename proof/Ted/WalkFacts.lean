import Driver
open Aeneas Aeneas.Std Result ControlFlow
open Ted
namespace difffold_lines_extract

/-! One step of the traceback through a window table, as statements about the true distances.

Let `v` be the table value at `(p, q)`. If the cell is on an optimal path (`Dw p q + δ <= t`) the table holds the
truth there and, for the three neighbours the traceback looks at, a table value that matches the step equation
forces the step to be an optimal one. -/

section
variable {la lb : Nat → Nat} {ren : Nat → Nat → Nat} {li lj : Nat}

theorem Dw_le_del (hli : 1 ≤ li) (hlj : 1 ≤ lj) {p : Nat} (q : Nat) (hp : 1 ≤ p) :
    Dw la lb ren li lj p q ≤ Dw la lb ren li lj (p - 1) q + 1 := by
  by_cases hq : q = 0
  · subst hq; rw [Dw_col0 hli hlj, Dw_col0 hli hlj]; omega
  · unfold Dw
    have := D_le_del (la := la) (lb := lb) (ren := ren) li (li + p - 1) lj (lj + q - 1) (by omega) (by omega)
    have e : li + (p - 1) - 1 = li + p - 1 - 1 := by omega
    rw [e]; exact this

theorem Dw_le_ins (hli : 1 ≤ li) (hlj : 1 ≤ lj) (p : Nat) {q : Nat} (hq : 1 ≤ q) :
    Dw la lb ren li lj p q ≤ Dw la lb ren li lj p (q - 1) + 1 := by
  by_cases hp : p = 0
  · subst hp; rw [Dw_row0 hli hlj, Dw_row0 hli hlj]; omega
  · unfold Dw
    have := D_le_ins (la := la) (lb := lb) (ren := ren) li (li + p - 1) lj (lj + q - 1) (by omega) (by omega)
    have e : lj + (q - 1) - 1 = lj + q - 1 - 1 := by omega
    rw [e]; exact this

theorem Dw_le_leaf (hli : 1 ≤ li) (hlj : 1 ≤ lj) {p q : Nat} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hlx : la (li + p - 1) = li) (hly : lb (lj + q - 1) = lj) :
    Dw la lb ren li lj p q ≤ Dw la lb ren li lj (p - 1) (q - 1) + ren (li + p - 1) (lj + q - 1) := by
  unfold Dw
  have hc : clampL li (li + p - 1) (la (li + p - 1)) = li ∧ clampL lj (lj + q - 1) (lb (lj + q - 1)) = lj := by
    unfold clampL; omega
  have := D_le_leaf (la := la) (lb := lb) (ren := ren) li (li + p - 1) lj (lj + q - 1) (by omega) (by omega) hc
  have e1 : li + (p - 1) - 1 = li + p - 1 - 1 := by omega
  have e2 : lj + (q - 1) - 1 = lj + q - 1 - 1 := by omega
  rw [e1, e2]; exact this

theorem Dw_le_nonleaf (hA : WfL la) (hB : WfL lb) (hli : 1 ≤ li) (hlj : 1 ≤ lj) {p q : Nat} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcA : Closed la li (li + p - 1)) (hcB : Closed lb lj (lj + q - 1))
    (hn : ¬ (la (li + p - 1) = li ∧ lb (lj + q - 1) = lj)) :
    Dw la lb ren li lj p q ≤ Dw la lb ren li lj (la (li + p - 1) - li) (lb (lj + q - 1) - lj) +
      D la lb ren (la (li + p - 1)) (li + p - 1) (lb (lj + q - 1)) (lj + q - 1) := by
  unfold Dw
  have hcl := clamp_eq hA hcA hli (by omega : li ≤ li + p - 1)
  have hcl' := clamp_eq hB hcB hlj (by omega : lj ≤ lj + q - 1)
  have hc : ¬ (clampL li (li + p - 1) (la (li + p - 1)) = li ∧ clampL lj (lj + q - 1) (lb (lj + q - 1)) = lj) := by
    rw [hcl, hcl']; exact hn
  have := D_le_nonleaf (la := la) (lb := lb) (ren := ren) li (li + p - 1) lj (lj + q - 1) (by omega) (by omega) hc
  rw [hcl, hcl'] at this
  have hlx1 := hcA (li + p - 1) (by omega) (Nat.le_refl _)
  have hly1 := hcB (lj + q - 1) (by omega) (Nat.le_refl _)
  have e1 : li + (la (li + p - 1) - li) - 1 = la (li + p - 1) - 1 := by omega
  have e2 : lj + (lb (lj + q - 1) - lj) - 1 = lb (lj + q - 1) - 1 := by omega
  rw [e1, e2]; exact this

end
theorem step_sound {t δ D D' v g c : Nat} (hv : FOK t δ D v) (hg : FOK t δ D' g) (hb : D + δ ≤ t)
    (hle : D ≤ D' + c) (heq : g + c = v) : D = D' + c := by
  unfold FOK at hv hg
  have := hv.2.2 hb
  omega

theorem step_complete {t δ D D' v g c : Nat} (hv : FOK t δ D v) (hg : FOK t δ D' g) (hb : D + δ ≤ t)
    (hD : D = D' + c) : g + c = v := by
  unfold FOK at hv hg
  have h1 := hv.2.2 hb
  have h2 := hg.2.2 (by omega)
  omega

theorem split_sound {t δ D D'' T v g tdv : Nat} (hv : FOK t δ D v) (hg : FOK t δ D'' g)
    (hT : min T (t + 1) ≤ tdv ∧ tdv ≤ t + 1) (hb : D + δ ≤ t) (hle : D ≤ D'' + T) (heq : g + tdv = v) :
    D = D'' + T := by
  unfold FOK at hv hg
  have := hv.2.2 hb
  omega

namespace Ctx

variable (C : Ctx) {fd : List Std.U32}

theorem del_sound {p q : Nat} (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) (hp : 1 ≤ p) (hps : p ≤ C.si) (hqs : q ≤ C.sj)
    (hF : ∀ p q, p ≤ C.si → q ≤ C.sj → C.OkF fd p q)
    (hb : Dw C.la C.lb C.ren C.li C.lj p q + C.δ ≤ C.t)
    (heq : rd fd C.w C.t C.inf (p - 1) q + 1 = rd fd C.w C.t C.inf p q) :
    Dw C.la C.lb C.ren C.li C.lj p q = Dw C.la C.lb C.ren C.li C.lj (p - 1) q + 1 :=
  step_sound (hF p q hps hqs) (hF (p - 1) q (by omega) hqs) hb (Dw_le_del hli hlj q hp) heq

theorem del_complete {p q : Nat} (hp : 1 ≤ p) (hps : p ≤ C.si) (hqs : q ≤ C.sj)
    (hF : ∀ p q, p ≤ C.si → q ≤ C.sj → C.OkF fd p q)
    (hb : Dw C.la C.lb C.ren C.li C.lj p q + C.δ ≤ C.t)
    (hD : Dw C.la C.lb C.ren C.li C.lj p q = Dw C.la C.lb C.ren C.li C.lj (p - 1) q + 1) :
    rd fd C.w C.t C.inf (p - 1) q + 1 = rd fd C.w C.t C.inf p q :=
  step_complete (hF p q hps hqs) (hF (p - 1) q (by omega) hqs) hb hD

theorem ins_sound {p q : Nat} (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) (hq : 1 ≤ q) (hps : p ≤ C.si) (hqs : q ≤ C.sj)
    (hF : ∀ p q, p ≤ C.si → q ≤ C.sj → C.OkF fd p q)
    (hb : Dw C.la C.lb C.ren C.li C.lj p q + C.δ ≤ C.t)
    (heq : rd fd C.w C.t C.inf p (q - 1) + 1 = rd fd C.w C.t C.inf p q) :
    Dw C.la C.lb C.ren C.li C.lj p q = Dw C.la C.lb C.ren C.li C.lj p (q - 1) + 1 :=
  step_sound (hF p q hps hqs) (hF p (q - 1) hps (by omega)) hb (Dw_le_ins hli hlj p hq) heq

theorem ins_complete {p q : Nat} (hq : 1 ≤ q) (hps : p ≤ C.si) (hqs : q ≤ C.sj)
    (hF : ∀ p q, p ≤ C.si → q ≤ C.sj → C.OkF fd p q)
    (hb : Dw C.la C.lb C.ren C.li C.lj p q + C.δ ≤ C.t)
    (hD : Dw C.la C.lb C.ren C.li C.lj p q = Dw C.la C.lb C.ren C.li C.lj p (q - 1) + 1) :
    rd fd C.w C.t C.inf p (q - 1) + 1 = rd fd C.w C.t C.inf p q :=
  step_complete (hF p q hps hqs) (hF p (q - 1) hps (by omega)) hb hD

theorem leaf_sound {p q : Nat} (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) (hp : 1 ≤ p) (hq : 1 ≤ q) (hps : p ≤ C.si)
    (hqs : q ≤ C.sj) (hlx : C.la (C.li + p - 1) = C.li) (hly : C.lb (C.lj + q - 1) = C.lj)
    (hF : ∀ p q, p ≤ C.si → q ≤ C.sj → C.OkF fd p q)
    (hb : Dw C.la C.lb C.ren C.li C.lj p q + C.δ ≤ C.t) {rc : Nat}
    (hrc : rc = C.ren (C.li + p - 1) (C.lj + q - 1))
    (heq : rd fd C.w C.t C.inf (p - 1) (q - 1) + rc = rd fd C.w C.t C.inf p q) :
    Dw C.la C.lb C.ren C.li C.lj p q = Dw C.la C.lb C.ren C.li C.lj (p - 1) (q - 1) + rc := by
  subst hrc
  exact step_sound (hF p q hps hqs) (hF (p - 1) (q - 1) (by omega) (by omega)) hb (Dw_le_leaf hli hlj hp hq hlx hly) heq

theorem nonleaf_sound (hG : C.Good) {p q : Nat} (hli : 1 ≤ C.li) (hlj : 1 ≤ C.lj) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hps : p ≤ C.si) (hqs : q ≤ C.sj)
    (hn : ¬ (C.la (C.li + p - 1) = C.li ∧ C.lb (C.lj + q - 1) = C.lj))
    (hF : ∀ p q, p ≤ C.si → q ≤ C.sj → C.OkF fd p q)
    (hb : Dw C.la C.lb C.ren C.li C.lj p q + C.δ ≤ C.t) {tdv : Nat}
    (hT : min (TD C.la C.lb C.ren (C.li + p - 1) (C.lj + q - 1)) C.inf ≤ tdv ∧ tdv ≤ C.inf)
    (heq : rd fd C.w C.t C.inf (C.la (C.li + p - 1) - C.li) (C.lb (C.lj + q - 1) - C.lj) + tdv =
      rd fd C.w C.t C.inf p q) :
    Dw C.la C.lb C.ren C.li C.lj p q = Dw C.la C.lb C.ren C.li C.lj (C.la (C.li + p - 1) - C.li)
      (C.lb (C.lj + q - 1) - C.lj) + TD C.la C.lb C.ren (C.li + p - 1) (C.lj + q - 1) := by
  have hxi : C.li + p - 1 ≤ C.i0 := by
    have hlile : C.li ≤ C.i0 := by have := (hG.wa.1 C.i0 hG.i0a).2; rw [← hG.li_eq] at this; exact this
    have hps2 : p ≤ C.i0 - C.li + 1 := hps
    omega
  have hyj : C.lj + q - 1 ≤ C.j0 := by
    have hljle : C.lj ≤ C.j0 := by have := (hG.wb.1 C.j0 hG.j0a).2; rw [← hG.lj_eq] at this; exact this
    have hqs2 : q ≤ C.j0 - C.lj + 1 := hqs
    omega
  have hcA := closed_win C hG hxi
  have hcB := closed_winB C hG hyj
  have hle := Dw_le_nonleaf (ren := C.ren) hG.wa hG.wb hli hlj hp hq hcA hcB hn
  have hlx1 := hcA (C.li + p - 1) (by omega) (Nat.le_refl _)
  have hly1 := hcB (C.lj + q - 1) (by omega) (Nat.le_refl _)
  have hlx2 := (hG.wa.1 (C.li + p - 1) (by omega)).2
  have hly2 := (hG.wb.1 (C.lj + q - 1) (by omega)).2
  exact split_sound (hF p q hps hqs) (hF _ _ (by omega) (by omega)) hT hb hle heq

end Ctx
end difffold_lines_extract
