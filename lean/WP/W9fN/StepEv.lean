import WP.W9fN.SL
import Contracts.W6

/-!
# WP.W9fN.StepEv — the recurrence step blocks and their values

Adapted from `WP.W9f.Blocks` to `WP.W9fN.SL`: `Prm` comes from
`SL.lean` (with `SS = 2^(q+2)` and `HALF`), shifts read `natAbs`, and `pRec` multiplies by `SS`.

| block | computes | equality |
|---|---|---|
| `pDivRB out` | `out := divRoundBarrett H μ T5 a` (indicator form `divRBI`) | `divRBI_eq` (`0 < a`) |
| `pRec y z out` | one coordinate of `recStepBarrett` | `ev_pRec_out`, `ev_pRec_eq` |
| `pStepP`, `pStepH` | zPart / zHom step (`recStepBarrett`, both coordinates) | `ev_pStepP`, `ev_pStepH` |
| `pStepF` | zPart then zHom | `ev_pStepF` |
| `pStepN` | zPart step and Nyquist sum `B := Z − B` | `ev_pStepN` |
-/

namespace WP.W9fN

open IntMul IntMulTM.Contracts

/-! ## Barrett rounding in indicator form -/

/-- Barrett estimate `⌊x·μ / 2^H⌋`. -/
def qhOf (H : ℕ) (μ x : ℤ) : ℤ := (x * μ) >>> H

/-- Barrett quotient after the one-step correction, written with indicators. -/
def qOf (H : ℕ) (μ x d : ℤ) : ℤ :=
  qhOf H μ x - (1 - (if 0 ≤ x - qhOf H μ x * d then 1 else 0)) +
    (if d ≤ x - qhOf H μ x * d then 1 else 0)

/-- Indicator form of `W8.divRoundBarrett`: quotient plus `[d ≤ 2r]`. -/
def divRBI (H : ℕ) (μ x d : ℤ) : ℤ :=
  qOf H μ x d + (if d ≤ (x - qOf H μ x d * d) + (x - qOf H μ x d * d) then 1 else 0)

theorem barrettEuclid_eq (H : ℕ) (μ x d : ℤ) (hd : 0 < d) :
    W8.barrettEuclid H μ x d = (qOf H μ x d, x - qOf H μ x d * d) := by
  unfold W8.barrettEuclid qOf
  change (let qh := qhOf H μ x; let rh := x - qh * d;
    if rh < 0 then (qh - 1, rh + d) else if d ≤ rh then (qh + 1, rh - d) else (qh, rh)) = _
  generalize qhOf H μ x = qh
  dsimp only
  by_cases h1 : x - qh * d < 0
  · have h2 : ¬ (0 ≤ x - qh * d) := by omega
    have h3 : ¬ (d ≤ x - qh * d) := by omega
    simp only [if_pos h1, if_neg h2, if_neg h3]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
  · have h2 : 0 ≤ x - qh * d := by omega
    simp only [if_neg h1, if_pos h2]
    by_cases h3 : d ≤ x - qh * d
    · simp only [if_pos h3]
      refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
    · simp only [if_neg h3]
      refine Prod.ext ?_ ?_ <;> dsimp only <;> ring

/-- **The indicator form is W8's reciprocal rounding** (for a positive divisor). -/
theorem divRBI_eq (H : ℕ) (μ x d : ℤ) (hd : 0 < d) :
    divRBI H μ x d = W8.divRoundBarrett H μ x d := by
  unfold W8.divRoundBarrett
  rw [barrettEuclid_eq H μ x d hd]
  unfold divRBI
  dsimp only
  split_ifs <;> omega

/-! ## One coordinate of a recurrence step -/

/-- `out := divRoundBarrett H μ T5 a`: dividend `T5`, divisor `DA`, reciprocal `MU`, shift `HV`.
Temporaries `T1 … T4`. -/
def pDivRB (out : V) : SL :=
  block (op .T1 .mul .T5 .MU)
   [op .T1 .sar .T1 .HV, op .T2 .mul .T1 .DA, op .T2 .sub .T5 .T2,
    op .T3 .le .ZERO .T2, op .T3 .sub .ONE .T3, op .T4 .le .DA .T2,
    op .T1 .sub .T1 .T3, op .T1 .add .T1 .T4,
    op .T2 .mul .T1 .DA, op .T2 .sub .T5 .T2, op .T2 .add .T2 .T2,
    op .T3 .le .DA .T2, op out .add .T1 .T3]

/-- One coordinate of a reciprocal recurrence step:
`out := divRoundBarrett H μ (y·2^(q+2) − c·z) a` (multiplier `MC`, `SS = 2^(q+2)`). -/
def pRec (y z out : V) : SL :=
  block (op .T5 .mul y .SS) [op .T6 .mul .MC z, op .T5 .sub .T5 .T6, pDivRB out]

theorem writes_pRec (y z out : V) : writes (pRec y z out) =
    [.T5, .T6, .T5, .T1, .T1, .T2, .T2, .T3, .T3, .T4, .T1, .T1, .T2, .T2, .T2, .T3, out] := rfl

theorem ev_pRec_out (y z out : V) (hz : z ≠ .T5) (env : V → ℤ) (h0 : env .ZERO = 0)
    (h1 : env .ONE = 1) :
    ev (pRec y z out) env out =
      divRBI (env .HV).natAbs (env .MU) (env y * env .SS - env .MC * env z) (env .DA) := by
  simp only [pRec, pDivRB, ev_block_cons, ev_block_nil, ev_op, Function.update_self,
    Function.update_apply, if_neg hz, reduceCtorEq, if_false, h0, h1, sem_add, sem_sub, sem_mul,
    sem_sar, sem_le]
  unfold divRBI qOf qhOf
  rfl

/-- Variables that no step block writes. -/
def Kept (v : V) : Prop :=
  v ≠ .T1 ∧ v ≠ .T2 ∧ v ≠ .T3 ∧ v ≠ .T4 ∧ v ≠ .T5 ∧ v ≠ .T6

theorem ev_pRec_frame (y z out : V) (env : V → ℤ) (v : V) (hv : v ≠ out) (h : Kept v) :
    ev (pRec y z out) env v = env v := by
  refine ev_of_not_mem _ env v ?_
  rw [writes_pRec]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h5, h6, h5, h1, h1, h2, h2, h3, h3, h4, h1, h1, h2, h2, h2, h3, hv⟩

/-- The coordinate block computes W8's reciprocal step coordinate. -/
theorem ev_pRec_eq (y z out : V) (hz : z ≠ .T5) (env : V → ℤ) {q H : ℕ} {μ a c : ℤ}
    (hp : Prm env q H μ a c) (ha : 0 < a) :
    ev (pRec y z out) env out =
      W8.divRoundBarrett H μ (env y * ((2 ^ (q + 2) : ℕ) : ℤ) - c * env z) a := by
  rw [ev_pRec_out y z out hz env hp.zero hp.one, hp.hv, hp.mu, hp.da, hp.mc, hp.ss,
    Int.natAbs_natCast, divRBI_eq _ _ _ _ ha]

/-! ## Recurrence steps -/

/-- zPart step, both coordinates (Fwd, Bwd and Nyquist columns). -/
def pStepP : SL := block (pRec .Y1 .Z1 .Z1) [pRec .Y2 .Z2 .Z2]

/-- zHom step, both coordinates (input `0`). -/
def pStepH : SL := block (pRec .ZERO .G1 .G1) [pRec .ZERO .G2 .G2]

/-- Fwd/Bwd step: zPart then zHom. -/
def pStepF : SL := .seq pStepP pStepH

/-- Nyquist step: zPart, then the alternating sum `B := Z − B`. -/
def pStepN : SL := block pStepP [op .B1 .sub .Z1 .B1, op .B2 .sub .Z2 .B2]

/-- The parameter variables are kept by every step block. -/
theorem kept_of_prmVar {v : V} (hv : PrmVar v) : Kept v := by
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem ne_of_prmVar {v w : V} (hv : PrmVar v) (hw : ¬ PrmVar w) : v ≠ w := by
  rintro rfl
  exact hw hv

theorem ev_pStepP (env : V → ℤ) {q H : ℕ} {μ a c : ℤ} (hp : Prm env q H μ a c) (ha : 0 < a) :
    (ev pStepP env .Z1, ev pStepP env .Z2) =
      W8.recStepBarrett q H μ a c (env .Y1, env .Y2) (env .Z1, env .Z2) ∧
    ∀ v, Kept v → v ≠ .Z1 → v ≠ .Z2 → ev pStepP env v = env v := by
  set env1 := ev (pRec .Y1 .Z1 .Z1) env with henv1
  have f1 : ∀ v, Kept v → v ≠ .Z1 → env1 v = env v := fun v hk h1 =>
    ev_pRec_frame _ _ _ env v h1 hk
  have hp1 : Prm env1 q H μ a c := hp.of_eq (fun v hv =>
    f1 v (kept_of_prmVar hv) (ne_of_prmVar hv (by simp [PrmVar])))
  have e2 : ev pStepP env = ev (pRec .Y2 .Z2 .Z2) env1 := rfl
  refine ⟨?_, ?_⟩
  · rw [e2, ev_pRec_frame _ _ _ env1 .Z1 (by decide) (by unfold Kept; decide),
      ev_pRec_eq .Y2 .Z2 .Z2 (by decide) env1 hp1 ha, henv1,
      ev_pRec_eq .Y1 .Z1 .Z1 (by decide) env hp ha]
    rw [ev_pRec_frame _ _ _ env .Y2 (by decide) (by unfold Kept; decide),
      ev_pRec_frame _ _ _ env .Z2 (by decide) (by unfold Kept; decide)]
    rfl
  · intro v hk h1 h2
    rw [e2, ev_pRec_frame _ _ _ env1 v h2 hk, f1 v hk h1]

theorem ev_pStepH (env : V → ℤ) {q H : ℕ} {μ a c : ℤ} (hp : Prm env q H μ a c) (ha : 0 < a) :
    (ev pStepH env .G1, ev pStepH env .G2) =
      W8.recStepBarrett q H μ a c (0, 0) (env .G1, env .G2) ∧
    ∀ v, Kept v → v ≠ .G1 → v ≠ .G2 → ev pStepH env v = env v := by
  set env1 := ev (pRec .ZERO .G1 .G1) env with henv1
  have f1 : ∀ v, Kept v → v ≠ .G1 → env1 v = env v := fun v hk h1 =>
    ev_pRec_frame _ _ _ env v h1 hk
  have hp1 : Prm env1 q H μ a c := hp.of_eq (fun v hv =>
    f1 v (kept_of_prmVar hv) (ne_of_prmVar hv (by simp [PrmVar])))
  have e2 : ev pStepH env = ev (pRec .ZERO .G2 .G2) env1 := rfl
  refine ⟨?_, ?_⟩
  · rw [e2, ev_pRec_frame _ _ _ env1 .G1 (by decide) (by unfold Kept; decide),
      ev_pRec_eq .ZERO .G2 .G2 (by decide) env1 hp1 ha, henv1,
      ev_pRec_eq .ZERO .G1 .G1 (by decide) env hp ha]
    rw [ev_pRec_frame _ _ _ env .ZERO (by decide) (by unfold Kept; decide),
      ev_pRec_frame _ _ _ env .G2 (by decide) (by unfold Kept; decide), hp.zero]
    rfl
  · intro v hk h1 h2
    rw [e2, ev_pRec_frame _ _ _ env1 v h2 hk, f1 v hk h1]

/-- The Fwd/Bwd step: zPart and zHom advance by one reciprocal step each. -/
theorem ev_pStepF (env : V → ℤ) {q H : ℕ} {μ a c : ℤ} (hp : Prm env q H μ a c) (ha : 0 < a) :
    (ev pStepF env .Z1, ev pStepF env .Z2) =
      W8.recStepBarrett q H μ a c (env .Y1, env .Y2) (env .Z1, env .Z2) ∧
    (ev pStepF env .G1, ev pStepF env .G2) =
      W8.recStepBarrett q H μ a c (0, 0) (env .G1, env .G2) ∧
    ∀ v, Kept v → v ≠ .Z1 → v ≠ .Z2 → v ≠ .G1 → v ≠ .G2 → ev pStepF env v = env v := by
  obtain ⟨hP, fP⟩ := ev_pStepP env hp ha
  set env1 := ev pStepP env with henv1
  have hp1 : Prm env1 q H μ a c := hp.of_eq (fun v hv =>
    fP v (kept_of_prmVar hv) (ne_of_prmVar hv (by simp [PrmVar]))
      (ne_of_prmVar hv (by simp [PrmVar])))
  obtain ⟨hH, fH⟩ := ev_pStepH env1 hp1 ha
  have e : ev pStepF env = ev pStepH env1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, fH .Z1 (by unfold Kept; decide) (by decide) (by decide),
      fH .Z2 (by unfold Kept; decide) (by decide) (by decide)]
    exact hP
  · rw [e, hH, fP .G1 (by unfold Kept; decide) (by decide) (by decide),
      fP .G2 (by unfold Kept; decide) (by decide) (by decide)]
  · intro v hk h1 h2 h3 h4
    rw [e, fH v hk h3 h4, fP v hk h1 h2]

/-- The Nyquist step: zPart advances, then `B := Z_new − B`. -/
theorem ev_pStepN (env : V → ℤ) {q H : ℕ} {μ a : ℤ} (hp : Prm env q H μ a a) (ha : 0 < a) :
    (ev pStepN env .Z1, ev pStepN env .Z2) =
      W8.recStepBarrett q H μ a a (env .Y1, env .Y2) (env .Z1, env .Z2) ∧
    (ev pStepN env .B1, ev pStepN env .B2) =
      (ev pStepN env .Z1 - env .B1, ev pStepN env .Z2 - env .B2) ∧
    ∀ v, Kept v → v ≠ .Z1 → v ≠ .Z2 → v ≠ .B1 → v ≠ .B2 → ev pStepN env v = env v := by
  obtain ⟨hP, fP⟩ := ev_pStepP env hp ha
  have e : ∀ v, ev pStepN env v = Function.update (Function.update (ev pStepP env) .B1
      (ev pStepP env .Z1 - ev pStepP env .B1)) .B2
      (Function.update (ev pStepP env) .B1 (ev pStepP env .Z1 - ev pStepP env .B1) .Z2 -
        Function.update (ev pStepP env) .B1 (ev pStepP env .Z1 - ev pStepP env .B1) .B2) v :=
    fun v => rfl
  have fB1 : ev pStepP env .B1 = env .B1 := fP .B1 (by unfold Kept; decide) (by decide) (by decide)
  have fB2 : ev pStepP env .B2 = env .B2 := fP .B2 (by unfold Kept; decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [e, e]
    simp only [Function.update_apply, reduceCtorEq, if_false]
    exact hP
  · rw [e, e, e, e]
    simp only [Function.update_apply, reduceCtorEq, if_false, if_true, fB1, fB2]
  · intro v hk h1 h2 h3 h4
    rw [e]
    simp only [Function.update_apply, if_neg h3, if_neg h4]
    exact fP v hk h1 h2

#assert_std_axioms barrettEuclid_eq divRBI_eq writes_pRec ev_pRec_out ev_pRec_frame ev_pRec_eq
  kept_of_prmVar ev_pStepP ev_pStepH ev_pStepF ev_pStepN

end WP.W9fN
