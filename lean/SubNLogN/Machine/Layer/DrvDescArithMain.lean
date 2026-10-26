/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescArithCost

/-!
# Layer driver pre-phase: the value kernel, assembly (`Machine/Layer/DrvDescArithMain.lean`)

**Scope (honest summary).** Proves `DrvDescArithStmt` (`Machine/Layer/DrvDescDefs.lean:48`) as
`SubNLogN.Machine.Layer.drvDescArith_holds`, with exponent `J = 3`; nothing is assumed (no
hypotheses, no `sorry`). The kernel `mainProg` (registers `DrvArith.Reg2`, private stacks
`Fin 80`):
1. `preProg`: copy the first eight header fields from stack `0` (restored) and floor them,
   `ρ = (ρ+1) − 1`, `q₀ = q0Of d` (`DrvArith.q0N`);
2. `branchProg`: compare `q₀` with `D`; rows case `q₀ < D`: `e = D − q₀`, `R = padR d K` (`DrvArith.padRN`
   from `DrvArith.lean`), `a = A·R`; otherwise `e = R = a = 0` (then `2^{q₀K}` is never computed);
3. `postProg`: push `hdrSyms [P, d, r, a, R, K, e, S, ρ]` on stack `1`, drop all floors.
The record pushed is `hdrSyms (drvDescVals t)` in both cases. Cost
`(c₀ + c_P + 1000·(B + L + 2))·(|hdr| + D·K + 1)^3` (constants of `Machine/Layer/DrvDescArithCost.lean`).
Paper: the rows/pieces parameters of Section A.6 (`sec:transfer-layer`), Proposition A.11 (`q₀`
written `d₀`, `k₀`, row field `2^{q₀K}` padded to a multiple of `W_c^{k₀}`, `D − q₀` remaining chunks);
Lean definitions `Math/Networks/AppCLayerProc.lean:92-99` (`q0Of`, `k0Of`, `padR`).
-/

namespace SubNLogN.Machine.Layer.DrvDescArithAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith (fl fl_self fl_ne q0Cost padRCost Reg2 lN)
open SubNLogN.Math.Networks (q0Of padR)

/-! ## 1. The program -/

/-- The pre-part: parse, `ρ`, `q₀`. -/
noncomputable def preProg : Prog AK (fun _ => Sym) Reg := .seq pre1Prog q0Prog

theorem closed_preProg : preProg.Closed := WP.W9comp.closed_seq closed_pre1Prog closed_q0Prog

/-- The post-part: emit the value record, drop the floors. -/
def postProg : Prog AK (fun _ => Sym) Reg := .seq emitsProg dropsProg

theorem closed_postProg : postProg.Closed :=
  WP.W9comp.closed_seq closed_emitsProg closed_dropsProg

/-- **The value kernel.** -/
noncomputable def mainProg : Prog AK (fun _ => Sym) Reg2 :=
  .seq (preProg.liftRegs lN) (.seq branchProg (postProg.liftRegs lN))

theorem closed_mainProg : mainProg.Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN closed_preProg)
    (WP.W9comp.closed_seq closed_branchProg (WP.W9comp.closed_liftRegs lN closed_postProg))

/-! ## 2. Runs -/

theorem runs_pre (S0 : AK → List Sym) (P d r D A Sv K ρ w : ℕ) (hrest : List Sym)
    (hS : S0 sH = hdrSyms [P, d, r, D, A, Sv, K, ρ + 1, w] ++ hrest) :
    Runs preProg S0 (preSt S0 P d r D A Sv K (ρ + 1) ρ (q0Of d)) (fun _ => True)
      (pre1Cost P d r D A Sv K (ρ + 1) + (1 + q0Cost d)) :=
  WP.W9comp.runs_seq (runs_pre1 S0 P d r D A Sv K ρ w hrest hS)
    (runs_q0 (fl (parseSt S0 P d r D A Sv K (ρ + 1)) sRo ρ) d (S0 sd)
      (by simp [parseSt, fl_apply]))

/-- **The kernel, rows case** (`q₀ < D`). -/
theorem runs_main_rows (t : LayerRT) (hrest : List Sym) (S0 : AK → List Sym)
    (hS : S0 sH = t.hdr ++ hrest) (h : q0Of t.d < t.D) :
    Runs mainProg S0 (Function.update S0 sO (hdrSyms [t.P, t.d, t.r, t.A * padR t.d t.K,
        padR t.d t.K, t.K, t.D - q0Of t.d, t.S, t.ρ] ++ S0 sO)) (fun _ => True)
      ((pre1Cost t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) + (1 + q0Cost t.d)) +
        ((12 * min (bitLen (q0Of t.d)) (bitLen t.D) + 15 +
            (rowsCost t.D (q0Of t.d) (padRCost t.d t.K) (2 ^ (q0Of t.d * t.K)) t.A
              (padR t.d t.K) + 1)) +
          (emitsCost t.P t.d t.r (t.A * padR t.d t.K) (padR t.d t.K) t.K (t.D - q0Of t.d) t.S
              t.ρ +
            dropsCost t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d) (t.D - q0Of t.d)
              (padR t.d t.K) (t.A * padR t.d t.K)))) := by
  have r1 := runs_lN (runs_pre S0 t.P t.d t.r t.D t.A t.S t.K t.ρ t.w hrest hS)
  have r2 := runs_branch_rows (preSt S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d))
    t.d t.K t.A t.D (q0Of t.d) h (S0 sd) (S0 sK) (S0 sA) (S0 sD) (S0 sq)
    (by simp [preSt, parseSt, fl_apply]) (by simp [preSt, parseSt, fl_apply])
    (by simp [preSt, parseSt, fl_apply]) (by simp [preSt, parseSt, fl_apply])
    (by simp [preSt, parseSt, fl_apply])
  have r3 := runs_emits (postSt S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d)
      (t.D - q0Of t.d) (padR t.d t.K) (t.A * padR t.d t.K))
    t.P t.d t.r (t.A * padR t.d t.K) (padR t.d t.K) t.K (t.D - q0Of t.d) t.S t.ρ
    (S0 sP) (S0 sd) (S0 sr) (S0 sa) (S0 sR) (S0 sK) (S0 se) (S0 sS) (S0 sRo)
    (by simp [postSt, preSt, parseSt, fl_apply]) (by simp [postSt, preSt, parseSt, fl_apply])
    (by simp [postSt, preSt, parseSt, fl_apply]) (by simp [postSt, preSt, parseSt, fl_apply])
    (by simp [postSt, preSt, parseSt, fl_apply]) (by simp [postSt, preSt, parseSt, fl_apply])
    (by simp [postSt, preSt, parseSt, fl_apply]) (by simp [postSt, preSt, parseSt, fl_apply])
    (by simp [postSt, preSt, parseSt, fl_apply]) (S0 sO)
  have r4 := runs_drops S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d) (t.D - q0Of t.d)
    (padR t.d t.K) (t.A * padR t.d t.K)
    (hdrSyms [t.P, t.d, t.r, t.A * padR t.d t.K, padR t.d t.K, t.K, t.D - q0Of t.d, t.S, t.ρ] ++
      S0 sO)
  have eO : Function.update (postSt S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d)
      (t.D - q0Of t.d) (padR t.d t.K) (t.A * padR t.d t.K)) sO (S0 sO) =
      postSt S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d)
      (t.D - q0Of t.d) (padR t.d t.K) (t.A * padR t.d t.K) :=
    Function.update_eq_self_iff.mpr (by simp [postSt, preSt, parseSt, fl_apply])
  rw [eO] at r3
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (runs_lN (WP.W9comp.runs_seq r3 r4)))

/-- **The kernel, other case** (`¬ q₀ < D`). -/
theorem runs_main_norows (t : LayerRT) (hrest : List Sym) (S0 : AK → List Sym)
    (hS : S0 sH = t.hdr ++ hrest) (h : ¬ q0Of t.d < t.D) :
    Runs mainProg S0 (Function.update S0 sO (hdrSyms [t.P, t.d, t.r, 0, 0, t.K, 0, t.S, t.ρ] ++
        S0 sO)) (fun _ => True)
      ((pre1Cost t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) + (1 + q0Cost t.d)) +
        ((12 * min (bitLen (q0Of t.d)) (bitLen t.D) + 15 + (1 + (1 + 1) + 1)) +
          (emitsCost t.P t.d t.r 0 0 t.K 0 t.S t.ρ +
            dropsCost t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d) 0 0 0))) := by
  have r1 := runs_lN (runs_pre S0 t.P t.d t.r t.D t.A t.S t.K t.ρ t.w hrest hS)
  have r2 := runs_branch_norows (preSt S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d))
    t.D (q0Of t.d) h (S0 sD) (S0 sq)
    (by simp [preSt, parseSt, fl_apply]) (by simp [preSt, parseSt, fl_apply])
  have r3 := runs_emits (postSt S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d) 0 0 0)
    t.P t.d t.r 0 0 t.K 0 t.S t.ρ
    (S0 sP) (S0 sd) (S0 sr) (S0 sa) (S0 sR) (S0 sK) (S0 se) (S0 sS) (S0 sRo)
    (by simp [postSt, preSt, parseSt, fl_apply]) (by simp [postSt, preSt, parseSt, fl_apply])
    (by simp [postSt, preSt, parseSt, fl_apply]) (by simp [postSt, preSt, parseSt, fl_apply])
    (by simp [postSt, preSt, parseSt, fl_apply]) (by simp [postSt, preSt, parseSt, fl_apply])
    (by simp [postSt, preSt, parseSt, fl_apply]) (by simp [postSt, preSt, parseSt, fl_apply])
    (by simp [postSt, preSt, parseSt, fl_apply]) (S0 sO)
  have r4 := runs_drops S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d) 0 0 0
    (hdrSyms [t.P, t.d, t.r, 0, 0, t.K, 0, t.S, t.ρ] ++ S0 sO)
  have eO : Function.update (postSt S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d)
      0 0 0) sO (S0 sO) =
      postSt S0 t.P t.d t.r t.D t.A t.S t.K (t.ρ + 1) t.ρ (q0Of t.d) 0 0 0 :=
    Function.update_eq_self_iff.mpr (by simp [postSt, preSt, parseSt, fl_apply])
  rw [eO] at r3
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (runs_lN (WP.W9comp.runs_seq r3 r4)))

end SubNLogN.Machine.Layer.DrvDescArithAux

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Layer.DrvDescArithAux
open SubNLogN.Math.Networks (q0Of padR)

/-- **Descriptor values, proved** (`DrvDescArithStmt`, `Machine/Layer/DrvDescDefs.lean:48`).
The kernel `mainProg` (`Machine/Layer/DrvDescArithMain.lean`) reads the layer header
`hdrSyms [P, d, r, D, A, S, K, ρ+1, w]` from stack `0` (restored, anything below it), pushes
`hdrSyms (drvDescVals t)` on stack `1` (old content kept below), restores every private stack
(arbitrary content at entry), within `(c₀ + c_P + 1000·(B + L + 2))·(|hdr| + D·K + 1)^3` steps
(exponent `J = 3`; `c₀`, `c_P` from `q0Cost_le`, `padRCost_le`, `L = ⌈lg W_c⌉`,
`B = bitLen W_c + 3`). In the rows case `q₀ < D` the value `2^{q₀K}` is computed (inside
`DrvArith.padRN`) and paid by `D·K`; otherwise it is never computed. No hypotheses. Paper:
Section A.6 (`sec:transfer-layer`), Proposition A.11 (`prop:prop14-param`). -/
theorem drvDescArith_holds : DrvDescArithStmt := by
  obtain ⟨c0, h0⟩ := DrvArith.q0Cost_le
  obtain ⟨cP, hP⟩ := DrvArith.padRCost_le
  obtain ⟨B, hB⟩ := bitLen_padR_exists
  obtain ⟨L, hL⟩ := q0Of_le_exists
  refine ⟨3, c0 + cP + 1000 * (B + L + 2), fun _ => ⟨Fin 80, inferInstance, inferInstance,
    DrvArith.Reg2, mainProg, inferInstance, inferInstance, closed_mainProg, ?_⟩⟩
  intro t hrest S hS
  unfold drvDescVals
  by_cases h : q0Of t.d < t.D
  · rw [if_pos h]
    exact WP.W9comp.runs_mono (runs_main_rows t hrest S hS h) (fun _ _ => trivial)
      (cost_rows_gen t.P t.d t.r t.D t.A t.S t.K t.ρ t.w (q0Of t.d) (padR t.d t.K)
        (2 ^ (q0Of t.d * t.K)) (DrvArith.q0Cost t.d) (DrvArith.padRCost t.d t.K) c0 cP B L h
        (hB t.d t.K) (DrvArith.BoundsAux.bl_two_pow_le _) (h0 t.d) (hP t.d t.K))
  · rw [if_neg h]
    exact WP.W9comp.runs_mono (runs_main_norows t hrest S hS h) (fun _ _ => trivial)
      (cost_norows_gen t.P t.d t.r t.D t.A t.S t.K t.ρ t.w (q0Of t.d) (DrvArith.q0Cost t.d)
        c0 cP B L (hL t.d) (h0 t.d))

end SubNLogN.Machine.Layer
