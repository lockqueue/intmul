/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitSt

/-!
# Schedule compiler emitter, two straight-line blocks: programs and contracts
(`PosPermSchedEmitBlockDefs.lean`)

Two blocks of the stage emitter (`StageEmitSpec`, `PosPermSchedState.lean`), stated on the emitter
states `st S₀ v acc bt` (`PosPermSchedEmitSt.lean`):
* `emitBatch` pushes the batch command of a slice onto the accumulator: `tag 0`, then the fields
  `ρ, nS, D, j₀`, then `sep2`, then the pair block (moved from the batch buffer), then the count,
  then `sep2`. Its contract is `EmitBatchStmt`.
* `gSetup` computes the per-group registers `j₀ = g d K`, `D = min d (J - g d)`, `DK = D K`,
  `E = j₀ + DK` (register `q4`) and `nS = m - j₀ - DK`. Its contract is `GSetupStmt`.

**Scope (honest summary).** Definitions and two contracts, no proofs here (except closedness). Both
are proved as `emitBatch_holds` and `gSetup_holds` (`PosPermSchedEmitBlk.lean`).
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- **Batch command emission** (the accumulator gains `(cmdSyms (batch j₀ D nS ρ ps)).reverse` when
`BT = hdrSyms (pairFields ps)` and `cnt = |ps|`; `batch_acc`). -/
def emitBatch : SProg Stk :=
  .seq (pushA (Sym.tag 0)) (.seq (copyR .rho .b) (.seq (emitA .b) (.seq (copyR .nS .b)
    (.seq (emitA .b) (.seq (copyR .D .b) (.seq (emitA .b) (.seq (copyR .j0 .b) (.seq (emitA .b)
    (.seq (pushA Sym.sep2) (.seq xferBT (.seq (emitA .cnt) (pushA Sym.sep2))))))))))))

/-- **[CONTRACT, proved: `emitBatch_holds`, `PosPermSchedEmitBlk.lean`] Batch command emission.**
From any state with `b = 0`, the accumulator gains
`sep2, cnt, mark, BT, sep2, j₀, mark, D, mark, nS, mark, ρ, mark, tag 0` (top first; numbers as
`natSyms`). The batch buffer is emptied, `cnt` is set to `0`, and nothing else changes. The
scratch raw stacks `U`, `B1` are empty. Cost `20·opW V` for any `V ≥ 1` bounding the values
emitted and `|BT|`. -/
def EmitBatchStmt : Prop :=
  ∀ (S₀ : Stk → List Sym) (v : RegN → ℕ) (acc bt : List Sym) (V : ℕ),
    S₀ (rs .U) = [] → S₀ (rs .B1) = [] → v .b = 0 →
    1 ≤ V → v .rho ≤ V → v .nS ≤ V → v .D ≤ V → v .j0 ≤ V → v .cnt ≤ V → bt.length ≤ V →
    Runs emitBatch (st S₀ v acc bt)
      (st S₀ (Function.update v .cnt 0)
        (Sym.sep2 :: (natSyms (v .cnt) ++ Sym.mark :: (bt ++ Sym.sep2 :: (natSyms (v .j0) ++
          Sym.mark :: (natSyms (v .D) ++ Sym.mark :: (natSyms (v .nS) ++ Sym.mark ::
            (natSyms (v .rho) ++ Sym.mark :: Sym.tag 0 :: acc))))))) [])
      (fun _ => True) (20 * opW V)

/-- **Per-group setup**: `q2 := g d`, `j₀ := q2 K`, `q3 := J - q2`, `D := min d q3` (via
`f := [d < q3]`), clear `f, q3, q2`, `DK := D K`, `E := j₀ + DK` (in `q4`), `q5 := m - j₀`,
`nS := q5 - DK`, clear `q5`. -/
def gSetup : SProg Stk :=
  .seq (mulR .g .d .q2) (.seq (mulR .q2 .K .j0) (.seq (subR .J .q2 .q3) (.seq (ltR .d .q3 .f)
    (.seq (ifR .f (copyR .d .D) (copyR .q3 .D)) (.seq (clr .f) (.seq (clr .q3) (.seq (clr .q2)
    (.seq (mulR .D .K .DK) (.seq (copyR .j0 .q4) (.seq (copyR .DK .q4) (.seq (subR .m .j0 .q5)
    (.seq (subR .q5 .DK .nS) (clr .q5)))))))))))))

/-- The per-group values (`groupStart`, `groupSize` of `Math/Walsh/Cube.lean` with `J = v .J`). -/
def gVals (v : RegN → ℕ) : RegN → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update v
    .j0 (v .g * v .d * v .K)) .D (min (v .d) (v .J - v .g * v .d)))
    .DK (min (v .d) (v .J - v .g * v .d) * v .K))
    .q4 (v .g * v .d * v .K + min (v .d) (v .J - v .g * v .d) * v .K))
    .nS (v .m - v .g * v .d * v .K - min (v .d) (v .J - v .g * v .d) * v .K)

/-- **[CONTRACT, proved: `gSetup_holds`, `PosPermSchedEmitBlk.lean`] Per-group setup.** From a
state where the registers it writes (`q2 q3 q5 f
j0 D DK q4 nS`) are `0`, `gSetup` sets `j0 D DK q4 nS` to `gVals` and restores everything else.
Here `d, K ≥ 1`. Cost `30·opW V` for any `V ≥ 1` with `m, d, K, J, g ≤ V` and
`g d K + d K ≤ V`. -/
def GSetupStmt : Prop :=
  ∀ (S₀ : Stk → List Sym) (v : RegN → ℕ) (acc : List Sym) (V : ℕ),
    v .q2 = 0 → v .q3 = 0 → v .q5 = 0 → v .f = 0 → v .j0 = 0 → v .D = 0 → v .DK = 0 →
    v .q4 = 0 → v .nS = 0 → 1 ≤ v .d → 1 ≤ v .K →
    1 ≤ V → v .m ≤ V → v .d ≤ V → v .K ≤ V → v .J ≤ V → v .g ≤ V →
    v .g * v .d * v .K + v .d * v .K ≤ V →
    Runs gSetup (st S₀ v acc []) (st S₀ (gVals v) acc []) (fun _ => True) (30 * opW V)

theorem closed_emitBatch : emitBatch.Closed := by
  simp [emitBatch, copyR, emitA, pushA, xferBT, copyU, PSIO.emitField, PSIO.halveStep, PSIO.halveBody,
    PSIO.moveAll, clearU, incR, forDown, whileNE, whileTop, moveU, mv, popR, pushR, peekR, pushC,
    Prog.Closed, Prog.FreeBelow]

theorem closed_gSetup : gSetup.Closed := by
  simp [gSetup, mulR, subR, ltR, ifR, copyR, clr, mulU, subU, ltF, copyU, ifNE, clearU, incR,
    forDown, whileNE, whileTop, moveU, mv, popR, pushR, peekR, pushC, skip, Prog.Closed,
    Prog.FreeBelow]

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
