/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitPair
import SubNLogN.Machine.Walsh.PosPermSchedEmitBlockDefs

/-!
# Schedule compiler emitter, the slice loops: programs and contracts (`PosPermSchedEmitLoopDefs.lean`)

The slice part of one stage of the emitter (`StageEmitSpec`, `PosPermSchedState.lean`):
* `rhoBody IT stA` handles one slice `(g, ρ)`. It sets `hi := K - ρ - 1`, scans the positions in
  decreasing order (`xBody`, collecting the batch onto `BT` with its count `cnt`), emits the batch
  if it is nonempty (`emitBatch`), then sets `hi := 0` and `ρ := ρ + 1`. Its contract is
  `RhoBodyStmt`.
* `gBody IT stA` handles group `g`: the group setup (`gSetup`), then the `K` slices, then the
  clears and `g := g + 1`.
* `gLoop IT stA` runs all `numGroups m K d` groups. Its contract is `GLoopStmt`.

All are stated on the emitter states `st S₀ v acc bt` (`PosPermSchedEmitSt.lean`).

**Scope (honest summary).** Definitions and two contracts, no proofs here (except closedness).
`RhoBodyStmt` is proved as `rhoBody_holds` and `GLoopStmt` as `gLoop_holds`
(`PosPermSchedEmitAll.lean`; via `rhoBody_of` in `PosPermSchedEmitRho.lean` and `gLoop_of` in
`PosPermSchedEmitGLoop.lean`).
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh

/-- One slice `(g, ρ)`. -/
def rhoBody (IT : RawN) (stA : Bool) : SProg Stk :=
  .seq (subR .K .rho .hi) (.seq (dec .hi) (.seq (copyR .m .x) (.seq (loopR .x (xBody IT stA))
    (.seq (ifR .cnt emitBatch skip) (.seq (clr .hi) (inc .rho))))))

/-- One group `g`: setup, the `K` slices (counter `rc`, `ρ` counts up), clears, `g := g + 1`. -/
def gBody (IT : RawN) (stA : Bool) : SProg Stk :=
  .seq gSetup (.seq (copyR .K .rc) (.seq (loopR .rc (rhoBody IT stA)) (.seq (clr .rho)
    (.seq (clr .j0) (.seq (clr .D) (.seq (clr .DK) (.seq (clr .q4) (.seq (clr .nS)
    (inc .g)))))))))

/-- All groups (counter `gc`, `g` counts up). -/
def gLoop (IT : RawN) (stA : Bool) : SProg Stk :=
  .seq (copyR .G .gc) (.seq (loopR .gc (gBody IT stA)) (clr .g))

/-- The slice-level registers (and the per-position ones), cleared. -/
def rz (w : RegN → ℕ) : RegN → ℕ := fun r =>
  match r with
  | .hi | .cnt | .x | .y | .f | .c | .t | .e0 | .e1 | .q7 | .q8 | .v | .fnd | .b => 0
  | r => w r

/-- The pairs of a stage (`stage_eq`: `stageA I` or `stageB I`). -/
def stPairs {m : ℕ} (stA : Bool) (I : Fin m → Fin m) : List (Fin m × Fin m) :=
  (List.finRange m).filterMap (pairOf stA I)

/-- **[CONTRACT, proved: `rhoBody_holds`, `PosPermSchedEmitAll.lean`] One slice `(g, ρ)`**
(Theorem 5.8 (`thm:positional-perm`); `sliceCmds`, `PosPermLeaf.lean`).
* Setting: the table `IT` holds `utab (finVals I)`; `U`, `B1` and `BT` are empty. The registers
  hold `rz w` with `ρ` in `rho`, where `w` carries `m`, `K`, `j₀ = groupStart K d g`,
  `D = groupSize m K d g`, `E = j₀ + D K` (`q4`) and `nS = m - j₀ - D K`.
* Effect: the accumulator gains `(schedSyms (sliceCmds m d K g ρ stagePairs)).reverse`, and `ρ`
  becomes `ρ + 1`. Nothing else changes.
* Cost `(m + 2)·50·opW V` for any `V ≥ 1` bounding the values and `|BT| ≤ (m+1)(2m+2)`. -/
def RhoBodyStmt : Prop :=
  ∀ (S₀ : Stk → List Sym) (IT : RawN), (IT = .I0T ∨ IT = .I1T) →
    ∀ (m d K g : ℕ) (I : Fin m → Fin m) (stA : Bool) (w : RegN → ℕ) (acc : List Sym)
      (V ρ : ℕ) (hρ : ρ < K),
      S₀ (rs IT) = utab (finVals I) → S₀ (rs .U) = [] → S₀ (rs .B1) = [] →
      w .m = m → w .K = K → w .j0 = groupStart K d g → w .D = groupSize m K d g →
      w .q4 = groupStart K d g + groupSize m K d g * K →
      w .nS = m - groupStart K d g - groupSize m K d g * K →
      1 ≤ V → m ≤ V → K ≤ V → (utab (finVals I)).length ≤ V → w .j0 ≤ V → w .q4 ≤ V →
      w .D ≤ V → w .nS ≤ V → (m + 1) * (2 * m + 2) ≤ V →
      Runs (rhoBody IT stA) (st S₀ (Function.update (rz w) .rho ρ) acc [])
        (st S₀ (Function.update (rz w) .rho (ρ + 1))
          ((schedSyms (sliceCmds m d K g ⟨ρ, hρ⟩ (stPairs stA I))).reverse ++ acc) [])
        (fun _ => True) ((m + 2) * (50 * opW V))

/-- **[CONTRACT, proved: `gLoop_holds`, `PosPermSchedEmitAll.lean`] All groups of a stage**
(Theorem 5.8 (`thm:positional-perm`); the slice part of `stageCmds`).
* Setting: the table `IT` holds `utab (finVals I)`; `U`, `B1` and `BT` are empty. The registers hold
  `v`: `m, d, K` (with `d, K ≥ 1`), `J = numChunks m K`, `G = numGroups m K d`, any `JK`, and `0` in
  every other register.
* Effect: the accumulator gains `(schedSyms Lslices).reverse`, where `Lslices` is the slice part of
  `stageCmds m d K stagePairs` (groups `g < G`, then offsets `ρ < K`). Nothing else changes.
* Cost `(m + d + K + 2)^3·100·opW V` for any `V` with `2 (m + d + K + 1)^3 ≤ V` and the table
  length `≤ V`. -/
def GLoopStmt : Prop :=
  ∀ (S₀ : Stk → List Sym) (IT : RawN), (IT = .I0T ∨ IT = .I1T) →
    ∀ (m d K : ℕ) (I : Fin m → Fin m) (stA : Bool) (v : RegN → ℕ) (acc : List Sym) (V : ℕ),
      S₀ (rs IT) = utab (finVals I) → S₀ (rs .U) = [] → S₀ (rs .B1) = [] →
      1 ≤ d → 1 ≤ K → v .m = m → v .d = d → v .K = K → v .J = numChunks m K →
      v .G = numGroups m K d →
      (∀ q : RegN, q ≠ .m → q ≠ .d → q ≠ .K → q ≠ .J → q ≠ .G → q ≠ .JK → v q = 0) →
      2 * (m + d + K + 1) ^ 3 ≤ V → (utab (finVals I)).length ≤ V →
      Runs (gLoop IT stA) (st S₀ v acc [])
        (st S₀ v ((schedSyms ((List.range (numGroups m K d)).flatMap fun g =>
          (List.finRange K).flatMap fun ρ => sliceCmds m d K g ρ (stPairs stA I))).reverse ++ acc)
          [])
        (fun _ => True) ((m + d + K + 2) ^ 3 * (100 * opW V))

theorem closed_gLoop (IT : RawN) (stA : Bool) : (gLoop IT stA).Closed := by
  cases stA <;>
  simp [gLoop, gBody, rhoBody, xBody, pairBody, pairBranch, sliceTest, emitPairB, clrPair,
    emitBatch, gSetup, ctSet, copyR, ltR, eqR, subR, mulR, dmR, lookR, emitA, emitB, pushA, clr,
    inc, dec, ifR, loopR, xferBT, copyU, ltF, eqF, subU, mulU, divmodU, lookup, PSIO.emitField,
    PSIO.halveStep, PSIO.halveBody, PSIO.moveAll, clearU, incR, decR, ifNE, forDown, whileNE, whileTop,
    moveU, mv, skipEntry, moveToks, copyToks, drainTo, popR, pushR, peekR, pushC, skip,
    Prog.Closed, Prog.FreeBelow]

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
