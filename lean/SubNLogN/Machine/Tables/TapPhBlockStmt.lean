/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapPhaseStmt

/-!
# K6 (`Machine/Tables/TapPhBlockStmt.lean`): one tap block — statement only

**Scope (honest summary).** Defines the per-axis cost `tapAxisCost` (the axis-`i` summands of
`tapPart` and `tapTabLen`) and the interface statement `TapBlockStmt` (the inner loop of the tap
phase, proved from `TapRecStmt`, `TapBlockRankStmt` and the rank fragment
`HT.rankProg_spec` of `TapPhRank.lean`). It is consumed by the tap-phase driver (`TapPh.lean`)
as an explicit hypothesis. Nothing is proved here.

`TapBlockStmt` asks for **one** host program `blk` (uniform in all runtime data) that, at axis `i`
of a bridge header `b`, pushes `carrSyms wT (tapBlock t P (tabOf ω P t) i) ++ [mark]` onto `tapTab`
(the block's records last first, then preceded on the stack by its `mark`), reading the parameter
roles of `TapRecStmt` and the axis data `rT = t_i`, `rA = A_i = prefixProd t i`,
`rDen = 2·t_i·A_i`, `rI = i`, `rSH = hdrSyms (lowerShape t i)`; `ru`, `ra` and the temporaries
`.inr 40 … .inr 60` are empty before (and, since the final state is exact, after); every other
stack is restored. Cost `K (C+1)(KM+1)·tapAxisCost b i`.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common

/-- The axis-`i` summands of `tapPart b` and `tapTabLen b`. -/
def tapAxisCost (b : BrPar) (i : Fin b.d) : ℕ :=
  prefixProd b.t i * ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i) +
    (prefixProd b.t i * ((tapOffsets b.t b.P i).length * (2 * b.wT) + 1) + 1)

/-- **[INTERFACE] One tap block** (`TapBlockStmt`). See the module docstring. -/
def TapBlockStmt : Prop :=
  ∃ K : ℕ, ∀ (I : TB) (Mul : ℕ → ℕ) (C KM : ℕ), I.Spec Mul C → (∀ w, Mul w ≤ KM * (w + 1) ^ 2) →
    ∃ blk : TP I, blk.Closed ∧
      ∀ (b : BrPar) (i : Fin b.d) (B : TL → List Sym),
        ShapeOK b.t → 1 ≤ b.ω → 1 ≤ b.wT →
        CArrFits b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) i) →
        B rP = natSyms b.P → B rW = natSyms b.ω → B rB = natSyms (tapPrec b.P) →
        B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1 →
        B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1 →
        B rPW = intSyms ((2 ^ b.wT : ℕ) : ℤ) → B rPW1 = intSyms ((2 ^ (b.wT + 1) : ℕ) : ℤ) →
        B rT = natSyms (b.t i) → B rA = natSyms (prefixProd b.t i) →
        B rDen = natSyms (2 * b.t i * prefixProd b.t i) → B rI = natSyms (i : ℕ) →
        B rSH = hdrSyms (lowerShape b.t i) → B ru = [] → B ra = [] →
        (∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) →
        HT [] B blk
          (Function.update B sTap
            (carrSyms b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) i) ++ Sym.mark :: B sTap))
          (K * (C + 1) * (KM + 1) * tapAxisCost b i)

end SubNLogN.Machine.Tables
