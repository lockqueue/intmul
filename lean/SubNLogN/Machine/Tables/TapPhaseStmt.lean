/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapEntryStmt
import SubNLogN.Machine.Tables.TapRank

/-!
# K6 (`Machine/Tables/TapPhaseStmt.lean`): the tap phase — statement only

**Scope (honest summary).** Defines the cost part `tapPart` of `tabCost` and the interface
statement `TapPhaseStmt` (proved in `TapPh.lean` from `TapRecStmt` and
`TapBlockRankStmt`). Nothing is proved here.

`TapPhaseStmt` asks for **one** host program that pushes the whole tap table
`tapTabSyms wT P t (tabOf ω P t)` (`SubNLogN/Machine/Contracts/Bridge.lean:175`) onto `tapTab`
(axes `1, …, d-1` in this order, each block pushed last record first then preceded on the stack
by its `mark`, so that axis `d-1` ends on top), reading `t_i` from the header on `par`, starting
from the lower shape `hdrSyms [t_0]` on `rSH` and `A_1 = t_0` on `rA`, and ending with
`hdrSyms [t_{d-1}, …, t_0]` on `rSH` and `A_d = prefixProd t d` on `rA` (as the solver phase
needs them); every other stack is restored. The parameter stacks (`Roles.lean`) `rP rW rB rPC rPi
rLn rPW rPW1 rZero rNmu rPq rq` hold their values; all other scratch stacks are empty and may be
used as temporaries. Cost `K (C+1)(KM+1) (tapPart + tapTabLen + setup)`
(`SubNLogN/Machine/Contracts/Tables.lean`, Lemma 4.6 (`lem:bridge-C`) (bridge Lemma C)(iii) and Lemma B.3 (`lem:phase-tables`)).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common

/-- The tap part of `tabCost`: per spread axis `i`, `A_i` records of `(2P+1)` entries with
`(2P+1)` samples of size `tabUnit b i` each. -/
def tapPart (b : BrPar) : ℕ :=
  ((spreadOrder b.d).map fun i : Fin b.d =>
    prefixProd b.t i * ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i)).sum

/-- The scratch stacks that are empty around the tap phase (all `.inr j` except the parameter
roles `0 … 10`, `13`, `16` (`rA`) and `22` (`rSH`)). -/
def TapScratch (j : ℕ) : Prop :=
  j = 11 ∨ j = 12 ∨ j = 14 ∨ j = 15 ∨ (17 ≤ j ∧ j ≤ 21) ∨ (23 ≤ j)

/-- **[INTERFACE] The tap phase** (`TapPhaseStmt`). See the module docstring. -/
def TapPhaseStmt : Prop :=
  ∃ K : ℕ, ∀ (I : TB) (Mul : ℕ → ℕ) (C KM : ℕ), I.Spec Mul C → (∀ w, Mul w ≤ KM * (w + 1) ^ 2) →
    ∃ prog : TP I, prog.Closed ∧
      ∀ (b : BrPar) (rpar : List Sym) (B : TL → List Sym),
        2 ≤ b.d → ShapeOK b.t → 1 ≤ b.ω → 1 ≤ b.wT →
        (∀ i ∈ spreadOrder b.d, CArrFits b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) i)) →
        B sPar = hdrSyms b.hdr ++ rpar →
        B rP = natSyms b.P → B rW = natSyms b.ω → B rB = natSyms (tapPrec b.P) →
        B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1 →
        B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1 →
        B rPW = intSyms ((2 ^ b.wT : ℕ) : ℤ) → B rPW1 = intSyms ((2 ^ (b.wT + 1) : ℕ) : ℤ) →
        B rSH = hdrSyms (lowerShape b.t 1) → B rA = natSyms (prefixProd b.t 1) →
        (∀ j : Fin 61, TapScratch j → B (.inr j) = []) →
        HT [] B prog
          (Function.update (Function.update (Function.update B sTap
            (tapTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ B sTap))
            rSH (hdrSyms (lowerShape b.t b.d))) rA (natSyms (prefixProd b.t b.d)))
          (K * (C + 1) * (KM + 1) * (tapPart b + tapTabLen b + b.setup))

end SubNLogN.Machine.Tables
