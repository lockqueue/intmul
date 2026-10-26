/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapPhaseStmt

/-!
# K6 (`Machine/Tables/SetupStmt.lean`): parameter setup and cleanup — statement only

**Scope (honest summary).** Defines the parameter state `parSt B b` (all parameter roles of
`Roles.lean` set on top of `B`) and the interface statement `SetupStmt` (parameter setup
and cleanup). Nothing is proved here.

`SetupStmt` asks for two host programs: `setupP`, which from a state with the bridge header
`hdrSyms b.hdr` on `par` (fields `p, P, ω, wI, wT, wOut, pIn, wIn, d, t_0, …`;
`SubNLogN/Machine/Contracts/Bridge.lean:100`) and all scratch stacks `.inr j` empty sets the
parameter roles (`rP = P`, `rW = ω`, `rB = tapPrec P`, `rPC = coeffPrec P`, `rPi`/`rLn` = the W7
`π`/`ln 2` evaluations at `W7.tapPrec (tapPrec P)`, `rPW = 2^wT`, `rPW1 = 2^(wT+1)`,
`rZero = 0`, `rNmu = 2^(pC+2+q)`, `rPq = 2^q`, `rq = q = P+2`, `rSH = hdrSyms [t_0]`,
`rA = t_0`) and restores everything else; and `cleanP`, which pops them all again. Cost
`K (C+1)(KM+1) (tabOnce + setup + wT + 1)` each (`tabOnce` covers the one-time `π`, `ln 2`
evaluations, `SubNLogN/Machine/Contracts/Tables.lean:58`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common

/-- The parameter state of the table generator: the parameter roles set on top of `B`. -/
def parSt (B : TL → List Sym) (b : BrPar) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update B
    rP (natSyms b.P)) rW (natSyms b.ω)) rB (natSyms (tapPrec b.P)))
    rPC (natSyms (coeffPrec b.P)))
    rPi (intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1))
    rLn (intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1))
    rPW (intSyms ((2 ^ b.wT : ℕ) : ℤ))) rPW1 (intSyms ((2 ^ (b.wT + 1) : ℕ) : ℤ)))
    rZero (intSyms 0)) rNmu (intSyms ((2 ^ (coeffPrec b.P + 2 + (b.P + 2)) : ℕ) : ℤ)))
    rPq (intSyms ((2 ^ (b.P + 2) : ℕ) : ℤ))) rq (natSyms (b.P + 2)))
    rSH (hdrSyms (lowerShape b.t 1))) rA (natSyms (prefixProd b.t 1))

/-- **[INTERFACE] Parameter setup and cleanup** (`SetupStmt`). See the
module docstring. -/
def SetupStmt : Prop :=
  ∃ K : ℕ, ∀ (I : TB) (Mul : ℕ → ℕ) (C KM : ℕ), I.Spec Mul C → (∀ w, Mul w ≤ KM * (w + 1) ^ 2) →
    ∃ setupP cleanP : TP I, setupP.Closed ∧ cleanP.Closed ∧
      (∀ (b : BrPar) (rpar : List Sym) (B : TL → List Sym),
        2 ≤ b.d → ShapeOK b.t → B sPar = hdrSyms b.hdr ++ rpar →
        (∀ j : Fin 61, B (.inr j) = []) →
        HT [] B setupP (parSt B b) (K * (C + 1) * (KM + 1) * (tabOnce b + b.setup + b.wT + 1))) ∧
      (∀ (b : BrPar) (B : TL → List Sym), 2 ≤ b.d → ShapeOK b.t →
        (∀ j : Fin 61, B (.inr j) = []) →
        HT [] (parSt B b) cleanP B (K * (C + 1) * (KM + 1) * (tabOnce b + b.setup + b.wT + 1)))

end SubNLogN.Machine.Tables
