/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.BranchFinal
import SubNLogN.Machine.Pipe.ConvIn
import SubNLogN.Machine.Pipe.ConvOut
import SubNLogN.Machine.Pipe.Guard
import SubNLogN.Machine.Pipe.BranchMathSpread
import SubNLogN.Machine.MulBig.Main
import SubNLogN.Machine.Pipe.BranchCostW8

/-!
# K7 (`Machine/Pipe/BranchWired.lean`): the Walsh-branch cut with the landed kernels plugged in

`walshBranchCut_of_pipeW P₀ P₁ J τ hRP hTab hBr hSV hTF hC` is `walshBranchCut_of_pipe`
(`BranchFinal.lean`) with the five hypotheses that are now theorems discharged:
* `MulBigContract` by `MulBig.mulBig_holds` (`Machine/MulBig/Main.lean`);
* `GuardStmt` by `guard_holds` (`Pipe/Guard.lean`);
* `ConvInStmt` / `ConvOutStmt` by `convIn_holds` / `convOut_holds` (`Pipe/ConvIn.lean`,
  `Pipe/ConvOut.lean`);
* `Bridge_spreadPart_widthsStmt` by `bridge_spreadPart_widths` (`Pipe/BranchMathSpread.lean`).

Remaining explicit hypotheses (nothing else is assumed): the parameter kernel
`ReadParamsStmt fnewSched (walshMidData fnewSched row46Layer P₀ P₁ J) readParamsCost`,
the K6 table machine `BridgeTablesMachineStmt`, the K5 bridge machine at the pipe's family
`BridgeMachineStmt (bridgeX τ) (fnewFam fnewSched (walshMid row46) (walshMidData … P₀ P₁ J))`
(reduced via `bridgeMachine_of_parts` and `midMachine_fnew_of_walsh`), the solver-state widths
`Bridge_solve_widthsStmt` and the table widths `TabConcrete_fitStmt` (proved in
`Pipe/BranchMathSolve.lean` and `Pipe/BranchMathTables.lean`), and the Walsh cost clause at
`branchCost readParamsCost (bridgeX τ) fnewSched (walshMidData … P₀ P₁ J)`.

`walshBranchCut_of_pipeWC P₀ P₁ J hRP hTab hBr hSV hTF` additionally fixes `τ = Row46.tau` and
discharges the cost clause by `walshCostClause_walshMidData row46Layer rfl P₀ P₁ J`
(`Pipe/BranchCostW8.lean`).

Paper: the branch is one bridge call of Theorem 4.7 (`thm:bridge-precision`) with the Walsh-route
middle (Corollary 6.6 (`cor:walsh-middle`)), Section 7.1 (`sec:main-alg`).
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge

/-- **The Walsh-branch cut with the landed kernels plugged in (`walshBranchCut_of_pipeW`,
0 `sorry`).** For any constants `P₀ P₁ J` and interchange exponent `τ`: from the parameter kernel,
the K6 table machine, the K5 bridge machine at the pipe's family, the solver-state and table widths and the
cost clause (the six remaining hypotheses, see the module docstring), the body of the
assembly's `WalshBranchCut` holds for the closed map
`FnewOfR roundHalfUpR row46 (TabConcreteR roundHalfUpR row46) (walshMid row46)`. -/
theorem walshBranchCut_of_pipeW (P₀ P₁ J : ℕ) (τ : ℝ)
    (hRP : ReadParamsStmt fnewSched (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J)
      readParamsCost)
    (hTab : BridgeTablesMachineStmt)
    (hBr : BridgeMachineStmt (bridgeX τ) (fnewFam fnewSched (walshMid Math.Cost.row46)
      (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J)))
    (hSV : Bridge_solve_widthsStmt) (hTF : TabConcrete_fitStmt)
    (hC : WalshCostClause (branchCost readParamsCost (bridgeX τ) fnewSched
      (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J))) :
    ∃ (N : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
      WalshBranchFromStmt (FnewOfR roundHalfUpR Math.Cost.row46
        (TabConcreteR roundHalfUpR Math.Cost.row46) (walshMid Math.Cost.row46)) N Tw ∧
        WalshCostClause Tw :=
  walshBranchCut_of_pipe P₀ P₁ J τ MulBig.mulBig_holds hRP guard_holds hTab convIn_holds hBr
    convOut_holds bridge_spreadPart_widths hSV hTF hC

/-- **The Walsh-branch cut with the landed kernels and the cost clause plugged in
(`walshBranchCut_of_pipeWC`, 0 `sorry`).** `walshBranchCut_of_pipeW` at the row's interchange
exponent `τ = Row46.tau`, with the cost clause discharged by `walshCostClause_walshMidData`
(`Pipe/BranchCostW8.lean`). Remaining hypotheses: the parameter kernel, the K6 table machine, the K5 bridge machine
at the pipe's family, the solver-state widths and the table widths. -/
theorem walshBranchCut_of_pipeWC (P₀ P₁ J : ℕ)
    (hRP : ReadParamsStmt fnewSched (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J)
      readParamsCost)
    (hTab : BridgeTablesMachineStmt)
    (hBr : BridgeMachineStmt (bridgeX ((Math.Cost.Row46.tau : ℚ) : ℝ))
      (fnewFam fnewSched (walshMid Math.Cost.row46)
        (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J)))
    (hSV : Bridge_solve_widthsStmt) (hTF : TabConcrete_fitStmt) :
    ∃ (N : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
      WalshBranchFromStmt (FnewOfR roundHalfUpR Math.Cost.row46
        (TabConcreteR roundHalfUpR Math.Cost.row46) (walshMid Math.Cost.row46)) N Tw ∧
        WalshCostClause Tw :=
  walshBranchCut_of_pipeW P₀ P₁ J _ hRP hTab hBr hSV hTF
    (walshCostClause_walshMidData Assembly.row46Layer rfl P₀ P₁ J)

end SubNLogN.Machine.Pipe
