import SubNLogN.Assembly.Cut
import SubNLogN.Machine.Pipe.BranchFinal
import SubNLogN.Machine.MulBig.Main
import SubNLogN.Machine.Pipe.ConvIn

/-!
# Assembly: the kernel-level cut below `WalshBranchCut`

Using the pipe reduction `Machine.Pipe.walshBranchCut_of_pipe` (`Machine/Pipe/BranchFinal.lean`),
the bridge-branch machine `WalshBranchCut` follows from the machine kernels and three value-level width
statements, at the concrete schedule `fnewSched`, read-parameters cost `readParamsCost`, bridge cost
`bridgeX τ` and middle data `walshMidData fnewSched row46Layer P₀ P₁ J` (the middle eligibility `MOK` and
`ZeroOut`, `BranchMathStmt` are discharged inside, the band part by `midBandsW8_holds`). This file states
the remaining hypotheses as one structure `KernelCut P₀ P₁ J` (supplying `mulBig_holds : MulBigContract`
and `convIn_holds : ConvInStmt`), with the Lemma A.8 (`lem:transfer12`)
interchange exponent fixed to the row's `τ = 1 - 4ξ = 1 - 2^{-40}` (`Row46.tau`). The constants `P₀`
(cutoff of the Walsh-middle machine contract, ultimately Proposition A.11's cutoff), `P₁` (from the proved
`midCallsBand_of_bands`) and `J` (exponent of the Walsh-middle machine cost) are outputs of machine
contracts, so the cut is `KernelCutStmt := ∃ P₀ P₁ J, KernelCut P₀ P₁ J`.

* `walshBranchCut_of_kernelCut : KernelCutStmt → WalshBranchCut` and
  `w9X_of_kernelCut : KernelCutStmt → W9SubNLogNSpecX` (0 `sorry`).

All fields of `KernelCut` are discharged across `KernelCut2.lean`–`KernelCutFinal.lean`.
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Machine SubNLogN.Machine.Pipe SubNLogN.Math.Cost SubNLogN.Math.Bridge

/-- **The kernel-level cut at the constants `P₀ P₁ J` (`KernelCut P₀ P₁ J`).** Bundles the nine
hypotheses of `walshBranchCut_of_pipe` at `τ = Row46.tau` (all discharged in `KernelCut2`–`KernelCutFinal`):
`readParams` (header/parameter setup), `guard` (input-width guard), `tables` (table generation), `bridge`
(bridge stages and Walsh middle machine), `convOut` (output conversion), `spreadWidths`, `solveWidths`,
`tabFit` (value-level width bounds), and `cost` (the Walsh-route cost clause of the branch, Section 7.3). -/
structure KernelCut (P₀ P₁ J : ℕ) : Prop where
  /-- read the root header and push the bridge/middle parameters -/
  readParams : ReadParamsStmt fnewSched (walshMidData fnewSched row46Layer P₀ P₁ J) readParamsCost
  /-- the input-width guard kernel -/
  guard : GuardStmt
  /-- the table generator (K6) -/
  tables : BridgeTablesMachineStmt
  /-- the bridge machine (K5 parts + Walsh middle machine) -/
  bridge : BridgeMachineStmt (bridgeX ((Row46.tau : ℚ) : ℝ))
    (fnewFam fnewSched (walshMid row46) (walshMidData fnewSched row46Layer P₀ P₁ J))
  /-- the output conversion -/
  convOut : ConvOutStmt
  /-- value-level widths of the spreading parts -/
  spreadWidths : Bridge_spreadPart_widthsStmt
  /-- value-level widths of the solver states -/
  solveWidths : Bridge_solve_widthsStmt
  /-- value-level widths of the concrete tables -/
  tabFit : TabConcrete_fitStmt
  /-- the Walsh-route cost clause of the branch -/
  cost : WalshCostClause (branchCost readParamsCost (bridgeX ((Row46.tau : ℚ) : ℝ)) fnewSched
    (walshMidData fnewSched row46Layer P₀ P₁ J))

/-- **The kernel-level cut (`KernelCutStmt`):** `∃ P₀ P₁ J, KernelCut P₀ P₁ J`. -/
def KernelCutStmt : Prop := ∃ P₀ P₁ J : ℕ, KernelCut P₀ P₁ J

/-- **`WalshBranchCut` from the kernel-level cut (0 `sorry`):** `walshBranchCut_of_pipe` with the proved
`mulBig_holds` and `convIn_holds`. -/
theorem walshBranchCut_of_kernelCut (h : KernelCutStmt) : WalshBranchCut := by
  obtain ⟨P₀, P₁, J, hK⟩ := h
  exact walshBranchCut_of_pipe P₀ P₁ J _ MulBig.mulBig_holds hK.readParams hK.guard hK.tables
    convIn_holds hK.bridge hK.convOut hK.spreadWidths hK.solveWidths hK.tabFit hK.cost

/-- **`W9SubNLogNSpecX` from the kernel-level cut (0 `sorry`).** -/
theorem w9X_of_kernelCut (h : KernelCutStmt) : W9SubNLogNSpecX :=
  w9X_of_cut (walshBranchCut_of_kernelCut h)

end SubNLogN.Assembly
