import SubNLogN.Assembly.KernelCut
import SubNLogN.Machine.Pipe.Guard
import SubNLogN.Machine.Pipe.ConvOut
import SubNLogN.Machine.Pipe.BranchMathSpread
import SubNLogN.Machine.Pipe.BranchMathSolve
import SubNLogN.Machine.Pipe.BranchMathTables
import SubNLogN.Machine.Pipe.BranchCostW8

/-!
# Assembly: the kernel-level cut, version 2

`KernelCut2 P₀ P₁ J` refines `KernelCut P₀ P₁ J` (`Assembly/KernelCut.lean`) by discharging six
fields directly:
* `guard` — `Machine.Pipe.guard_holds` (`Pipe/Guard.lean`);
* `convOut` — `Machine.Pipe.convOut_holds` (`Pipe/ConvOut.lean`);
* `spreadWidths` — `Machine.Pipe.bridge_spreadPart_widths` (`Pipe/BranchMathSpread.lean`);
* `solveWidths` — `Machine.Pipe.bridge_solve_widths` (`Pipe/BranchMathSolve.lean`);
* `tabFit` — `Machine.Pipe.tabConcrete_fit` (`Pipe/BranchMathTables.lean`);
* `cost` — `Machine.Pipe.walshCostClause_walshMidData row46Layer rfl P₀ P₁ J`
  (`Pipe/BranchCostW8.lean`).

The remaining three fields (discharged in `KernelCut3`–`KernelCutFinal`) are `readParams`, `tables`,
and `bridge`, at the Lemma A.8 (`lem:transfer12`) interchange exponent `τ = Row46.tau`.

* `kernelCutStmt_of_2 : KernelCut2Stmt → KernelCutStmt` (0 `sorry`), reducing `KernelCutStmt`
  to the three-field `KernelCut2Stmt`;
* `w9X_of_kernelCut2 : KernelCut2Stmt → W9SubNLogNSpecX` (0 `sorry`).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Machine SubNLogN.Machine.Pipe SubNLogN.Math.Cost SubNLogN.Math.Bridge

/-- **The kernel-level cut, version 2 (`KernelCut2 P₀ P₁ J`).** The three remaining fields of `KernelCut P₀ P₁ J`:
`readParams` (read the root header, push the bridge/middle parameters), `tables` (the
table generator) and `bridge` (the bridge machine: bridge stages + Walsh middle machine), at
`τ = Row46.tau`. -/
structure KernelCut2 (P₀ P₁ J : ℕ) : Prop where
  /-- read the root header and push the bridge/middle parameters -/
  readParams : ReadParamsStmt fnewSched (walshMidData fnewSched row46Layer P₀ P₁ J) readParamsCost
  /-- the table generator (K6) -/
  tables : BridgeTablesMachineStmt
  /-- the bridge machine (K5 parts + Walsh middle machine) -/
  bridge : BridgeMachineStmt (bridgeX ((Row46.tau : ℚ) : ℝ))
    (fnewFam fnewSched (walshMid row46) (walshMidData fnewSched row46Layer P₀ P₁ J))

/-- **The kernel-level cut, version 2 (`KernelCut2Stmt`):** `∃ P₀ P₁ J, KernelCut2 P₀ P₁ J`. -/
def KernelCut2Stmt : Prop := ∃ P₀ P₁ J : ℕ, KernelCut2 P₀ P₁ J

/-- **Version 2 implies version 1 (`kernelCutStmt_of_2`, 0 `sorry`):** the dropped fields are the proved
`guard_holds`, `convOut_holds`, `bridge_spreadPart_widths`, `bridge_solve_widths`, `tabConcrete_fit`
and `walshCostClause_walshMidData row46Layer rfl P₀ P₁ J`. -/
theorem kernelCutStmt_of_2 (h : KernelCut2Stmt) : KernelCutStmt := by
  obtain ⟨P₀, P₁, J, hK⟩ := h
  exact ⟨P₀, P₁, J, hK.readParams, guard_holds, hK.tables, hK.bridge, convOut_holds,
    bridge_spreadPart_widths, bridge_solve_widths, tabConcrete_fit,
    walshCostClause_walshMidData row46Layer rfl P₀ P₁ J⟩

/-- **`W9SubNLogNSpecX` from the version-2 cut (0 `sorry`).** -/
theorem w9X_of_kernelCut2 (h : KernelCut2Stmt) : W9SubNLogNSpecX :=
  w9X_of_kernelCut (kernelCutStmt_of_2 h)

end SubNLogN.Assembly
