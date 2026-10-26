import SubNLogN.Assembly.KernelCut3
import SubNLogN.Machine.Bridge.ReorderLoop
import SubNLogN.Machine.Pipe.ReadParams
import SubNLogN.Machine.Bridge.PrePostFinal

/-!
# Assembly: the kernel-level cut, version 4

`KernelCut4` refines `KernelCut3Stmt` (`Assembly/KernelCut3.lean`) with
* the field `reorder` discharged from the field `c6`: `reorder_of_c6 τ hτ hC6`
  (`Machine/Bridge/ReorderLoop.lean`), using the Lemma A.8 (`lem:transfer12`) premise `c6Premise_row46`;
* the field `readParams` discharged: `Machine.Pipe.readParams_holds row46Layer P₀ P₁ J`
  (`Machine/Pipe/ReadParams.lean`, uniform in `P₀ P₁ J`);
* the field `preScale` discharged: `Machine.preScale_holds`
  (`Machine/Bridge/PrePostFinal.lean`);
* the Walsh middle stated directly as the contract `WalshMiddleMachineStmt (midLayerParams row46Layer 1)`
  (`Contracts/FFT.lean`, Corollary 6.6 (`cor:walsh-middle`), which supplies the cutoff `P₀`).

Remaining fields (discharged in `KernelCut5`–`KernelCutFinal`): `tables`, `c6`, `spreadLines`, `solveAxis`, `walshMiddle`.

* `kernelCut3Stmt_of_4 : KernelCut4 → KernelCut3Stmt` (0 `sorry`);
* `kernelCutStmt_of_4 : KernelCut4 → KernelCutStmt` (0 `sorry`);
* `w9X_of_kernelCut4 : KernelCut4 → W9SubNLogNSpecX` (0 `sorry`).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Machine SubNLogN.Machine.Pipe SubNLogN.Math.Cost SubNLogN.Math.Bridge

/-- **The kernel-level cut, version 4 (`KernelCut4`).** The five remaining parts of the bridge-branch machine at
`τ = Row46.tau`:
* `tables` — the certified table generator;
* `spreadLines`, `solveAxis` — spreading and per-axis deconvolution kernels (Section 4.4);
* `c6` — the Lemma A.8 (`lem:transfer12`) interchange `C6InterchangeStmt τ` (gives Expose, Restore and Reorder);
* `walshMiddle` — the Walsh middle contract `WalshMiddleMachineStmt (midLayerParams row46Layer 1)` (Corollary 6.6). -/
structure KernelCut4 : Prop where
  /-- the table generator (K6) -/
  tables : BridgeTablesMachineStmt
  /-- Appendix A (Lemma A.8): the interchange network machine at `τ` -/
  c6 : C6InterchangeStmt ((Row46.tau : ℚ) : ℝ)
  /-- K5: spreading the lines -/
  spreadLines : SpreadLinesStmt
  /-- K5: the per-axis solver -/
  solveAxis : SolveAxisStmt
  /-- K4: the Walsh middle machine at Proposition A.11's bands of `midLayerParams row46Layer 1` -/
  walshMiddle : WalshMiddleMachineStmt (midLayerParams row46Layer 1)

/-- **Version 4 implies version 3 (`kernelCut3Stmt_of_4`, 0 `sorry`).** `P₀` from the Walsh middle contract;
`readParams` from `readParams_holds row46Layer P₀`; `preScale` from `preScale_holds`; `reorder` from `reorder_of_c6` with `c6Premise_row46`. -/
theorem kernelCut3Stmt_of_4 (h : KernelCut4) : KernelCut3Stmt := by
  obtain ⟨P₀, hW⟩ := h.walshMiddle
  exact ⟨P₀, readParams_holds row46Layer P₀, h.tables, preScale_holds, reorder_of_c6 _ c6Premise_row46 h.c6, h.c6,
    h.spreadLines, h.solveAxis, hW⟩

/-- **Version 4 implies version 1 (`kernelCutStmt_of_4`, 0 `sorry`).** -/
theorem kernelCutStmt_of_4 (h : KernelCut4) : KernelCutStmt :=
  kernelCutStmt_of_3 (kernelCut3Stmt_of_4 h)

/-- **`W9SubNLogNSpecX` from the version-4 cut (0 `sorry`).** -/
theorem w9X_of_kernelCut4 (h : KernelCut4) : W9SubNLogNSpecX :=
  w9X_of_kernelCut3 (kernelCut3Stmt_of_4 h)

end SubNLogN.Assembly
