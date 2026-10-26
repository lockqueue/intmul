import SubNLogN.Assembly.KernelCut4
import SubNLogN.Machine.Bridge.SolveAxis
import SubNLogN.Machine.Bridge.SolveSweep
import SubNLogN.Machine.Bridge.SolveParams
import SubNLogN.Machine.Arith.CMul
import SubNLogN.Machine.Tables.Main
import SubNLogN.Machine.Tables.SetupProg
import SubNLogN.Machine.Tables.TapPhHolds
import SubNLogN.Machine.Tables.TapRec
import SubNLogN.Machine.Tables.TapRankProof

/-!
# Assembly: the kernel-level cut, version 5

`KernelCut5` refines `KernelCut4` (`Assembly/KernelCut4.lean`) with
* the field `solveAxis` discharged: `solveAxis_holds Bridge.solveSweep_holds solParamRows_holds
  Arith.cmulTrunc_holds` (`Machine/Bridge/SolveAxis.lean`, `Machine/Arith/CMul.lean`);
* the field `tables` discharged: `Tables.bridgeTablesMachine_holds Tables.setup_holds
  (Tables.tapPhase_holds Tables.tapRec_holds Tables.TapRankProof.tapBlockRank_holds)`
  (`Machine/Tables/Main.lean`, Lemma B.3 (`lem:phase-tables`) and Lemma 4.6 (bridge Lemma C)(iii)).

Remaining fields (discharged in `KernelCut6`–`KernelCutFinal`): `c6`, `spreadLines`, `walshMiddle`.

* `kernelCut4_of_5 : KernelCut5 → KernelCut4` (0 `sorry`);
* `kernelCutStmt_of_5 : KernelCut5 → KernelCutStmt` (0 `sorry`);
* `w9X_of_kernelCut5 : KernelCut5 → W9SubNLogNSpecX` (0 `sorry`).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Machine SubNLogN.Machine.Pipe SubNLogN.Math.Cost SubNLogN.Math.Bridge

/-- **The kernel-level cut, version 5 (`KernelCut5`).** The three remaining parts of the bridge-branch machine at
`τ = Row46.tau`:
* `spreadLines` — spreading the lines along exposed axes (Section 4.4);
* `c6` — the Lemma A.8 (`lem:transfer12`) interchange `C6InterchangeStmt τ` (gives Expose, Restore and Reorder);
* `walshMiddle` — the Walsh middle contract `WalshMiddleMachineStmt (midLayerParams row46Layer 1)` (Corollary 6.6). -/
structure KernelCut5 : Prop where
  /-- Appendix A (Lemma A.8): the interchange network machine at `τ` -/
  c6 : C6InterchangeStmt ((Row46.tau : ℚ) : ℝ)
  /-- K5: spreading the lines -/
  spreadLines : SpreadLinesStmt
  /-- K4: the Walsh middle machine at Proposition A.11's bands of `midLayerParams row46Layer 1` -/
  walshMiddle : WalshMiddleMachineStmt (midLayerParams row46Layer 1)

/-- **Version 5 implies version 4 (`kernelCut4_of_5`, 0 `sorry`).** -/
theorem kernelCut4_of_5 (h : KernelCut5) : KernelCut4 :=
  ⟨Tables.bridgeTablesMachine_holds Tables.setup_holds
    (Tables.tapPhase_holds Tables.tapRec_holds Tables.TapRankProof.tapBlockRank_holds), h.c6, h.spreadLines,
    solveAxis_holds Bridge.solveSweep_holds solParamRows_holds Arith.cmulTrunc_holds, h.walshMiddle⟩

/-- **Version 5 implies version 1 (`kernelCutStmt_of_5`, 0 `sorry`).** -/
theorem kernelCutStmt_of_5 (h : KernelCut5) : KernelCutStmt :=
  kernelCutStmt_of_4 (kernelCut4_of_5 h)

/-- **`W9SubNLogNSpecX` from the version-5 cut (0 `sorry`).** -/
theorem w9X_of_kernelCut5 (h : KernelCut5) : W9SubNLogNSpecX :=
  w9X_of_kernelCut4 (kernelCut4_of_5 h)

end SubNLogN.Assembly
