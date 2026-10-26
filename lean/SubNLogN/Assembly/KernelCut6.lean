import SubNLogN.Assembly.KernelCut5
import SubNLogN.Machine.Bridge.SpreadStageMain

/-!
# Assembly: the kernel-level cut, version 6 (interchange and Walsh middle remaining)

`KernelCut6` refines `KernelCut5` (`Assembly/KernelCut5.lean`) by discharging the field `spreadLines`
via `Bridge.SpreadAux.spreadLines_holds : SpreadLinesStmt`
(`Machine/Bridge/SpreadStageMain.lean`, formalizing the overlap-add spreading stages of Section 4.4
(`sec:bridge-alg`) and Lemma 4.6 (bridge Lemma C)(ii), `lem:bridge-C`, on the multi-stack
Turing-machine framework).

All spreading, deconvolution, and table-generation fields are now discharged; the two remaining fields are:
* `c6` — the Appendix A (Lemma A.8, `lem:transfer12`) interchange network machine `C6InterchangeStmt τ` at `τ = Row46.tau`;
* `walshMiddle` — the Walsh middle contract `WalshMiddleMachineStmt (midLayerParams row46Layer 1)`.

* `kernelCut5_of_6 : KernelCut6 → KernelCut5` (0 `sorry`);
* `kernelCutStmt_of_6 : KernelCut6 → KernelCutStmt` (0 `sorry`);
* `w9X_of_kernelCut6 : KernelCut6 → W9SubNLogNSpecX` (0 `sorry`).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Machine SubNLogN.Machine.Pipe SubNLogN.Math.Cost SubNLogN.Math.Bridge

/-- **The kernel-level cut, version 6 (`KernelCut6`).** The two remaining parts of the bridge-branch machine
at `τ = Row46.tau` (discharged in `KernelCut7` and `KernelCutFinal`):
* `c6` — the Lemma A.8 (`lem:transfer12`) interchange `C6InterchangeStmt τ` (gives Expose, Restore and Reorder);
* `walshMiddle` — the Walsh middle contract `WalshMiddleMachineStmt (midLayerParams row46Layer 1)` (Corollary 6.6). -/
structure KernelCut6 : Prop where
  /-- Appendix A (Lemma A.8): the interchange network machine at `τ` -/
  c6 : C6InterchangeStmt ((Row46.tau : ℚ) : ℝ)
  /-- K4: the Walsh middle machine at Proposition A.11's bands of `midLayerParams row46Layer 1` -/
  walshMiddle : WalshMiddleMachineStmt (midLayerParams row46Layer 1)

/-- **Version 6 implies version 5 (`kernelCut5_of_6`, 0 `sorry`).** -/
theorem kernelCut5_of_6 (h : KernelCut6) : KernelCut5 :=
  ⟨h.c6, Bridge.SpreadAux.spreadLines_holds, h.walshMiddle⟩

/-- **Version 6 implies version 1 (`kernelCutStmt_of_6`, 0 `sorry`).** -/
theorem kernelCutStmt_of_6 (h : KernelCut6) : KernelCutStmt :=
  kernelCutStmt_of_5 (kernelCut5_of_6 h)

/-- **`W9SubNLogNSpecX` from the version-6 cut (0 `sorry`).** -/
theorem w9X_of_kernelCut6 (h : KernelCut6) : W9SubNLogNSpecX :=
  w9X_of_kernelCut5 (kernelCut5_of_6 h)

end SubNLogN.Assembly
