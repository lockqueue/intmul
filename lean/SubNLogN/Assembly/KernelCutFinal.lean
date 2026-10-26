import SubNLogN.Assembly.KernelCut7
import SubNLogN.Machine.T4aHolds

/-!
# Assembly: closing the kernel-level cut

The final field of `KernelCut7` is the Walsh middle machine contract
`WalshMiddleMachineStmt (midLayerParams row46Layer 1)` (`Machine/Contracts/FFT.lean`, Corollary 6.6 (`cor:walsh-middle`)). This file reduces
`W9SubNLogNSpecX` to that statement (0 `sorry`):

* `kernelCut7_of_mid (h : WalshMiddleMachineStmt (midLayerParams row46Layer 1)) : KernelCut7`;
* `w9X_of_mid (h : WalshMiddleMachineStmt (midLayerParams row46Layer 1)) : W9SubNLogNSpecX`.

Applying `Machine.walshMiddle_holds : WalshMiddleMachineStmt (midLayerParams row46Layer 1)`
(`Machine/T4aHolds.lean`, unconditional) discharges the entire cut (0 `sorry`, no hypotheses):
`theorem kernelCut7_proved : KernelCut7 := kernelCut7_of_mid Machine.walshMiddle_holds` and
`theorem w9SubNLogNSpecX_proved : W9SubNLogNSpecX := w9X_of_mid Machine.walshMiddle_holds`.
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Machine

/-- **The cut from the Walsh middle contract (`kernelCut7_of_mid`, 0 `sorry`).** -/
theorem kernelCut7_of_mid (h : WalshMiddleMachineStmt (midLayerParams row46Layer 1)) : KernelCut7 :=
  ⟨h⟩

/-- **`W9SubNLogNSpecX` from the Walsh middle contract alone (`w9X_of_mid`, 0 `sorry`).** -/
theorem w9X_of_mid (h : WalshMiddleMachineStmt (midLayerParams row46Layer 1)) : W9SubNLogNSpecX :=
  w9X_of_kernelCut7 (kernelCut7_of_mid h)

/-- **The kernel-level cut, proved (`kernelCut7_proved`, 0 `sorry`, no hypotheses):** supplied by
`Machine.walshMiddle_holds` (`Machine/T4aHolds.lean`; identifier `T4aHolds` kept for stability). -/
theorem kernelCut7_proved : KernelCut7 :=
  kernelCut7_of_mid Machine.walshMiddle_holds

/-- **`W9SubNLogNSpecX`, proved (`w9SubNLogNSpecX_proved`, 0 `sorry`, no hypotheses).** -/
theorem w9SubNLogNSpecX_proved : W9SubNLogNSpecX :=
  w9X_of_mid Machine.walshMiddle_holds

end SubNLogN.Assembly
