import SubNLogN.Assembly.KernelCut6
import SubNLogN.Machine.AppC.C6Holds

/-!
# Assembly: the kernel-level cut, version 7 (only the Walsh middle remains)

`KernelCut7` refines `KernelCut6` (`Assembly/KernelCut6.lean`) by discharging the field `c6` via
`Machine.c6_holds : C6InterchangeStmt ((Row46.tau : ℚ) : ℝ)` (`Machine/AppC/C6Holds.lean`, Lemma A.8 (`lem:transfer12`),
built from the Proposition A.7 (`prop:transfer11`) power-width interchange `C5.NetAuxF.c5Net_of` on the certified `h = 100` bit network).

The single remaining field (discharged in `KernelCutFinal.lean`) is `walshMiddle` — the Walsh middle contract
`WalshMiddleMachineStmt (midLayerParams row46Layer 1)` (`Machine/Contracts/FFT.lean`).

* `kernelCut6_of_7 : KernelCut7 → KernelCut6` (0 `sorry`);
* `kernelCutStmt_of_7 : KernelCut7 → KernelCutStmt` (0 `sorry`);
* `w9X_of_kernelCut7 : KernelCut7 → W9SubNLogNSpecX` (0 `sorry`).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Machine SubNLogN.Machine.Pipe SubNLogN.Math.Cost SubNLogN.Math.Bridge

/-- **The kernel-level cut, version 7 (`KernelCut7`).** The single remaining obligation of the bridge-branch machine:
`walshMiddle` — the Walsh middle contract `WalshMiddleMachineStmt (midLayerParams row46Layer 1)` (the
Walsh middle machine at Proposition A.11's bands of `midLayerParams row46Layer 1`, exponent
`λ' = row46Layer.lam'`, Corollary 6.6 (`cor:walsh-middle`)). -/
structure KernelCut7 : Prop where
  /-- K4: the Walsh middle machine at Proposition A.11's bands of `midLayerParams row46Layer 1` -/
  walshMiddle : WalshMiddleMachineStmt (midLayerParams row46Layer 1)

/-- **Version 7 implies version 6 (`kernelCut6_of_7`, 0 `sorry`):** `c6` is `c6_holds`. -/
theorem kernelCut6_of_7 (h : KernelCut7) : KernelCut6 :=
  ⟨c6_holds, h.walshMiddle⟩

/-- **Version 7 implies version 1 (`kernelCutStmt_of_7`, 0 `sorry`).** -/
theorem kernelCutStmt_of_7 (h : KernelCut7) : KernelCutStmt :=
  kernelCutStmt_of_6 (kernelCut6_of_7 h)

/-- **`W9SubNLogNSpecX` from the version-7 cut (0 `sorry`).** -/
theorem w9X_of_kernelCut7 (h : KernelCut7) : W9SubNLogNSpecX :=
  w9X_of_kernelCut6 (kernelCut6_of_7 h)

end SubNLogN.Assembly
