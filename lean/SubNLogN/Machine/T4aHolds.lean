/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.WalshMiddleFinal
import SubNLogN.Machine.Layer.LayerMid
import SubNLogN.Machine.Layer.DrvPreHolds
import SubNLogN.Machine.AppC.C6Holds
import SubNLogN.Machine.AppC.C7Final
import SubNLogN.Machine.AppC.C7ExtractHolds
import SubNLogN.Machine.CCore.LeafPhaseFinal
import SubNLogN.Machine.CCore.LeafRowAdd

/-!
# Interchange and Walsh-middle fields of `KernelCut4` (`Machine/T4aHolds.lean`)

Paper: Theorem 6.5 (`thm:direct-fft`), Corollary 6.6 (`cor:walsh-middle`), and Lemma A.8 (`lem:transfer12`).
(`T4a`, `c6`, `c7`, and `AppC` are historical names from an earlier draft for Lemmas A.8 (`lem:transfer12`) and A.9 (`lem:transfer13`), kept for stability.)
* `walshMiddle_holds : WalshMiddleMachineStmt (midLayerParams row46Layer 1)`:
  `walshMiddle_of_open` (`FFT/WalshMiddleFinal.lean`) applied to
  `Layer.layerMachine_mid_of_remaining` (`Layer/LayerMid.lean`) with
  - the phase leaf `CCore.phase_holds` (`CCore/LeafPhaseFinal.lean`);
  - the row addition `CCore.rowAdd_of_c7` (`CCore/LeafRowAdd.lean`) from Lemma A.9
    (`lem:transfer13`), `c7PackedXor_mid_of_open c6_holds c7Extract_holds` (`AppC/C7Final.lean`,
    `AppC/C6Holds.lean`, `AppC/C7ExtractHolds.lean`), and `midLayerParams_OK 1 row46Layer_OK`;
  - the driver pre-phase `Layer.drvPre_mid_holds` (`Layer/DrvPreHolds.lean`);
* `t4aFields_holds : C6InterchangeStmt ((Row46.tau : ℚ) : ℝ) ∧
  WalshMiddleMachineStmt (midLayerParams row46Layer 1)`, with `c6_holds` (Lemma A.8) for the first
  field (the same Lemma A.8 proof feeds the Lemma A.9 packed addition above).
-/

namespace SubNLogN.Machine

open SubNLogN.Assembly

/-- **The Walsh middle at `midLayerParams row46Layer 1`** (`KernelCut4.walshMiddle`,
Corollary 6.6 (`cor:walsh-middle`)), with no hypotheses. -/
theorem walshMiddle_holds : WalshMiddleMachineStmt (midLayerParams row46Layer 1) :=
  walshMiddle_of_open (Layer.layerMachine_mid_of_remaining (CCore.phase_holds _)
    (CCore.rowAdd_of_c7 _ (c7PackedXor_mid_of_open c6_holds c7Extract_holds)
      (midLayerParams_OK 1 row46Layer_OK))
    Layer.drvPre_mid_holds)

/-- **The interchange and Walsh-middle fields of `KernelCut4`** (`c6`, `walshMiddle`), no hypotheses. -/
theorem t4aFields_holds :
    C6InterchangeStmt ((SubNLogN.Math.Cost.Row46.tau : ℚ) : ℝ) ∧
      WalshMiddleMachineStmt (midLayerParams row46Layer 1) :=
  ⟨c6_holds, walshMiddle_holds⟩

end SubNLogN.Machine
