/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.PartsDefs
import SubNLogN.Machine.CCore.MathM1Holds
import SubNLogN.Machine.CCore.MathM2
import SubNLogN.Machine.CCore.MathM3
import SubNLogN.Machine.CCore.MathM4
import SubNLogN.Machine.CCore.MathM6
import SubNLogN.Machine.CCore.NodeCodeCount
import SubNLogN.Machine.CCore.LeafSplitAux
import SubNLogN.Math.Networks.Proofs.AppCFinal

/-!
# C-core skeleton: the mathematical inputs (`CCore/MathInputs.lean`)

Proves `cCoreMathInputs_holds p βn βd : CCoreMathInputs p βn βd` (`CCore/PartsDefs.lean`) for all
`p βn βd`, with no hypotheses. It is pure assembly of proved theorems:
* valid complex edge data `cdat`: `AppCFinalAux.existsValidCxData_holds`
  (`Math/Networks/Proofs/AppCFinal.lean`);
* the mathematical leaves `CCoreMathLeaves p βn βd cdat` (`CCore/SkelMathDefs.lean`):
  (M1) `nodeValue_holds` (`MathM1Holds.lean`), (M2) `nodeGrowth_holds` (`MathM2.lean`),
  (M3) `costRec_holds` (`MathM3.lean`), (M4) `childBands_holds` (`MathM4.lean`),
  (M5) `nodeChildCount_holds` (`NodeCodeCount.lean`), (M6a) `encLen_holds` (`MathM6.lean`),
  (M6b) `hdrLen_holds` (`LeafSplitAux.lean`);
* Value-level network premises: `complexNetCert_holds` (`H2Final.lean`), `runEightSpec_holds`
  (`AppCLeaves.lean`), `packedAgree_holds` (`PackedAgree.lean`), `packedProcCorrect_holds`
  (`PackedProc.lean`), `translationConj_holds` (`AppCLayerAlg.lean`).

The consumer is `cCore_of_inputs` in `CCore/Parts.lean`.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-- **The mathematical inputs of the C-core reduction hold**, for every `p βn βd`. The leaves
(M1)–(M6) are instantiated at the certified edge data, with network premises from `Math/Networks/Proofs/`. -/
theorem cCoreMathInputs_holds (p : LayerParams) (βn βd : ℕ) : CCoreMathInputs p βn βd := by
  obtain ⟨cdat, hval⟩ := AppCFinalAux.existsValidCxData_holds
  exact ⟨cdat, hval, ⟨nodeValue_holds cdat, nodeGrowth_holds cdat βn βd, costRec_holds p βn βd,
      childBands_holds p, nodeChildCount_holds cdat, encLen_holds p, hdrLen_holds p⟩,
    complexNetCert_holds, runEightSpec_holds, packedAgree_holds, packedProcCorrect_holds,
    translationConj_holds⟩

end SubNLogN.Machine.CCore
