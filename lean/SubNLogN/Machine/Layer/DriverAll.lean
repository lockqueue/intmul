/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.Driver
import SubNLogN.Machine.Layer.DrvMathCost
import SubNLogN.Machine.Layer.DrvMathCtx
import SubNLogN.Machine.Layer.DrvFunctional

/-!
# Layer driver, part 3: assembly with the proved math leaves (`Machine/Layer/DriverAll.lean`)

**Scope (honest summary).** `layerMachine_of_kernels`: for admissible constants `p` (`p.OK`), the
C-core contract at every rational leaf exponent and the two driver kernels give
`LayerMachineStmt p`. The leaf exponent `βn/βd` is chosen by `exists_drvBeta` (`Math/Cost/Recurrence.lean`). The three math
statements of the driver are discharged by `drvFunctional_holds`, `drvCtx_holds` and
`drvCost_holds`. Proved without `sorry`. The open hypotheses are exactly `CCoreStmt` (at every
`βn, βd`; it carries its own admissibility premises), `DrvPreStmt` and `DrvPostStmt`.
-/

namespace SubNLogN.Machine.Layer

/-- **Proposition A.11's machine part from the kernels.** For admissible `p`, if the C-core
contract holds at every rational leaf exponent and the driver's pre- and post-phase kernels exist,
then `LayerMachineStmt p` holds. -/
theorem layerMachine_of_kernels (p : LayerParams) (hOK : p.OK)
    (hcore : ∀ βn βd : ℕ, CCoreStmt p βn βd) (hpre : DrvPreStmt p) (hpost : DrvPostStmt p) :
    LayerMachineStmt p := by
  obtain ⟨βn, βd, hβn, hβd, -, hσ, hτ⟩ := exists_drvBeta p hOK
  exact layerMachine_of_parts p βn βd hOK hβn hβd hτ (hcore βn βd) hpre hpost
    (drvFunctional_holds p) (drvCtx_holds p hOK βn βd) (drvCost_holds p hOK βn βd hσ)

end SubNLogN.Machine.Layer
