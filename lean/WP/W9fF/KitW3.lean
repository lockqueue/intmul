import WP.W9fF.Kit
import WP.W9fOps.ShrFloor
import WP.W9fOps.MulPow2
import WP.W9fOps.LeInd

/-!
# WP.W9fF.KitW3 — the ops kit from the machine contracts only

`opsHyp_of_W3`: `OpsHyp` from `W3_all` via W9fOps (`shrFloor_holds` from `W3_shrVar`,
`mulPow2_holds` from `W3_shlVar`, `leInd_holds` hypothesis-free); the bodies of `W9fBinOp` /
`W9fShiftOp` are verbatim those of `BinOpH` / `ShiftOpH`.
`kit_exists_W3`: `W5_mulAt Mul → W3_all → W6a_all → Nonempty (Kit Mul)`.
-/

namespace WP.W9fF

open TMFw TMFw.Contracts

theorem opsHyp_of_W3 (h3 : W3_all) : OpsHyp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hshl, hshr, -⟩ := h3
  exact ⟨WP.W9fOps.shrFloor_holds hshr, WP.W9fOps.mulPow2_holds hshl, WP.W9fOps.leInd_holds⟩

theorem kit_exists_W3 (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul) (h3 : W3_all) (h6 : W6a_all) :
    Nonempty (Kit Mul) :=
  kit_exists Mul h5 h3 h6 (opsHyp_of_W3 h3)

#assert_std_axioms opsHyp_of_W3 kit_exists_W3

end WP.W9fF
