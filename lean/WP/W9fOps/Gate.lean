import IntMulTM.Gate
import WP.W9fOps.LeInd
import WP.W9fOps.MulPow2
import WP.W9fOps.ShrFloor
import WP.W9fOps.Smoke

/-!
# WP.W9fOps.Gate — G1 trust gate for the W9f machine operations

Module mode over every `WP.W9fOps.*` module, plus the cones of the three operation theorems.
`shrFloor_holds` takes `W3_shrVar`, `mulPow2_holds` takes `W3_shlVar` (open W3 contracts, as
agreed with W9f); `leInd_holds` has no hypotheses.
-/

#intmul_gate_modules WP.W9fOps

#intmul_gate_check [WP.W9fOps.shrFloor_holds, WP.W9fOps.mulPow2_holds, WP.W9fOps.leInd_holds]
