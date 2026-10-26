import WP.W9e.All
import WP.W9e.SmokeRun
import IntMulTM.Gate

/-!
# WP.W9e.Gate — G1 trust gate for the W9e work package

* Module mode: every constant of every `WP.W9e.*` module.
* Declaration mode: the cones of the main theorems.

The main theorems take the W4 contracts (`W4_transpose .down .down`, `W4_oddStrideFactor`,
`W4_oddRoute .down .down`) and the W3 contracts (`W3_shlVar`, `W3_splitAt`, `W3_subNat`,
`W3_cmpNat`) as explicit hypotheses; `W9e_holds` takes the bundles `W3_all`, `W4_all`.
-/

#intmul_gate_modules WP.W9e

#intmul_gate_check [WP.W9e.W9_postTranspose_holds, WP.W9e.W9_columnRoutes_holds,
  WP.W9e.W9_postOutput_holds, WP.W9e.W9e_holds]
