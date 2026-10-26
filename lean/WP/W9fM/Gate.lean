import WP.W9fM.Holds
import WP.W9fM.Smoke
import IntMulTM.Gate

/-!
# WP.W9fM.Gate — G1 trust gate for the W9fM work package

* Module mode: every constant of every `WP.W9fM.*` module.
* Declaration mode: the cones of the main theorems.
-/

#intmul_gate_modules WP.W9fM

#intmul_gate_check [WP.W9fM.W9f_moveEntries_holds, WP.W9fM.moveEntries_holds]
