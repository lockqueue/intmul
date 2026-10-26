import WP.W9fDiv.Holds
import WP.W9fDiv.OfSub
import WP.W9fDiv.Smoke
import IntMulTM.Gate

/-!
# WP.W9fDiv.Gate — G1 trust gate for the W9fDiv work package

* Module mode: every constant of every `WP.W9fDiv.*` module.
* Declaration mode: the cones of the main theorems.
-/

#intmul_gate_modules WP.W9fDiv

#intmul_gate_check [WP.W9fDiv.W9fDiv_holds, WP.W9fDiv.W9fDiv_holds_of_sub,
  WP.W9fDiv.divRound_bridge]
