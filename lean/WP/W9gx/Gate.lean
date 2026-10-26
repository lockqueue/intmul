import WP.W9gx.Final
import IntMulTM.Gate

/-!
# WP.W9gx.Gate — G1 trust gate for the W9gx package (LEAF bridge and contract)

* Module mode: every constant of every `WP.W9gx.*` module.
* Declaration mode: the cone of `W9_leafFFT_holds` (W9g's kernel included).
-/

#intmul_gate_modules WP.W9gx

#intmul_gate_check [WP.W9gx.W9_leafFFT_holds, WP.W9gx.W9_leafFFT_of_top, WP.W9gx.leaf_toList,
  WP.W9gx.core_toList, WP.W9gx.fftW_of_leafCoreW, WP.W9gx.leafCost_le]
