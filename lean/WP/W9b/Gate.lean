import WP.W9b.Transpose
import WP.W9b.Smoke
import IntMulTM.Gate

/-!
# WP.W9b.Gate — G1 trust gate for the W9b work package

* Module mode: every constant of every `WP.W9b.*` module.
* Declaration mode: the cones of the main theorems.

`W9_preTranspose_holds` takes `W4_transpose .down .up` and `W9_altSum_holds` takes `W3_addInt`,
`W3_subInt`, `W3_addNat`, `W3_subNat`, `W3_shlVar`, `W3_shrVar` as explicit hypotheses.
`W9_emitRows_holds` has none.
-/

#intmul_gate_modules WP.W9b

#intmul_gate_check [WP.W9b.W9_emitRows_holds, WP.W9b.W9_preTranspose_holds,
  WP.W9b.W9_altSum_holds]
