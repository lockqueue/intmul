import WP.W4.Main
import WP.W4.Smoke
import IntMulTM.Gate

/-!
# WP.W4.Gate — G1 trust gate for the W4 transpose work package

* Module mode: every constant of every `WP.W4.*` module.
* Declaration mode: the cones of the main theorems.

No contract hypotheses: `W4_transpose_holds` is unconditional.
-/

#intmul_gate_modules WP.W4

#intmul_gate_check [TMFw.W4.W4_transpose_holds, TMFw.W4.W4_transpose_down_up,
  TMFw.W4.W4_transpose_down_down]
