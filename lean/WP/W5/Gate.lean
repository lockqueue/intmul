import IntMulTM.Gate
import WP.W5.Bound
import WP.W5.Main
import WP.W5.Smoke

/-!
# WP.W5.Gate — G1 gate on the W5 package

Every constant of every `WP.W5.*` module, and the cones of the two exported theorems.
-/

#intmul_gate_modules WP.W5
#intmul_gate_check [WP.W5.W5_T3_bound_holds, WP.W5.W5_toom3Mul_holds]
