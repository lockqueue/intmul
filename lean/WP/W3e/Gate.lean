import IntMulTM.Gate
import WP.W3e.Shift
import WP.W3e.Smoke

/-!
# WP.W3e.Gate — G1 gate for W3e (constant shifts)
-/

#intmul_gate_modules WP.W3e

#intmul_gate_check [WP.W3e.W3_shlConst_holds, WP.W3e.W3_shrConst_holds, WP.W3e.shlProg_eval,
  WP.W3e.shrProg_eval, WP.W3e.natSyms_mul_two_pow, WP.W3e.natSyms_half]
