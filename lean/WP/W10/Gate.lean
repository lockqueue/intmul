import IntMulTM.Gate
import WP.W10.Cost
import WP.W10.Smoke

/-!
# WP.W10.Gate — G1 gate for W10 (global cost theorem)
-/

#intmul_gate_modules WP.W10

#intmul_gate_check [WP.W10.W10_cost_holds, WP.W10.total_le, WP.W10.level_mul_le]
