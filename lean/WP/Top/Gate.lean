import IntMulTM.Gate
import WP.Top.Main
import WP.Top.Smoke
import WP.Top.Remaining2
import WP.Top.TapeConvBridge
import WP.Top.Current3
import WP.Top.Current4

/-!
# WP.Top.Gate — G1 gate for the top-level composition
-/

#intmul_gate_modules WP.Top

#intmul_gate_check [WP.Top.intMul_TM2_nlogn_of_stages, WP.Top.top_triple, WP.Top.outStage_triple,
  WP.Top.glue_eval, WP.Top.topCosts_bounds, WP.Top.topProg_closed, WP.Top.mulBound_of_T3,
  WP.Top.eventually_supCost, WP.Top.W9CostShape_of_W10b, WP.Top.intMul_TM2_nlogn_of_remaining2, WP.Top.TapeConv_proved,
  WP.Top.intMul_TM2_nlogn_current3, WP.Top.intMul_TM2_nlogn_current4]
