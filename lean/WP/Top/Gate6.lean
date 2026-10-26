import IntMulTM.Gate
import WP.Top.Current6

/-!
# WP.Top.Gate6 — G1 gate for Current6

This is separate from `WP.Top.Gate` because Current6 imports the worker snapshots (W3s, W9a, W9b,
W9e). Declaration mode covers the whole cone of `intMul_TM2_nlogn_current6`, snapshot theorems
included.
-/

#intmul_gate_modules WP.Top

#intmul_gate_check [WP.Top.intMul_TM2_nlogn_current6, WP.Top.W3_all_holds,
  WP.Top.intMul_TM2_nlogn_current4]
