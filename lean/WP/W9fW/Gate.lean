import IntMulTM.Gate
import WP.W9fW.AltSum
import WP.W9fW.Smoke

/-!
# WP.W9fW.Gate — G1 gate for W9fW (width lemmas of the W9f column solvers)
-/

#intmul_gate_modules WP.W9fW

#intmul_gate_check [WP.W9fW.zPartFwdBarrett_entryW, WP.W9fW.zHomFwdBarrett_entryW,
  WP.W9fW.zPartNyqBarrett_entryW, WP.W9fW.zPartFwdBarrett_abs_le, WP.W9fW.zHomFwdBarrett_abs_le,
  WP.W9fW.zPartNyqBarrett_abs_le, WP.W9fW.zPartFwdBarrett_arrW, WP.W9fW.zHomFwdBarrett_arrW,
  WP.W9fW.zPartNyqBarrett_arrW, WP.W9fW.altSum_abs_le, WP.W9fW.altSum_abs_lt,
  WP.W9fW.recStepBarrett_entryW, WP.W9fW.abs_divRoundRatInt_le]
