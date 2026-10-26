import IntMulTM.Gate
import WP.W9fBind.Plug

/-!
# WP.W9fBind.Gate — G1 trust gate for the column-solver binding
-/

#intmul_gate_modules WP.W9fBind

#intmul_gate_check [WP.W9fBind.W9_columns_holds_final, WP.W9fBind.W9_columnSolve_all,
  WP.W9fBind.W9_columns_final, WP.W9fBind.W9_columnSolve_final]
