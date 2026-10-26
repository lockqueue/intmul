import IntMulTM.Gate
import WP.W9f.Binding

/-!
# WP.W9f.Gate — G1 gate for W9f (column-solver composition)
-/

#intmul_gate_modules WP.W9f

#intmul_gate_check [WP.W9f.W9_columnSolve_of_cores, WP.W9f.W9_columnSolve_holds,
  WP.W9f.W9_columns_holds]
