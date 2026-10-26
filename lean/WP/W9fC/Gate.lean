import IntMulTM.Gate
import WP.W9fC.Main
import WP.W9fC.Smoke
import WP.W9fC.SmokeFin

/-!
# WP.W9fC.Gate — G1 gate for W9fC (`W9_columns_of_columnSolve`, sub-kernel S3)
-/

#intmul_gate_modules WP.W9fC

#intmul_gate_check [WP.W9fC.W9_columns_of_columnSolve, WP.W9fC.runs_cols, WP.W9fC.runs_setup,
  WP.W9fC.runs_colLoop, WP.W9fC.runs_colBody, WP.W9fC.runs_cntLoop, WP.W9fC.runs_call,
  WP.W9fC.runs_finish, WP.W9fC.cost_total_le, WP.W9fC.colsProg_closed]
