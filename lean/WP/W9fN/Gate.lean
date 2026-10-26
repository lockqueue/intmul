import IntMulTM.Gate
import WP.W9fN.Main
import WP.W9fN.MainW3
import WP.W9fN.Smoke

/-!
# WP.W9fN.Gate — G1 gate for W9fN (the Nyquist column core `W9f_nyqCore`)
-/

#intmul_gate_modules WP.W9fN

#intmul_gate_check [WP.W9fN.W9f_nyqCore_of, WP.W9fN.W9f_nyqCore_of_finish, WP.W9fN.opsHyp_of_W3,
  WP.W9fN.nyqProg_runs, WP.W9fN.nyqCost_le,
  WP.W9fN.nyqProg_closed, WP.W9fN.inLoop_triple, WP.W9fN.inBody_step, WP.W9fN.prologue_runs,
  WP.W9fN.post_triple, WP.W9fN.Lay.hst_compile, WP.W9fN.whileEnt_triple,
  WP.W9fN.Lay.popEntry_runs, WP.W9fN.Lay.pushEntry_runs, WP.W9fN.kit_exists]
