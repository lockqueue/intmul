import IntMulTM.Gate
import WP.W9fF.Main
import WP.W9fF.Ops

/-!
# WP.W9fF.Gate — G1 trust gate for W9fF (S1, the forward column core)

Module mode over every `WP.W9fF.*` module, plus the cones of the main theorems.
-/

#intmul_gate_modules WP.W9fF

#intmul_gate_check [WP.W9fF.W9f_fwdCore_holds, WP.W9fF.core_runs, WP.W9fF.loop1_triple,
  WP.W9fF.bndLoop2_triple, WP.W9fF.setupStart_triple, WP.W9fF.teardown_triple,
  WP.W9fF.mainProg_closed, WP.W9fF.sBnd_sound, WP.W9fF.orc_sound, WP.W9fF.IL.compile_correct,
  WP.W9fF.pStepF_cost, WP.W9fF.ev_pStepF, WP.W9fF.ev_pBnd, WP.W9fF.ev_pComb,
  WP.W9fF.kit_exists_W3, WP.W9fF.opsOK_exists]
