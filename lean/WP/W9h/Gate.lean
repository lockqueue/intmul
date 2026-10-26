import IntMulTM.Gate
import WP.W9h.RecMain

/-!
# WP.W9h.Gate — G1 gate for W9h (`W9_reconstruct` and the shared host layer)
-/

namespace WP.W9h

open TMFw.Contracts

/-- `W9_reconstruct` in the binding shape of `WP.W9comp.W9StageThms`. -/
theorem W9_reconstruct_binding : W3_all → W4_all → W6a_all → W9_reconstruct :=
  fun h3 _ _ => W9_reconstruct_holds h3

#assert_std_axioms W9_reconstruct_binding

end WP.W9h

#intmul_gate_modules WP.W9h

#intmul_gate_check [WP.W9h.W9_reconstruct_holds, WP.W9h.W9_reconstruct_binding,
  WP.W9h.runs_of_HT, WP.W9h.exists_kit, WP.W9h.horner_carryRun_zero, WP.W9h.Kit.HT_recProg,
  WP.W9h.HT.cdLoop, WP.W9h.loopCost_amort]
