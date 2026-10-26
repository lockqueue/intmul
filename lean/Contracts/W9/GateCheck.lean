import Contracts.W9.Pipeline
import IntMulTM.Gate

/-!
# Contracts.W9.GateCheck — G1 trust gate over the W9 contracts package

Module mode checks every constant of every `Contracts.W9.*` module. Declaration mode checks the
cones of the proved theorems.
-/

#intmul_gate_modules Contracts.W9

#intmul_gate_check [TMFw.Contracts.W9.entrySyms_recOK, TMFw.Contracts.W9.length_blkE_le,
  TMFw.Contracts.W9.postRecSyms_recOK, TMFw.Contracts.W9.tapeSyms_step_head,
  TMFw.Contracts.W9.tapeSyms_base_head, TMFw.Contracts.symTags_distinct,
  TMFw.Contracts.W9.preNodeV_eq_phases, TMFw.Contracts.W9.altNodeV_eq_phase,
  TMFw.Contracts.W9.w9UStatic_eq, TMFw.Contracts.W9.postNodeV_eq_phases,
  TMFw.Contracts.W9.w9ZBarrett_eq_exact, TMFw.Contracts.W9.computableOddStrideFactor_bridge,
  TMFw.Contracts.w9_retMark, TMFw.Contracts.w9_retPush, TMFw.Contracts.w9_rqPop,
  TMFw.Contracts.W9.multiply_eq_root_phases, TMFw.Contracts.W9.genEval_opsOf,
  TMFw.Contracts.W9.pipeline_out_eq_map, TMFw.Contracts.W9.symGuard_fresh,
  TMFw.Contracts.W9.groupSyms_eq_matSyms, TMFw.Contracts.W9.length_tapeSyms]
