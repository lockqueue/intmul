import WP.W9a.Final
import WP.W9a.Smoke
import IntMulTM.Gate

/-!
# WP.W9a.Gate — G1 trust gate for the W9a work package

* Module mode: every constant of every `WP.W9a.*` module.
* Declaration mode: the cones of the main theorems.

The level programs take the node-kernel contracts (and `W9_sweep`, `W9_retMark`, `W9_retFlip`) as
explicit hypotheses; `W9_pipeline_of_kernels` discharges all but the three kernels.
-/

#intmul_gate_modules WP.W9a

#intmul_gate_check [WP.W9a.W9_sweep_holds, WP.W9a.W9_level_holds, WP.W9a.W9_retFlip_holds,
  WP.W9a.W9_preLevelProg_holds, WP.W9a.W9_leafLevelProg_holds, WP.W9a.W9_postLevelProg_holds,
  WP.W9a.W9_levels_of_kernels_holds, WP.W9a.W9_pipeline_of_levels_holds,
  WP.W9a.W9_pipeline_of_kernels]
