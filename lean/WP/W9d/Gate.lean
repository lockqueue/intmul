import IntMulTM.Gate
import WP.W9d.Final
import WP.W9d.Smoke

/-!
# WP.W9d.Gate — G1 trust gate for the W9d twists

Module mode covers every constant of every `WP.W9d.*` module (Basic, Inst, TwistPure, EntryA,
EntryB, Entry, Loops, Mat, Kernel, CostPure, Twist, Final, Smoke). Declaration mode covers the
cones of the main theorems.
-/

#intmul_gate_modules WP.W9d

#intmul_gate_check [WP.W9d.W9_preTwist_holds, WP.W9d.W9_postTwist_holds,
  WP.W9d.W9_preTwist_core, WP.W9d.W9_postTwist_core, WP.W9d.twist_holds, WP.W9d.entry_spec,
  WP.W9d.kernel_spec]
