import WP.F9.Run
import WP.F9.PostRun
import WP.F9.W5Run
import WP.F9.Top
import WP.F9.SpecCheck
import WP.F9.PipeRun
import WP.F9.MulLeafRun
import WP.F9.StepRun
import WP.F9.PostLevelRun
import WP.F9.StepPipeRun
import IntMulTM.Gate

/-!
# WP.F9.Gate — G1 trust gate for the F9 package (Phase F)

* Module mode: every constant of every `WP.F9.*` module.
* Declaration mode: the runner's correctness theorems. The code table is the framework machine
  (`tabled_eq`), and the runners are sound and complete w.r.t. `Eval`/`machine_run`
  (`runTabledIxR` given an identity register normalizer). Also the `P9C` facts of `WP.F9.Top`.
-/

#intmul_gate_modules WP.F9

#intmul_gate_check [WP.F9.tabled_eq, WP.F9.runTabled_sound, WP.F9.runTabled_of_eval,
  WP.F9.runTabledIx_sound, WP.F9.runTabledIx_of_eval, WP.F9.runTabledIxR_sound,
  WP.F9.runTabledIxR_of_eval, WP.Inst.toomMul_closed, WP.F9.Top.hm9, WP.F9.Top.m9_eq,
  WP.F9.Top.closedC, WP.F9.Top.nr9_eq]
