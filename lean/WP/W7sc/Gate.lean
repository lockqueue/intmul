import IntMulTM.Gate
import WP.W7sc.Inst
import WP.W7sc.Smoke

/-!
# WP.W7sc.Gate — G1 gate on the W7sc package

Every constant of every `WP.W7sc.*` module, and the cones of the exported theorems.
-/

#intmul_gate_modules WP.W7sc
#intmul_gate_check [WP.W7sc.W7_stdChar_holds, WP.W7sc.scInst_spec]
