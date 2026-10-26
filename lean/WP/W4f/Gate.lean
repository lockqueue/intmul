import IntMulTM.Gate
import WP.W4f.Top
import WP.W4f.Smoke

/-!
# WP.W4f.Gate — G1 trust gate for work package W4f

Module mode over every `WP.W4f.*` module, plus the cone of the contract theorem
`W4_oddStrideFactor_holds` (no hypotheses).
-/

#intmul_gate_modules WP.W4f

#intmul_gate_check [WP.W4f.W4_oddStrideFactor_holds]
