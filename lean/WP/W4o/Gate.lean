import IntMulTM.Gate
import WP.W4o.OddRoute
import WP.W4o.Smoke

/-!
# WP.W4o.Gate — G1 trust gate for work package W4o

Module mode over every `WP.W4o.*` module, plus the cone of the contract theorem
`W4_oddRoute_holds : W4_oddRoute .down .down` (no hypotheses).
-/

#intmul_gate_modules WP.W4o

#intmul_gate_check [TMFw.W4o.W4_oddRoute_holds]
