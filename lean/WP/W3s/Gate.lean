import IntMulTM.Gate
import WP.W3s.Split
import WP.W3s.Concat
import WP.W3s.Smoke

/-!
# WP.W3s.Gate — G1 trust gate for work package W3s

Module mode over every `WP.W3s.*` module, plus the cones of the four contract theorems (all
without hypotheses).
-/

#intmul_gate_modules WP.W3s

#intmul_gate_check [TMFw.W3s.W3_splitAt_holds, TMFw.W3s.W3_shlVar_holds,
  TMFw.W3s.W3_shrVar_holds, TMFw.W3s.W3_concatAt_holds]
