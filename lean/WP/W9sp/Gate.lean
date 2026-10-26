import IntMulTM.Gate
import WP.W9sp.Main
import WP.W9sp.Smoke

/-!
# WP.W9sp.Gate — G1 trust gate for `W9_splitPack`

Module mode over every `WP.W9sp.*` module, plus the cone of `W9_splitPack_holds`
(hypothesis `W3_all`, the W9 convention; used: copy, drop, splitAt, shlConst 2, shlVar, isZero,
dec, dec_amortised).
-/

#intmul_gate_modules WP.W9sp

#intmul_gate_check [WP.W9sp.W9_splitPack_holds]
