import IntMulTM.Gate
import WP.W9sq.Theorem
import WP.W9sq.Smoke

/-!
# WP.W9sq.Gate — G1 gate for W9sq (the W9 root kernel `W9_square`)
-/

#intmul_gate_modules WP.W9sq

#intmul_gate_check [WP.W9sq.W9_square_holds, WP.W9sq.W9_square_holds',
  WP.W9sq.W9_square_holds_min, WP.W9sq.W9_square_core, WP.W9sq.sq_spec, WP.W9sq.entry_spec,
  WP.W9sq.loop_spec, WP.W9sq.rootSquareV_toList, WP.W9sq.rnd_re, WP.W9sq.rnd_im]
