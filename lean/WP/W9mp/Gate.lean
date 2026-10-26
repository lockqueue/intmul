import IntMulTM.Gate
import WP.W9mp.Main
import WP.W9mp.Smoke

/-!
# WP.W9mp.Gate — G1 trust gate for the root composite

Module mode covers every constant of every `WP.W9mp.*` module (Glue, GlueP0, Prog, Main, Smoke).
Declaration mode covers the cone of the main theorem.
-/

#intmul_gate_modules WP.W9mp

#intmul_gate_check [WP.W9mp.W9_multiply_of_parts_holds]
