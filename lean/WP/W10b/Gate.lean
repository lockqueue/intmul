import IntMulTM.Gate
import WP.W10b.Main
import WP.W10b.Tape
import WP.W10b.Smoke

/-!
# WP.W10b.Gate — G1 gate for W10b (W9 cost shape)
-/

#intmul_gate_modules WP.W10b

#intmul_gate_check [WP.W10b.w9_cost_le, WP.W10b.w9_bounds, WP.W10b.w7_tape_le,
  WP.W10b.pipeBound_eq_slots]
