import IntMulTM.Gate
import WP.W9ex.Extract
import WP.W9ex.Smoke

/-!
# WP.W9ex.Gate — G1 trust gate for the W9 extract kernel

Module mode covers every constant of every `WP.W9ex.*` module (Kit, Macros, State, Digit, Loop,
Phases, Cost, Main, Value, Extract, Smoke). Declaration mode covers the cones of the main theorems.
-/

#intmul_gate_modules WP.W9ex

#intmul_gate_check [WP.W9ex.W9_extract_proved, WP.W9ex.W9_extract_holds,
  WP.W9ex.W9_extract_binding, WP.W9ex.xt_extract]
