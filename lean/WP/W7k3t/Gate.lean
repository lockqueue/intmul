import IntMulTM.Gate
import WP.W7k3t.Tap
import WP.W7k3t.Smoke

/-!
# WP.W7k3t.Gate — G1 gate for W7k3t (the table series kernel `W7_sincGaussianTap`)
-/

#intmul_gate_modules WP.W7k3t

#intmul_gate_check [WP.W7k3t.W7_sincGaussianTap_holds, WP.W7k3t.W7_sincGaussianTap_bind,
  WP.W7k3t.tapC_eq_tapV, WP.W7k3t.topProg_spec]
