import IntMulTM.Gate
import WP.W7k3.Bind
import WP.W7k3.Smoke
import WP.W7k3.ConcreteRun

/-!
# WP.W7k3.Gate — G1 gate for W7k3 (the series sub-kernel)
-/

#intmul_gate_modules WP.W7k3

#intmul_gate_check [WP.W7k3.W7S_series_holds, WP.W7k3.W7S_series_bind, WP.W7k3.serInst_spec,
  WP.W7k3.serProg_spec, WP.W7k3.serLoop_spec, WP.W7k3.serBody_spec, WP.W7k3.serSetup_spec,
  WP.W7k3.serEnd_spec, WP.W7k3.serW_ends, WP.W7k3.HT.user, WP.W7k3.exists_ser,
  WP.W7k3.serProg_closed, WP.W7k3.SK.erf_OK, WP.W7k3.SK.erf_f, WP.W7k3.SK.erf_g,
  WP.W7k3.Concrete.progC, WP.W7k3.Concrete.closedC, WP.W7k3.Concrete.serC]
