import IntMulTM.Gate
import WP.W7k1.Canon
import WP.W7k1.Isqrt
import WP.W7k1.IsqrtOp
import WP.W7k1.Bounds
import WP.W7k1.Smoke
import WP.W7k1.Pi
import WP.W7k1.Ln

/-!
# WP.W7k1.Gate — G1 gate for W7k1 (isqrt, π and ln 2 kernels)
-/

#intmul_gate_modules WP.W7k1

#intmul_gate_check [WP.W7k1.W7_isqrt_holds, WP.W7k1.isqrtProg_eval, WP.W7k1.sqRun_padMSB,
  WP.W7k1.isqOp_runs, WP.W7k1.piNat_eq, WP.W7k1.piRef_eq, WP.W7k1.piIter_le, WP.W7k1.piWidths,
  WP.W7k1.log2Nat_eq, WP.W7k1.log2Ref_eq, WP.W7k1.lnWidths, WP.W7k1.HT.cdLoopLt,
  WP.W7k1.piProg_spec, WP.W7k1.W7_piScaled_holds, WP.W7k1.lnX_succ, WP.W7k1.lnProg_spec,
  WP.W7k1.W7_log2Scaled_holds]
