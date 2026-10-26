import IntMulTM.Gate
import WP.Inst.W3
import WP.Inst.W3Ok
import WP.Inst.W4
import WP.Inst.W6a
import WP.Inst.W7k1
import WP.Inst.Smoke2
import WP.Inst.Smoke

/-!
# WP.Inst.Gate — G1 gate for the W3 instance module
-/

#intmul_gate_modules WP.Inst

#intmul_gate_check [WP.Inst.copyNat.ok, WP.Inst.cmpNat.ok, WP.Inst.isZeroNat.ok, WP.Inst.incNat.ok,
  WP.Inst.decNat.ok, WP.Inst.natToInt.ok, WP.Inst.splitSign.ok, WP.Inst.addNat.ok, WP.Inst.subNat.ok,
  WP.Inst.dropNat.ok, WP.Inst.normNat.ok, WP.Inst.splitAt.ok, WP.Inst.concatAt.ok,
  WP.Inst.shlConst.ok, WP.Inst.shrConst.ok, WP.Inst.shrVar.ok, WP.Inst.shlVar.ok]

#intmul_gate_check [WP.Inst.transpose.ok, WP.Inst.oddStrideFactor.ok, WP.Inst.oddRoute.ok]

#intmul_gate_check [WP.Inst.subNat.subSpec, WP.Inst.divModNat.ok, WP.Inst.divRound.ok,
  WP.Inst.isqrt.ok, WP.Inst.log2Scaled.closed, WP.Inst.piScaled.closed]
