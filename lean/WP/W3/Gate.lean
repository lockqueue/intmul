import IntMulTM.Gate
import WP.W3.AddSub
import WP.W3.Misc
import WP.W3.Smoke

/-!
# WP.W3.Gate — G1 trust gate for work package W3 (unsigned arithmetic)

Module mode over every `WP.W3.*` module, plus the cones of the eleven contract theorems. All are
stated without hypotheses.
-/

#intmul_gate_modules WP.W3

#intmul_gate_check [WP.W3.W3_addNat_holds, WP.W3.W3_subNat_holds, WP.W3.W3_normNat_holds,
  WP.W3.W3_dropNat_holds, WP.W3.W3_copyNat_holds, WP.W3.W3_cmpNat_holds,
  WP.W3.W3_isZeroNat_holds, WP.W3.W3_incNat_holds, WP.W3.W3_decNat_holds,
  WP.W3.W3_natToInt_holds, WP.W3.W3_splitSign_holds]
