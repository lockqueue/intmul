import IntMulTM.Gate
import WP.W7pure.TapeSize
import WP.W7pure.EntryWidths
import WP.W7pure.TableCost
import WP.W7pure.TapeBound
import WP.W7pure.Smoke

/-!
# WP.W7pure.Gate — G1 gate for W7-pure (the pure W7 table obligations)
-/

#intmul_gate_modules WP.W7pure

#intmul_gate_check [WP.W7pure.W7_entryWidths_of_faithful_holds, WP.W7pure.W7_tapeSize_holds,
  WP.W7pure.W7_tableCost_sqrt_holds, WP.W7pure.W7_tapeBound_sqrt_holds]
