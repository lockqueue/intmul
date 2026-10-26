import IntMulTM.Gate
import WP.TapeConv.Main
import WP.TapeConv.Smoke

/-!
# WP.TapeConv.Gate — G1 gate for the table-tape converter
-/

#intmul_gate_modules WP.TapeConv

#intmul_gate_check [WP.TapeConv.TapeConv_holds, WP.TapeConv.TapeConv_snapshot,
  WP.TapeConv.TapeConv_snapshotSchedule, WP.TapeConv.conv_runs, WP.TapeConv.conv_embed,
  WP.TapeConv.tapeSyms_length_le, WP.TapeConv.tapeSyms_length_le',
  WP.TapeConv.tapeSyms_length_le_snapshot, WP.TapeConv.convP_closed]
