import IntMulTM.Gate
import WP.W14.Headline
import WP.W14.SnapshotSlots
import WP.W14.Smoke

/-!
# W14 gate

Module mode over every `WP.W14.*` module, and declaration mode over the W14 headline theorems.
-/

#intmul_gate_modules WP.W14

#intmul_gate_check [WP.W14.computablePaperFastDFTMultiply_faithful_eq_mul_paper,
  WP.W14.computablePaperFastDFTMultiply_faithful_eq_mul_at,
  WP.W14.paperSchedule_admissible,
  WP.W14.buildQuantizedSpecPaperStop_paperStopValid,
  WP.W14.idealRoundedTablesAt_paperSpec_faithful,
  WP.W14.paperMultiply_idealTables_eq_mul,
  WP.W14.computablePaperFastDFTMultiply_faithful_eq_mul_via_W14,
  WP.W14.tablesFaithfulAt_snapshot_iff,
  WP.W14.computablePaperFastDFTMultiplyAt_snapshot,
  WP.W14.sincGaussianFastDFTOfTablesAt_snapshot]
