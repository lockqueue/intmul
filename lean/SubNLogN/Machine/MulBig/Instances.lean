/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.Top.Current6
import WP.Top.TapeConvBridge
import WP.W7k2.B.Top
import WP.W7k3.StdChar
import WP.W7k3t.Tap
import WP.W7k3c.Final
import WP.W5.Main
import WP.W3b.AddSub
import WP.W3b.SmallOp
import WP.W3s.Split
import WP.W3s.Concat
import WP.W6a.DivMod
import WP.W6a.DivRound
import WP.W4.Main
import WP.W4f.Top
import WP.W4o.OddRoute
import WP.W9a.Level
import WP.W9a.Pipeline
import WP.W9a.Ret
import WP.W9a.Sweep
import WP.W9b.AltSum
import WP.W9b.Emit
import WP.W9b.Transpose
import WP.W9c.Main
import WP.W9comp.PostNode
import WP.W9comp.PreNode
import WP.W9d.Final
import WP.W9e.All
import WP.W9fBind.Plug
import WP.W9gx.Final
import WP.W9s.Main
import WP.W9mp.Main
import WP.W9sp.Main
import WP.W9sq.Theorem
import WP.W9ex.Extract
import WP.W9h.RecMain
import Contracts.W9.Ret
import Contracts.Machine.W4

/-!
# `mulBig` (K0.4): the proved stage contracts of the IntMul pipeline, assembled

Hypothesis-free instances of the stage contracts used by `mulBig`, assembled from the proved WP
kernels with the same terms as `SubNLogN.S5.TopDispatcher.W7_buildTables_proved` and
`SubNLogN.S5.Pipe.w9_pipeline_proved` (re-assembled here so that this directory depends only on
`WP`, `Contracts` and `IntMulTM` modules):
* `w5_toom3Mul_proved : W5_toom3Mul` (Toom-3 on the proved W3 kernels);
* `w7_buildTables_proved : W7_buildTables W7.snapshotSchedule` (the W7 table builder);
* `w4_all_proved : W4_all`;
* `w9_pipeline_proved Mul : W5_mulAt Mul → W9_pipeline Mul` (the radix-2 IntMul transform);
* `w9_multiply_proved Mul : W5_mulAt Mul → W9_multiply Mul` (the root composite: split/pack,
  forward transform, pointwise square, inverse transform, extract, reconstruct).
-/

namespace SubNLogN.Machine.MulBig

open TMFw TMFw.Contracts

/-- Toom-3 multiplication (`W5_toom3Mul`), from the proved W3 kernels. -/
theorem w5_toom3Mul_proved : W5_toom3Mul :=
  WP.W5.W5_toom3Mul_holds
    (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    TMFw.W3b.W3_smallOpInt_holds TMFw.W3s.W3_splitAt_holds TMFw.W3s.W3_shlVar_holds

/-- The W7 table builder for the snapshot schedule, from the proved W3, W5, W6a and W7 leaves. -/
theorem w7_buildTables_proved : W7_buildTables W7.snapshotSchedule :=
  WP.Top.W7_buildTables_of_leaves WP.Top.W3_all_holds
    (WP.W6a.W6a_holds WP.W3.W3_subNat_holds) w5_toom3Mul_proved
    WP.W7k3.W7_stdChar_bind WP.W7k3t.W7_sincGaussianTap_bind WP.W7k3c.W7_c0c1_bind
    WP.W7k2.W7_buildTablesRef_holds

/-- All W4 contracts (transposes, odd-stride factor, odd routing, record moves). -/
theorem w4_all_proved : W4_all :=
  ⟨TMFw.W4.W4_transpose_holds .down .down, WP.W4f.W4_oddStrideFactor_holds,
    TMFw.W4o.W4_oddRoute_holds, w4_moveRecord⟩

/-- The level-synchronous radix-2 IntMul transform `W9_pipeline Mul`, for every `Mul` with
`W5_mulAt Mul`. -/
theorem w9_pipeline_proved (Mul : ℕ → ℕ) (hM : W5_mulAt Mul) : W9_pipeline Mul := by
  have h3 : W3_all := WP.Top.W3_all_holds
  have h4 : W4_all := w4_all_proved
  have h6 : W6a_all := WP.W6a.W6a_holds WP.W3.W3_subNat_holds
  have hAddInt : W3_addInt :=
    TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds
  have hSubInt : W3_subInt :=
    TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds
  have hpre : W9_preNode Mul := WP.W9comp.W9_preNode_of_phases_holds Mul
    (WP.W9b.W9_preTranspose_holds (TMFw.W4.W4_transpose_holds .down .up))
    (WP.W9b.W9_altSum_holds hAddInt hSubInt WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds
      TMFw.W3s.W3_shlVar_holds TMFw.W3s.W3_shrVar_holds)
    (WP.W9c.W9_spread_stage Mul hM h3 h4 h6)
    (WP.W9d.W9_preTwist_holds Mul hM h3 h4 h6)
    (WP.W9s.W9_synFFT_holds hAddInt hSubInt)
    (WP.W9d.W9_postTwist_holds Mul hM h3 h4 h6)
    WP.W9b.W9_emitRows_holds
  have h9e := WP.W9e.W9e_holds h3 h4
  have hpost : W9_postNode Mul := WP.W9comp.W9_postNode_of_phases_holds Mul h9e.1 h9e.2.1
    (WP.W9fBind.W9_columns_holds_final Mul hM h3 h4 h6) h9e.2.2
  have hleaf : W9_leafFFT Mul := WP.W9gx.W9_leafFFT_holds Mul hM hAddInt hSubInt
    TMFw.W3s.W3_shlVar_holds TMFw.W3s.W3_shrVar_holds
  obtain ⟨hpl, hll, hpol⟩ := WP.W9a.W9_levels_of_kernels_holds Mul WP.W9a.W9_sweep_holds
    w9_retMark WP.W9a.W9_retFlip_holds hpre hleaf hpost
  exact WP.W9a.W9_pipeline_of_levels_holds Mul WP.W9a.W9_level_holds hpl hll hpol

/-- The IntMul root composite `W9_multiply Mul` (the multiplier `WP.Top.topProg` runs as its
Stage 5), for every `Mul` with `W5_mulAt Mul`. -/
theorem w9_multiply_proved (Mul : ℕ → ℕ) (hM : W5_mulAt Mul) : W9_multiply Mul :=
  WP.W9mp.W9_multiply_of_parts_holds Mul (w9_pipeline_proved Mul hM)
    (WP.W9sp.W9_splitPack_holds WP.Top.W3_all_holds)
    (WP.W9sq.W9_square_holds Mul hM WP.Top.W3_all_holds)
    WP.W9ex.W9_extract_proved
    (WP.W9h.W9_reconstruct_holds WP.Top.W3_all_holds)

#assert_std_axioms w5_toom3Mul_proved w7_buildTables_proved w4_all_proved w9_pipeline_proved
  w9_multiply_proved

end SubNLogN.Machine.MulBig
