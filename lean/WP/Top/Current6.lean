import WP.Top.Current4
import WP.W3.AddSub
import WP.W3.Misc
import WP.W3e.Shift
import WP.W3s.Split
import WP.W3s.Concat
import WP.W9a.Final
import WP.W9b.Transpose
import WP.W9b.Emit
import WP.W9e.All

/-!
# WP.Top.Current6 — the headline with every proved piece plugged in (mid-course integration)

`intMul_TM2_nlogn_current6` is `intMul_TM2_nlogn_current4` (= the integrator's `current5`) with
everything proved so far discharged. The remaining hypotheses are exactly the open leaves.

| discharged | by | source |
|---|---|---|
| all 25 conjuncts of `W3_all` | `W3_all_holds` | W3 (`WP.W3`), W3e (`WP.W3e`), W3s (`TMFw.W3s`), frozen `w3_*`, W3b |
| `h9pT` (pre-transpose, from `W4_transpose .down .up`) | `WP.W9b.W9_preTranspose_holds` | W9b |
| `emitRows` | `WP.W9b.W9_emitRows_holds` | W9b |
| `postTranspose`, `columnRoutes`, `postOutput` | `WP.W9e.W9e_holds` | W9e |
| `retFlip`, `sweep`, `level` | `WP.W9a.W9_{retFlip,sweep,level}_holds` | W9a |
| `hA1`, `hA2` | `WP.W9a.W9_levels_of_kernels_holds`, `W9_pipeline_of_levels_holds` | W9a |

W3s, W9a, W9b and W9e are integrated from their respective sub-packages (`TMFw.W3s`, `WP.W9a`, `WP.W9b`, `WP.W9e`).
-/

namespace WP.Top

open TMFw TMFw.Contracts IntMulTM.Contracts.Top

/-- **All of W3 is proved.** -/
theorem W3_all_holds : W3_all :=
  W3_all_of_open WP.W3.W3_dropNat_holds WP.W3.W3_normNat_holds WP.W3.W3_addNat_holds
    WP.W3.W3_subNat_holds WP.W3e.W3_shlConst_holds WP.W3e.W3_shrConst_holds
    TMFw.W3s.W3_shlVar_holds TMFw.W3s.W3_shrVar_holds TMFw.W3s.W3_splitAt_holds
    TMFw.W3s.W3_concatAt_holds

/-- **The headline from the open leaves.**
| hypotheses | owner |
|---|---|
| `h4tr`, `h4trU` (`W4_transpose`, both orientations) | W4 |
| `h4osf` (`W4_oddStrideFactor`) | W4 oddStrideFactor |
| `h4or` (`W4_oddRoute .down .down`) | W4o |
| `h7ref` (`W7_buildTablesRef`) | W7 builder |
| `h7std`, `h7c01` | W7 stdChar / c0c1 |
| `h7tap` | W7 sincGaussianTap |
| `h9alt` | W9b |
| `h9spread` | W9c |
| `h9preTw`, `h9postTw` | W9d |
| `h9syn` | W9 synFFT |
| `h9cols` | W9f |
| `h9leaf` | W9g |
| `h9split`, `h9rec` | W9h |
| `h9sq` | W9 square |
| `h9ext` | W9 extract |
| `hA3` (`W9_multiply_of_parts`) | W9 multiply |
| `hroot`, `hw` | W11b | -/
theorem intMul_TM2_nlogn_current6
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h4tr : W4_transpose .down .down) (h4osf : W4_oddStrideFactor)
    (h4or : W4_oddRoute .down .down) (h4trU : W4_transpose .down .up)
    (h7std : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_stdChar)
    (h7tap : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps →
      W7_sincGaussianTap)
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h7ref : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
      W7_buildTablesRef W7.snapshotSchedule)
    (h9alt : W3_all → W4_all → W6a_all → W9_altSum)
    (h9spread : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul)
    (h9preTw : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_preTwist Mul)
    (h9syn : W3_all → W4_all → W6a_all → W9_synFFT)
    (h9postTw : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_postTwist Mul)
    (h9cols : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul)
    (h9leaf : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_leafFFT Mul)
    (h9split : W3_all → W4_all → W6a_all → W9_splitPack)
    (h9sq : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_square Mul)
    (h9ext : W3_all → W4_all → W6a_all → W9_extract)
    (h9rec : W3_all → W4_all → W6a_all → W9_reconstruct)
    (hA3 : W3_all → W4_all → W6a_all → ∀ Mul, W9_multiply_of_parts Mul)
    (hroot : W9RootOK wdF wdI wR)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current4 wdF wdI wR WP.W3.W3_dropNat_holds WP.W3.W3_normNat_holds
    WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds WP.W3e.W3_shlConst_holds WP.W3e.W3_shrConst_holds
    TMFw.W3s.W3_shlVar_holds TMFw.W3s.W3_shrVar_holds TMFw.W3s.W3_splitAt_holds
    TMFw.W3s.W3_concatAt_holds h4tr h4osf h4or h4trU h7std h7tap h7c01 h7ref
    (fun h _ _ _ => WP.W9b.W9_preTranspose_holds h)
    { altSum := h9alt
      spread := h9spread
      preTwist := h9preTw
      synFFT := h9syn
      postTwist := h9postTw
      emitRows := fun _ _ _ => WP.W9b.W9_emitRows_holds
      postTranspose := fun h3 h4 _ => (WP.W9e.W9e_holds h3 h4).1
      columnRoutes := fun h3 h4 _ => (WP.W9e.W9e_holds h3 h4).2.1
      columns := h9cols
      postOutput := fun h3 h4 _ => (WP.W9e.W9e_holds h3 h4).2.2
      leafFFT := h9leaf
      splitPack := h9split
      square := h9sq
      extract := h9ext
      reconstruct := h9rec
      retFlip := fun _ _ _ => WP.W9a.W9_retFlip_holds
      sweep := fun _ _ _ => WP.W9a.W9_sweep_holds
      level := fun _ _ _ => WP.W9a.W9_level_holds }
    (fun _ _ _ => WP.W9a.W9_levels_of_kernels_holds)
    (fun _ _ _ => WP.W9a.W9_pipeline_of_levels_holds) hA3 hroot hw

#assert_std_axioms W3_all_holds intMul_TM2_nlogn_current6

end WP.Top
