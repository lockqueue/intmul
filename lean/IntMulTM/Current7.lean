import WP.Top.Current6
import WP.W4.Main
import WP.W9mp.Main

/-!
# Integrator's tracking theorem, version 7

`intMul_TM2_nlogn_current6` (`WP.Top.Current6`: all of W3, the W9a level/pipeline
assembly, W9b preTranspose/emitRows and W9e plugged in) with, in addition:
* `TMFw.W4.W4_transpose_holds` (both orientations; package wp/W4);
* `WP.W9mp.W9_multiply_of_parts_holds` (root assembly; package wp/W9mp).
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current7
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h4osf : W4_oddStrideFactor) (h4or : W4_oddRoute .down .down)
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
    (hroot : W9RootOK wdF wdI wR)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current6 wdF wdI wR (TMFw.W4.W4_transpose_holds .down .down) h4osf h4or
    (TMFw.W4.W4_transpose_holds .down .up) h7std h7tap h7c01 h7ref h9alt h9spread h9preTw h9syn
    h9postTw h9cols h9leaf h9split h9sq h9ext h9rec
    (fun _ _ _ Mul => WP.W9mp.W9_multiply_of_parts_holds Mul) hroot hw

#assert_std_axioms intMul_TM2_nlogn_current7

end IntMulTM.Final
