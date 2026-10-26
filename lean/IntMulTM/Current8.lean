import IntMulTM.Current7
import WP.W11b.Final

/-!
# Integrator's tracking theorem, version 8

`intMul_TM2_nlogn_current7` at W11b's headline width profiles
(`wdF = wdI = fun n _ => WP.W11b.wdHead n`, `wR = WP.W11b.wRHead`), with `hroot` and `hw`
discharged by `WP.W11b.w9RootOK_headline` and `WP.W11b.widths_headline` (package wp/W11b).
The remaining hypotheses are the open table and W9 kernels, plus W4 oddStrideFactor/oddRoute.
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current8
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
    (h9rec : W3_all → W4_all → W6a_all → W9_reconstruct) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current7 (fun n _ => WP.W11b.wdHead n) (fun n _ => WP.W11b.wdHead n)
    WP.W11b.wRHead h4osf h4or h7std h7tap h7c01 h7ref h9alt h9spread h9preTw h9syn h9postTw
    h9cols h9leaf h9split h9sq h9ext h9rec WP.W11b.w9RootOK_headline WP.W11b.widths_headline

#assert_std_axioms intMul_TM2_nlogn_current8

end IntMulTM.Final
