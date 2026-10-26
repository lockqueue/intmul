import IntMulTM.Current8
import WP.W9b.AltSum
import WP.W9d.Final
import WP.W9h.Gate

/-!
# Integrator's tracking theorem, version 9

`intMul_TM2_nlogn_current8` with, in addition:
* `WP.W9b.W9_altSum_holds` (instantiated with the proved W3 contracts; package wp/W9b);
* `WP.W9d.W9_preTwist_holds`, `WP.W9d.W9_postTwist_holds` (binding shape; packages wp/W9d, wp/W9dR);
* `WP.W9h.W9_reconstruct_binding` (package wp/W9h).
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current9
    (h4osf : W4_oddStrideFactor) (h4or : W4_oddRoute .down .down)
    (h7std : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_stdChar)
    (h7tap : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps →
      W7_sincGaussianTap)
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h7ref : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
      W7_buildTablesRef W7.snapshotSchedule)
    (h9spread : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul)
    (h9syn : W3_all → W4_all → W6a_all → W9_synFFT)
    (h9cols : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul)
    (h9leaf : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_leafFFT Mul)
    (h9split : W3_all → W4_all → W6a_all → W9_splitPack)
    (h9sq : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_square Mul)
    (h9ext : W3_all → W4_all → W6a_all → W9_extract) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current8 h4osf h4or h7std h7tap h7c01 h7ref
    (fun _ _ _ => WP.W9b.W9_altSum_holds
      (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
      (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
      WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds TMFw.W3s.W3_shlVar_holds
      TMFw.W3s.W3_shrVar_holds)
    h9spread WP.W9d.W9_preTwist_holds h9syn WP.W9d.W9_postTwist_holds h9cols h9leaf h9split
    h9sq h9ext WP.W9h.W9_reconstruct_binding

#assert_std_axioms intMul_TM2_nlogn_current9

end IntMulTM.Final
