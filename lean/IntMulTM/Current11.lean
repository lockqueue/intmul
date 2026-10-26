import IntMulTM.Current10
import WP.W9gx.Final
import WP.W9ex.Extract

/-!
# Integrator's tracking theorem, version 11

`intMul_TM2_nlogn_current10` with, in addition:
* `WP.W9gx.W9_leafFFT_holds` (leaf FFT; packages wp/W9g, wp/W9gx), instantiated with the proved
  W3 contracts;
* `WP.W9ex.W9_extract_binding` (package wp/W9ex).
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current11
    (h7std : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_stdChar)
    (h7tap : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps →
      W7_sincGaussianTap)
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h7ref : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
      W7_buildTablesRef W7.snapshotSchedule)
    (h9spread : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul)
    (h9syn : W3_all → W4_all → W6a_all → W9_synFFT)
    (h9cols : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul)
    (h9split : W3_all → W4_all → W6a_all → W9_splitPack)
    (h9sq : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_square Mul) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current10 h7std h7tap h7c01 h7ref h9spread h9syn h9cols
    (fun Mul hM _ _ _ => WP.W9gx.W9_leafFFT_holds Mul hM
      (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
      (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
      TMFw.W3s.W3_shlVar_holds TMFw.W3s.W3_shrVar_holds)
    h9split h9sq WP.W9ex.W9_extract_binding

#assert_std_axioms intMul_TM2_nlogn_current11

end IntMulTM.Final
