import IntMulTM.Current9
import WP.W4f.Top
import WP.W4o.OddRoute

/-!
# Integrator's tracking theorem, version 10

`intMul_TM2_nlogn_current9` with the last W4 leaves discharged:
* `WP.W4f.W4_oddStrideFactor_holds` (package wp/W4f);
* `TMFw.W4o.W4_oddRoute_holds` (package wp/W4o).
Remaining: the W7 table kernels and builder, and seven W9 kernels.
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current10
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
  intMul_TM2_nlogn_current9 WP.W4f.W4_oddStrideFactor_holds TMFw.W4o.W4_oddRoute_holds
    h7std h7tap h7c01 h7ref h9spread h9syn h9cols h9leaf h9split h9sq h9ext

#assert_std_axioms intMul_TM2_nlogn_current10

end IntMulTM.Final
