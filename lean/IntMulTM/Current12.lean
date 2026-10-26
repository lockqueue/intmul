import IntMulTM.Current11
import WP.W9sp.Main
import WP.W9sq.Theorem

/-!
# Integrator's tracking theorem, version 12

`intMul_TM2_nlogn_current11` with, in addition:
* `WP.W9sp.W9_splitPack_holds` (package wp/W9sp);
* `WP.W9sq.W9_square_holds'` (binding shape; package wp/W9sq).
Remaining: the W7 table kernels and builder; W9 spread, synFFT and columns.
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current12
    (h7std : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_stdChar)
    (h7tap : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps →
      W7_sincGaussianTap)
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h7ref : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
      W7_buildTablesRef W7.snapshotSchedule)
    (h9spread : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul)
    (h9syn : W3_all → W4_all → W6a_all → W9_synFFT)
    (h9cols : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current11 h7std h7tap h7c01 h7ref h9spread h9syn h9cols
    (fun h3 _ _ => WP.W9sp.W9_splitPack_holds h3) WP.W9sq.W9_square_holds'

#assert_std_axioms intMul_TM2_nlogn_current12

end IntMulTM.Final
