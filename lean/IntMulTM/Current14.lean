import IntMulTM.Current13
import WP.W7k2.B.Top
import WP.W7k3.StdChar
import WP.W7k3t.Tap

/-!
# Integrator's tracking theorem, version 14

`intMul_TM2_nlogn_current13` with, in addition:
* `WP.W7k3.W7_stdChar_bind` (stdChar; packages wp/W7k3, wp/W7sc);
* `WP.W7k3t.W7_sincGaussianTap_bind` (sinc-Gaussian tap; package wp/W7k3t);
* `WP.W7k2.W7_buildTablesRef_holds` (the table builder; package wp/W7k2, witness `buildProg`).
Remaining: W7 c0c1; W9 spread and columns.
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current14
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h9spread : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul)
    (h9cols : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current13 WP.W7k3.W7_stdChar_bind WP.W7k3t.W7_sincGaussianTap_bind h7c01
    WP.W7k2.W7_buildTablesRef_holds h9spread h9cols

#assert_std_axioms intMul_TM2_nlogn_current14

end IntMulTM.Final
