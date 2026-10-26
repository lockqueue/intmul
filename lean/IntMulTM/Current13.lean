import IntMulTM.Current12
import WP.W9s.Main

/-!
# Integrator's tracking theorem, version 13

`intMul_TM2_nlogn_current12` with `WP.W9s.W9_synFFT_holds` (synthetic FFT; package wp/W9s)
discharged by the proved signed W3 contracts.
Remaining: the W7 table kernels and builder; W9 spread and columns.
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current13
    (h7std : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_stdChar)
    (h7tap : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps →
      W7_sincGaussianTap)
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h7ref : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
      W7_buildTablesRef W7.snapshotSchedule)
    (h9spread : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul)
    (h9cols : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current12 h7std h7tap h7c01 h7ref h9spread
    (fun _ _ _ => WP.W9s.W9_synFFT_holds
      (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
      (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds))
    h9cols

#assert_std_axioms intMul_TM2_nlogn_current13

end IntMulTM.Final
