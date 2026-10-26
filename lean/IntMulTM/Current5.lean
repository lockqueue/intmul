import WP.Top.Current4
import WP.W3.AddSub
import WP.W3.Misc
import WP.W3e.Shift

/-!
# Integrator's tracking theorem, version 5

`intMul_TM2_nlogn_current4` (`WP.Top.Current4`) with the W3 contracts proved so far
discharged: `WP.W3` (addNat, subNat, normNat, dropNat) and `WP.W3e` (shlConst, shrConst).
The remaining hypotheses are exactly the leaf contracts that are still open.
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current5
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h3shlV : W3_shlVar) (h3shrV : W3_shrVar) (h3split : W3_splitAt) (h3concat : W3_concatAt)
    (h4tr : W4_transpose .down .down) (h4osf : W4_oddStrideFactor)
    (h4or : W4_oddRoute .down .down) (h4trU : W4_transpose .down .up)
    (h7std : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_stdChar)
    (h7tap : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps →
      W7_sincGaussianTap)
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h7ref : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
      W7_buildTablesRef W7.snapshotSchedule)
    (h9pT : W4_transpose .down .up → W3_all → W4_all → W6a_all → W9_preTranspose)
    (H9 : WP.Top.W9StageThms4)
    (hA1 : W3_all → W4_all → W6a_all → ∀ Mul, W9_levels_of_kernels Mul)
    (hA2 : W3_all → W4_all → W6a_all → ∀ Mul, W9_pipeline_of_levels Mul)
    (hA3 : W3_all → W4_all → W6a_all → ∀ Mul, W9_multiply_of_parts Mul)
    (hroot : W9RootOK wdF wdI wR)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    IntMulTM.IntMulNLogN :=
  WP.Top.intMul_TM2_nlogn_current4 wdF wdI wR WP.W3.W3_dropNat_holds WP.W3.W3_normNat_holds
    WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds WP.W3e.W3_shlConst_holds WP.W3e.W3_shrConst_holds
    h3shlV h3shrV h3split h3concat h4tr h4osf h4or h4trU h7std h7tap h7c01 h7ref h9pT H9
    hA1 hA2 hA3 hroot hw

#assert_std_axioms intMul_TM2_nlogn_current5

end IntMulTM.Final
