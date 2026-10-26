import WP.W7k3t.Vals

/-!
# WP.W7k3t.Decomp — the canonical tap is the machine's value

`tapC_eq_tapV`: W7k2's canonical straight-line tap `tapC` (proved equal to the snapshot's
`computableSincGaussianTapWithProgramCost`, `tapC_eq`) is `tapV`, the composition of the values the
sub-kernels compute: `B = pSub+2`, `N = 17·pSub+22`, `B_c = 30·pSub+42`, `Bint = 43·pSub+60`,
`numY = numTheta²`, `negSq = -numY`.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

theorem tapC_eq_tapV (p_work pSub t1 j1 s πN lnN : ℕ) :
    tapC p_work pSub t1 j1 s πN lnN = tapV p_work pSub t1 j1 s πN lnN := by
  have eN : 4 * (4 * (pSub + 1)) + (pSub + 2) + 4 = 17 * pSub + 22 := by ring
  have eBc : pSub + 2 + (17 * pSub + 22) + 3 * (4 * (pSub + 1)) + 6 = 30 * pSub + 42 := by ring
  have eBi : pSub + 2 + 2 * (17 * pSub + 22) + 2 * (4 * (pSub + 1)) + 6 = 43 * pSub + 60 := by
    ring
  have e2B : 2 * (pSub + 2) = 2 * pSub + 4 := by ring
  have eB2 : pSub + 2 + 2 = pSub + 4 := by ring
  simp only [tapC, sincClampC, expClampC, eN, eBc, eBi, e2B, eB2, tapV, elseV, clampSerV, serV,
    srcV, denYV, denThV, numTV, ← Nat.cast_mul, Nat.cast_le]
  rfl

#assert_std_axioms tapC_eq_tapV

end WP.W7k3t
