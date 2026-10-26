import WP.W9ex.Digit
import Contracts.W9.Root

/-!
# WP.W9ex.Value — the contract's root digits are the machine's digits

`divRound9_toNat`: the root extraction `(divRoundPow2 (-z.2) 9).toNat` is `mdig z` (`0` unless
`z.2 < 0`, else `(|z.2| / 2^8 + 1) / 2`). `rootDigits_eq_mdig`: the `k1 + k2` digits of
`rootDigits` are `mdig` of the first `k1 + k2` entries (via `W8_extractRootSlot_shift_holds`).
Proved via the digit-extraction lemmas (matching `WP.W9exv.Digits`),
specialized directly to `WP.W9ex.mdig`.
-/

namespace WP.W9ex

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul

theorem divRound9_toNat (z : ℤ × ℤ) : (IntMul.divRoundPow2 (-z.2) 9).toNat = mdig z := by
  unfold divRoundPow2 mdig
  rw [if_neg (by decide)]
  have e1 : ((2 ^ (9 - 1) : ℕ) : ℤ) = 256 := by norm_num
  have e2 : ((2 ^ 9 : ℕ) : ℤ) = 512 := by norm_num
  rw [e1, e2]
  split_ifs with h
  · have hy : ((z.2.natAbs : ℕ) : ℤ) = -z.2 := Int.ofNat_natAbs_of_nonpos h.le
    generalize z.2.natAbs = n at hy ⊢
    have e : (-z.2 + 256) / 512 = (((n / 2 ^ 8 + 1) / 2 : ℕ) : ℤ) := by
      rw [show -z.2 = (n : ℤ) by omega]
      norm_num
      omega
    rw [e]
    exact Int.toNat_natCast _
  · push_neg at h
    rw [Int.toNat_eq_zero]
    omega

theorem rootDigits_eq_mdig (b K0 k1 k2 : ℕ) (v : Array (ℤ × ℤ)) (hv : v.size = 2 ^ K0)
    (hk : k1 + k2 ≤ 2 ^ K0) :
    TMFw.Contracts.W9.rootDigits b K0 k1 k2 v = (v.toList.take (k1 + k2)).map mdig := by
  unfold rootDigits
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, Array.length_toList]
    omega
  · intro j h1 h2
    have hj : j < k1 + k2 := by simpa using h1
    have hjK : j < 2 ^ K0 := by omega
    have hjv : j < v.size := by omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, Array.getElem_toList]
    unfold rootExtractV
    rw [read1D_runSequentialScanSteps_eq _ _ _ hjK]
    rw [IntMulTM.Contracts.W8_extractRootSlot_shift_holds b K0, divRound9_toNat]
    unfold read1D
    rw [dif_pos hjv]

#assert_std_axioms divRound9_toNat rootDigits_eq_mdig

end WP.W9ex
