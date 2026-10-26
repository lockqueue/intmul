import WP.W11b.Defs

/-!
# WP.W11b.Width — the headline width profiles are `O(log n)`

`wdHead n = 2·p0 + 3 + 4·specW (hSpec n)` and `wRHead n = 4·p0`, where `hSpec n` is
`buildQuantizedSpecPaperStop L p0 K0` with `p0 = 2b + 2K0 + 6`. With `ℓ = log₂ n`:

| quantity | bound | lemma |
|---|---|---|
| `b` | `≤ ℓ + 1` | `hB_le_log` |
| `K0` | `≤ ℓ + 4` | `hK0_le_log` |
| `L` | `≤ K0` | `hL_le_hK0` |
| `specW (buildQuantizedSpecPaperStop L p K)` | `≤ 2·leafPrecision L p K + K + 8` | `specW_paperStop_le` |
| `wdHead n` | `≤ 188ℓ + 787` | `wdHead_le` |
| `wRHead n` | `≤ 16ℓ + 64` | `wRHead_le` |

Pure `ℕ` arithmetic; `leafPrecision_le` (`≤ p + 4K + 14L`) is the snapshot's.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- Along the paper-stop builder, `specW` (max over the levels of `2·pChild p K` and the leaf
`2p + K + 8`) is at most `2·leafPrecision L p K + K + 8`. -/
theorem specW_paperStop_le (L p K : ℕ) :
    specW (buildQuantizedSpecPaperStop L p K) ≤ 2 * leafPrecision L p K + K + 8 := by
  induction L generalizing p K with
  | zero =>
    have e : specW (buildQuantizedSpecPaperStop 0 p K) = 2 * p + K + 8 := by
      simp only [buildQuantizedSpecPaperStop, specW, Nat.log2_two_pow]
    have e2 : leafPrecision 0 p K = p := rfl
    omega
  | succ L ih =>
    have hle := le_leafPrecision L (pChild p K) (K - K / 2)
    have hpc : p ≤ pChild p K := by unfold pChild pWork; omega
    have hih := ih (pChild p K) (K - K / 2)
    have hlp : leafPrecision (L + 1) p K = leafPrecision L (pChild p K) (K - K / 2) := rfl
    rw [hlp]
    by_cases h : 2 ^ K ≤ 4 * p * p
    · have e : specW (buildQuantizedSpecPaperStop (L + 1) p K) = 2 * p + K + 8 := by
        simp only [buildQuantizedSpecPaperStop, if_pos h, specW, Nat.log2_two_pow]
      omega
    · have e : specW (buildQuantizedSpecPaperStop (L + 1) p K) =
          max (2 * pChild p K) (specW (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2))) := by
        simp only [buildQuantizedSpecPaperStop, if_neg h, quantizedBoxGaussianStepSpec, specW]
      rw [e]
      exact max_le (by omega) (by omega)

theorem hB_le_log (n : ℕ) : IntMulTM.Contracts.W8.hB n ≤ Nat.log2 n + 1 := by
  unfold IntMulTM.Contracts.W8.hB
  exact max_le (by omega) (by omega)

theorem hK0_le_log (n : ℕ) : IntMulTM.Contracts.W8.hK0 n ≤ Nat.log2 n + 4 := by
  have hk : IntMulTM.Contracts.W8.hK n ≤ n + 1 := by
    unfold IntMulTM.Contracts.W8.hK
    have h := Nat.div_le_self n (IntMulTM.Contracts.W8.hB n)
    omega
  have hk1 : 1 ≤ IntMulTM.Contracts.W8.hK n := Nat.le_add_left 1 _
  have hn := lt_two_pow_log2_succ n
  have e : 2 ^ (Nat.log2 n + 3) = 4 * 2 ^ (Nat.log2 n + 1) := by ring
  have h2k : 2 * IntMulTM.Contracts.W8.hK n < 2 ^ (Nat.log2 n + 3) := by omega
  have hlog := (Nat.log2_lt (by omega : 2 * IntMulTM.Contracts.W8.hK n ≠ 0)).2 h2k
  unfold IntMulTM.Contracts.W8.hK0
  exact max_le (by omega) (by omega)

theorem hL_le_hK0 (n : ℕ) : IntMulTM.Contracts.W8.hL n ≤ IntMulTM.Contracts.W8.hK0 n := by
  have h := Nat.log2_le_self (IntMulTM.Contracts.W8.hK0 n - 1)
  unfold IntMulTM.Contracts.W8.hL
  omega

theorem wdHead_le (n : ℕ) : wdHead n ≤ 188 * Nat.log2 n + 787 := by
  have h1 := specW_paperStop_le (IntMulTM.Contracts.W8.hL n) (IntMulTM.Contracts.W8.hP0 n)
    (IntMulTM.Contracts.W8.hK0 n)
  have h2 := leafPrecision_le (IntMulTM.Contracts.W8.hL n) (IntMulTM.Contracts.W8.hP0 n)
    (IntMulTM.Contracts.W8.hK0 n)
  have h3 : IntMulTM.Contracts.W8.hP0 n =
      2 * IntMulTM.Contracts.W8.hB n + 2 * IntMulTM.Contracts.W8.hK0 n + 6 := rfl
  have h4 := hB_le_log n
  have h5 := hK0_le_log n
  have h6 := hL_le_hK0 n
  have h7 : wdHead n = 2 * IntMulTM.Contracts.W8.hP0 n + 3 +
      4 * specW (buildQuantizedSpecPaperStop (IntMulTM.Contracts.W8.hL n)
        (IntMulTM.Contracts.W8.hP0 n) (IntMulTM.Contracts.W8.hK0 n)) := rfl
  omega

theorem wRHead_le (n : ℕ) : wRHead n ≤ 16 * Nat.log2 n + 64 := by
  have h3 : IntMulTM.Contracts.W8.hP0 n =
      2 * IntMulTM.Contracts.W8.hB n + 2 * IntMulTM.Contracts.W8.hK0 n + 6 := rfl
  have h4 := hB_le_log n
  have h5 := hK0_le_log n
  have h7 : wRHead n = 4 * IntMulTM.Contracts.W8.hP0 n := rfl
  omega

/-- **(A) width bound.** Both headline width profiles are `O(log n)`. -/
theorem width_bound : ∃ cw, ∀ n ≥ 1,
    wdHead n ≤ cw * (Nat.log2 n + 1) ∧ wRHead n ≤ cw * (Nat.log2 n + 1) :=
  ⟨787, fun n _ => ⟨by have := wdHead_le n; omega, by have := wRHead_le n; omega⟩⟩

#assert_std_axioms specW_paperStop_le hB_le_log hK0_le_log hL_le_hK0 wdHead_le wRHead_le width_bound

end WP.W11b
