import IntMulTM.SpecFacts
import Contracts.Machine.Common

/-!
# WP.W0m.Sched — the headline schedule (CSWS:2264-2269) and the arithmetic the machine uses

The headline parameters of `computablePaperMultiplyOfBitLength` (CallSiteWidthSoundness.lean:2264-2269),
restated as functions of the operand bit length `n`. `WP.W0m.Bridge` proves them equal by `rfl` to the
W8 contract's `IntMulTM.Contracts.W8.hB/hK/hK0/hL/hP0`:
* `sB n = max 1 (log₂ n)`;
* `sK n = n / sB n + 1`;
* `sK0 n = max 4 (log₂ (2·sK n) + 2)`;
* `sL n = log₂ (sK0 n − 1)`;
* `sP0 n = 2·sB n + 2·sK0 n + 6` (`rootPrecision`).

The machine never computes `log₂` directly. It counts bits: `log₂ m = bitLen m − 1` for `m ≥ 1`
(`bitLen_eq_log2_succ`). `sK0_eq`, `sL_eq` and `sB_eq` rewrite the schedule in that form.
-/

namespace WP.W0m

open Computability TMFw.Contracts

/-- `b = max 1 (log₂ n)` (CSWS:2264). -/
def sB (n : ℕ) : ℕ := max 1 (Nat.log2 n)
/-- `k = n / b + 1` (CSWS:2265). -/
def sK (n : ℕ) : ℕ := n / sB n + 1
/-- `K0 = max 4 (log₂ (2k) + 2)` (CSWS:2266). -/
def sK0 (n : ℕ) : ℕ := max 4 (Nat.log2 (2 * sK n) + 2)
/-- `L = log₂ (K0 − 1)` (CSWS:2267). -/
def sL (n : ℕ) : ℕ := Nat.log2 (sK0 n - 1)
/-- `p0 = rootPrecision b K0 = 2b + 2K0 + 6` (CSWS:2268). -/
def sP0 (n : ℕ) : ℕ := 2 * sB n + 2 * sK0 n + 6

theorem size_eq_log2_succ {n : ℕ} (h : n ≠ 0) : Nat.size n = Nat.log2 n + 1 := by
  apply le_antisymm
  · exact Nat.size_le.mpr ((Nat.log2_lt h).mp (Nat.lt_succ_self _))
  · exact Nat.lt_size.mpr (Nat.log2_self_le h)

theorem bitLen_eq_size (n : ℕ) : bitLen n = Nat.size n := IntMulTM.length_encodeNat n

theorem bitLen_eq_log2_succ {n : ℕ} (h : n ≠ 0) : bitLen n = Nat.log2 n + 1 := by
  rw [bitLen_eq_size, size_eq_log2_succ h]

theorem bitLen_mono {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n := by
  rw [bitLen_eq_size, bitLen_eq_size]
  exact Nat.size_le_size h

theorem bitLen_pos {n : ℕ} (h : n ≠ 0) : 1 ≤ bitLen n := by
  rw [bitLen_eq_log2_succ h]
  omega

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem operandBits_pos (a b : ℕ) : 1 ≤ IntMulTM.operandBits a b := le_max_left _ _

theorem operandBits_eq (a b : ℕ) :
    IntMulTM.operandBits a b = max 1 (max (bitLen a) (bitLen b)) := rfl

theorem sB_pos (n : ℕ) : 1 ≤ sB n := le_max_left _ _

theorem sK_pos (n : ℕ) : 1 ≤ sK n := Nat.succ_le_succ (Nat.zero_le _)

theorem sK0_ge (n : ℕ) : 4 ≤ sK0 n := le_max_left _ _

/-- The machine's form of `b`: `max 1 (bitLen n − 1)`. -/
theorem sB_eq {n : ℕ} (hn : n ≠ 0) : sB n = max 1 (bitLen n - 1) := by
  unfold sB
  rw [bitLen_eq_log2_succ hn, Nat.add_sub_cancel]

/-- The machine's form of `K0`: `max 4 (bitLen k + 2)`. -/
theorem sK0_eq (n : ℕ) : sK0 n = max 4 (bitLen (sK n) + 2) := by
  have hk : sK n ≠ 0 := by have := sK_pos n; omega
  unfold sK0
  rw [Nat.log2_two_mul hk, bitLen_eq_log2_succ hk]

/-- The machine's form of `L`: `bitLen (K0 − 1) = L + 1`. -/
theorem sL_eq (n : ℕ) : bitLen (sK0 n - 1) = sL n + 1 := by
  have := sK0_ge n
  unfold sL
  rw [bitLen_eq_log2_succ (by omega)]

/-! ## Value bounds (for the cost statement) -/

theorem sB_le {n : ℕ} (hn : 1 ≤ n) : sB n ≤ n := max_le hn (Nat.log2_le_self n)

theorem sK_le (n : ℕ) : sK n ≤ n + 1 := by
  unfold sK
  have := Nat.div_le_self n (sB n)
  omega

theorem sK0_le (n : ℕ) : sK0 n ≤ 2 * n + 6 := by
  unfold sK0
  have h1 := Nat.log2_le_self (2 * sK n)
  have h2 := sK_le n
  omega

theorem sL_le (n : ℕ) : sL n ≤ 2 * n + 6 := by
  unfold sL
  have h1 := Nat.log2_le_self (sK0 n - 1)
  have h2 := sK0_le n
  omega

theorem sP0_le {n : ℕ} (hn : 1 ≤ n) : sP0 n ≤ 6 * n + 18 := by
  unfold sP0
  have h1 := sB_le hn
  have h2 := sK0_le n
  omega

#assert_std_axioms size_eq_log2_succ bitLen_eq_log2_succ bitLen_mono bitLen_pos sB_eq sK0_eq sL_eq
  sB_le sK_le sK0_le sL_le sP0_le

end WP.W0m
