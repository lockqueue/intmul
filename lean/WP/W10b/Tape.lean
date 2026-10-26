import WP.W10b.Headline
import WP.W7pure.TapeBound

/-!
# WP.W10b.Tape — the table tape is `O(n log n)`

`w7_tape_le`: for any W7 joint output `cSpec` of the headline schedule (`n ≥ 2`),
`|W7.tape fmt cSpec| ≤ 64·C₇·n·log₂ n`, with `C₇ = WP.W7pure.tapeBoundConst`. Route: `JointOutput.size`,
then W7pure's `tapeBound_le` (`≤ C₇·(√n+1)·(log₂ n+1)³`), then `sqrt_log_cube_le`.

W9's own tape encoding `tapeSyms` differs from `W7.tape`; the TapeConv worker bridges
`|tapeSyms cSpec| ≤ C·(|W7.tape cSpec| + 1)`, which turns this into the `T n` hypothesis of
`WP.W10b.w9_cost_le`/`w9_bounds`.
-/

namespace WP.W10b

open TMFw.Contracts IntMul IntMulTM.Contracts

/-- `(√n + 1)·(log₂ n + 1)³ ≤ 64·n·log₂ n` for `n ≥ 2`. -/
theorem sqrt_log_cube_le {n : ℕ} (hn : 2 ≤ n) :
    (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3 ≤ 64 * n * Nat.log2 n := by
  have hb1 := one_le_log2 hn
  have hs1 : 1 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  have hss : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have h2k : 2 ^ Nat.log2 (Nat.sqrt n) ≤ Nat.sqrt n := Nat.log2_self_le (by omega)
  have hsk : Nat.sqrt n < 2 ^ (Nat.log2 (Nat.sqrt n) + 1) := Nat.lt_log2_self
  generalize Nat.sqrt n = s at *
  generalize Nat.log2 s = k at *
  have hn2 : n < 2 ^ (2 * k + 2) := by
    have h1 : (s + 1) * (s + 1) ≤ 2 ^ (k + 1) * 2 ^ (k + 1) := Nat.mul_le_mul hsk hsk
    have e : 2 ^ (k + 1) * 2 ^ (k + 1) = 2 ^ (2 * k + 2) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    omega
  have hlog : Nat.log2 n < 2 * k + 2 := (Nat.log2_lt (by omega)).2 hn2
  have hsq := WP.W10.succ_sq_le_four_mul_two_pow k
  have hl2 : (Nat.log2 n + 1) ^ 2 ≤ 16 * s := by
    have h1 : Nat.log2 n + 1 ≤ 2 * (k + 1) := by omega
    calc (Nat.log2 n + 1) ^ 2 ≤ (2 * (k + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 4 * (k + 1) ^ 2 := by ring
      _ ≤ 4 * (4 * 2 ^ k) := Nat.mul_le_mul_left 4 hsq
      _ ≤ 16 * s := by omega
  calc (s + 1) * (Nat.log2 n + 1) ^ 3 = (s + 1) * (Nat.log2 n + 1) ^ 2 * (Nat.log2 n + 1) := by
        ring
    _ ≤ (2 * s) * (16 * s) * (2 * Nat.log2 n) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) hl2) (by omega)
    _ = 64 * (s * s) * Nat.log2 n := by ring
    _ ≤ 64 * n * Nat.log2 n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 hss)

/-- **Table tape (W7 format) is `O(n log n)`.** -/
theorem w7_tape_le {n : ℕ} (hn : 2 ≤ n) (cSpec : ComputablePaperFastDFTSpec)
    (hj : W7.JointOutput W7.snapshotSchedule.toTapeFormat W7.snapshotSchedule.Faithful
      (W8.hSpec n) cSpec) :
    (W7.tape W7.snapshotFormat cSpec).length ≤ 64 * WP.W7pure.tapeBoundConst * n * Nat.log2 n := by
  have h1 : (W7.tape W7.snapshotFormat cSpec).length ≤ W7.tapeBound W7.snapshotFormat cSpec :=
    hj.size
  have h2 := WP.W7pure.tapeBound_le n cSpec hj.faithful
  have h3 := sqrt_log_cube_le hn
  calc (W7.tape W7.snapshotFormat cSpec).length ≤ W7.tapeBound W7.snapshotFormat cSpec := h1
    _ ≤ WP.W7pure.tapeBoundConst * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3 := h2
    _ = WP.W7pure.tapeBoundConst * ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3) := by ring
    _ ≤ WP.W7pure.tapeBoundConst * (64 * n * Nat.log2 n) := Nat.mul_le_mul_left _ h3
    _ = 64 * WP.W7pure.tapeBoundConst * n * Nat.log2 n := by ring

#assert_std_axioms sqrt_log_cube_le w7_tape_le

end WP.W10b
