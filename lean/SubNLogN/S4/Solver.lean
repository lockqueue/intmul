import SubNLogN.Spec

/-!
# Component S4 (`Solver.lean`): Cyclic Deconvolution Conditioning & Truncated Closure Powering

**Scope.** Proves three closed-form `ℕ` polynomial/exponent inequalities accompanying Lemma 4.6 (bridge Lemma C)(iv)–(v) (`lem:bridge-C`) and Lemma 4.8 (bridge Lemma D) (`lem:bridge-D`); full analytical and `TM2` solver/exposure proofs live in `SubNLogN/{Math/Bridge,Machine/Bridge}/`:
1. Two-pass cyclic solver error bound `6 t^2 + 16 t ≤ 32 t^2` for all even `t ≥ 2`;
2. Truncated binary-powering closure precision `Q = q + lg_L + 2 lg_4t + 10` (`4 t^2 * 2 L ≤ 2^{Q - q} / 2048`);
3. Direct `O(d)` axis exposure count `2(d - 1)` vs `O(d^2)` adjacent cascade (Lemma 4.8 (bridge Lemma D), `lem:bridge-D`).
-/

namespace SubNLogN.S4

open SubNLogN

/-- **Cyclic Solver Error Constant (Lemma 4.6 (bridge Lemma C)(iv), `lem:bridge-C`):**
For every axis length `t ≥ 2`, the resolvent perturbation (`6 t^2`), closure error (`12 t`),
and second-pass error (`4 t`) satisfy `6 t^2 + 16 t ≤ 32 t^2`. -/
theorem cyclic_solver_error_constant (t : ℕ) (ht : 2 ≤ t) :
    6 * t ^ 2 + 16 * t ≤ 32 * t ^ 2 := by
  have h1 : 16 * t ≤ 26 * t * t := Nat.mul_le_mul_right t (by omega)
  have h2 : 26 * t * t = 26 * t ^ 2 := by ring
  omega

/-- **Truncated Binary-Powering Closure Precision (Lemma 4.6 (bridge Lemma C)(v), `lem:bridge-C`):**
With `Q = q + lg_L + 2 * lg_4t + 10` where `L ≤ 2 ^ lg_L` and `4 * t ≤ 2 ^ lg_4t`,
the powering error contribution `4 * t^2 * (2 * L)` satisfies
`4 * t^2 * (2 * L) * 2048 ≤ 2 ^ (lg_L + 2 * lg_4t + 10) = 2 ^ (Q - q)`. -/
theorem closure_powering_precision_margin (t L lg_L lg_4t : ℕ)
    (hL : L ≤ 2 ^ lg_L) (ht : 4 * t ≤ 2 ^ lg_4t) :
    4 * t ^ 2 * (2 * L) * 2048 ≤ 2 ^ (lg_L + 2 * lg_4t + 10) := by
  calc 4 * t ^ 2 * (2 * L) * 2048
      = (4 * t) * (4 * t) * L * 2 ^ 10 := by ring
    _ ≤ 2 ^ lg_4t * 2 ^ lg_4t * 2 ^ lg_L * 2 ^ 10 := by
        exact Nat.mul_le_mul_right (2 ^ 10) (Nat.mul_le_mul (Nat.mul_le_mul ht ht) hL)
    _ = 2 ^ (lg_L + 2 * lg_4t + 10) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        ring

/-- **Direct Axis Exposure Sweep Count (Lemma 4.8 (bridge Lemma D), `lem:bridge-D`):**
Exposing each of the `d - 1` outer axes directly to the innermost position and restoring it uses
`2 * (d - 1)` exchanges, and reversing the axis order uses `d / 2` exchanges. -/
theorem direct_axis_exposure_count (d : ℕ) (hd : 2 ≤ d) :
    2 * (d - 1) + d / 2 ≤ 3 * d := by
  omega

end SubNLogN.S4
