import SubNLogN.Spec

/-!
# Component S2 (`Butterfly.lean`): Euclidean Remainder Bound & `2 × 2` Phase-Basis Identity

**Scope.** Proves two `ℤ` checks: the Euclidean floor-division (`Int.ediv`) remainder bound `(x - (x / M) * M)^2 < M^2`
(not toward-zero `Q_q` or disk preservation; actual `Q_q` (`truncC`) and Proposition A.11 (`prop:prop14-param`) live in `SubNLogN/Math/Common/Grid.lean` and `SubNLogN/{Math/Networks,Machine/AppC}/`) and `(2 C)^2 = 4 X`.
-/

namespace SubNLogN.S2

open SubNLogN

/-- For every integer `x : ℤ` and positive modulus `M > 0`, Lean's Euclidean floor division `x / M`
(`Int.ediv`, with remainder `0 ≤ x % M < M`) satisfies `(x - (x / M) * M) ^ 2 < M ^ 2`. -/
theorem int_emod_sq_lt (x M : ℤ) (hM : 0 < M) :
    (x - (x / M) * M) ^ 2 < M ^ 2 := by
  have hdiv := Int.emod_def x M
  have hcomm : (x / M) * M = M * (x / M) := Int.mul_comm _ _
  have heq : x - (x / M) * M = x % M := by omega
  rw [heq]
  have h0 : 0 ≤ x % M := Int.emod_nonneg x (by omega)
  have h1 : x % M < M := Int.emod_lt_of_pos x hM
  have hpos : 0 < (M - x % M) * (M + x % M) := Int.mul_pos (by omega) (by omega)
  have hring : (M - x % M) * (M + x % M) = M ^ 2 - (x % M) ^ 2 := by ring
  omega

/-- **Euclidean Floor-Division Remainder Bound (historical identifier `truncation_toward_zero_error_sq`):**
For any `(re, im) ∈ ℤ × ℤ` and shift `s : ℕ`, Euclidean floor division by `2^s` (`truncationTowardZeroPair`,
using `Int.ediv`) leaves non-negative remainders `< 2^s`, so their squared sum is `< 2 · (2^s)^2`.
(Actual toward-zero truncation `Q_q` and disk preservation are proved in `SubNLogN/Math/Common/Grid.lean`.) -/
theorem truncation_toward_zero_error_sq (re im : ℤ) (s : ℕ) :
    (re - (truncationTowardZeroPair re im s).1 * (2 ^ s : ℤ)) ^ 2 +
    (im - (truncationTowardZeroPair re im s).2 * (2 ^ s : ℤ)) ^ 2 < 2 * ((2 ^ s : ℤ) ^ 2) := by
  dsimp only [truncationTowardZeroPair]
  have hM : (0 : ℤ) < (2 ^ s : ℤ) := pow_pos (by omega : (0 : ℤ) < 2) s
  have hre := int_emod_sq_lt re (2 ^ s : ℤ) hM
  have him := int_emod_sq_lt im (2 ^ s : ℤ) hM
  omega

/-- **Phase-Basis Identity (`[OAI26, (13)–(14)]`, Lemma A.10 (`lem:transfer-phase`)):**
With `2 C = (1 + i) I + (1 - i) X`, we have `(2 C)^2 = 4 X`, i.e. `C^2 = X`. -/
def twoC (p : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  let a := (1, 1)   -- 1 + i
  let b := (1, -1)  -- 1 - i
  let z0 := gaussMul a p.1
  let z1 := gaussMul b p.2
  let w0 := gaussMul b p.1
  let w1 := gaussMul a p.2
  ((z0.1 + z1.1, z0.2 + z1.2), (w0.1 + w1.1, w0.2 + w1.2))

theorem twoC_sq_eq_four_swap (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    twoC (twoC p) = ((4 * p.2.1, 4 * p.2.2), (4 * p.1.1, 4 * p.1.2)) := by
  unfold twoC gaussMul
  ext <;> ring

end SubNLogN.S2
