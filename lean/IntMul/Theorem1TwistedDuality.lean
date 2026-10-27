import IntMul.Preliminaries
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# `[MS]` Section 4.1: Proposition 4.1 — Polynomial-Transform Reduction (`F_{t_1, r} → t_1 F_r`)

This module is part of our independent formalization of `[MS]` Section 4.1 (Proposition 4.1)
(companion manuscript `[MS]`, *Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*):

1. **Twisted Root Property (`xi_pow_r_eq_neg_one`)**:
   For `ζ = exp(π i / r)` and `ξ_{u_2} = ζ^{2 u_2 - 1}`, we have `ξ_{u_2}^r = -1`, so
   `ξ_{u_2}^r + 1 = 0`.
2. **Negacyclic Quotient Ring Homomorphism (`phi_quotient_ringHom`)**:
   Because `ξ_{u_2}^r + 1 = 0`, polynomial evaluation `H(y) ↦ H(ξ_{u_2})` descends to a
   well-defined ring homomorphism `ϕ_{u_2} : ℂ[X] ⧸ Ideal.span {X^r + 1} →+* ℂ`.
3. **Twist & Twiddle Exponent Identities**:
   - Pre-twist × post-twist × `F_r` kernel: `ζ^{k_2} * (ζ^{-k_2} * e(k_2 u_2 / r)) = e(k_2 u_2 / r)`
     and `ζ^{-k_2} * e(k_2 u_2 / r) = ξ_{u_2}^{k_2}`.
   - Synthetic root evaluation: for `c_1 * t_1 = r`, `ξ_{u_2}^{2 c_1 j_1 v_1} = e(j_1 (2 u_2 - 1) v_1 / t_1)`.
   - Periodicity modulo `t_1`: for `u_1 ≡ (2 u_2 - 1) v_1 (mod t_1)`,
     `e(j_1 u_1 / t_1) = e(j_1 (2 u_2 - 1) v_1 / t_1)`.
4. **`[MS]` Proposition 4.1 (`theorem1_twisted_fourier_duality`; historical `theorem1_*` identifier retained)**:
   The 5-step Twisted Fourier-Duality pipeline (Pre-twist, Synthetic FFT `G_{t_1}`, Post-twist,
   `t_1` recursive 1D DFTs `F_r`, and Odd-Stride Permutation `u_1 = (2 u_2 - 1) v_1 mod t_1`)
   computes the exact 2D DFT `(F_{t_1, r} U)_{u_1, u_2}`.
5. **Odd-Stride Bijection (`odd_stride_bijection_zmod`)**:
   Since `2 u_2 - 1` is odd and `t_1 = 2^{k_1}`, `gcd(2 u_2 - 1, t_1) = 1` and the column permutation
   `v_1 ↦ (2 u_2 - 1) v_1 mod t_1` is a bijection on `ZMod t_1`.
-/

namespace IntMul

open scoped BigOperators
open Complex Real Polynomial

/-! ## 1. Twisted Roots of `-1` and the Quotient Ring Homomorphism `ϕ_{u_2}` (`[MS]` §4.1) -/

/-- The primitive `2r`-th root of unity `ζ_r = exp(π i / r) = stdChar(1 / (2r))`. -/
noncomputable def zetaRoot (r : ℕ) (k : ℝ) : ℂ :=
  stdChar (k / (2 * (r : ℝ)))

/-- The twisted evaluation point `ξ_{r, u_2}^k = ζ_r^{(2 u_2 - 1) k} = exp(π i (2 u_2 - 1) k / r)`. -/
noncomputable def xiPow (r : ℕ) (u2 : ℤ) (k : ℝ) : ℂ :=
  stdChar (((2 * (u2 : ℝ) - 1) * k) / (2 * (r : ℝ)))

/-- At `k = r` (with `r > 0`), `ζ_r^r = exp(π i) = -1`. -/
theorem zetaRoot_r_eq_neg_one (r : ℕ) (hr : 0 < r) :
    zetaRoot r (r : ℝ) = -1 := by
  unfold zetaRoot stdChar
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have h : (((2 * Real.pi * ((r : ℝ) / (2 * (r : ℝ))) : ℝ) : ℂ) * Complex.I) =
      Real.pi * Complex.I := by
    have hreal : 2 * Real.pi * ((r : ℝ) / (2 * (r : ℝ))) = Real.pi := by
      field_simp [hr_ne]
    rw [hreal]
  rw [h, Complex.exp_pi_mul_I]

/-- For any integer `u_2 ∈ ℤ` and `r > 0`, `ξ_{r, u_2}^r = (ζ_r^r)^{2 u_2 - 1} = -1`. -/
theorem xiPow_r_eq_neg_one (r : ℕ) (hr : 0 < r) (u2 : ℤ) :
    xiPow r u2 (r : ℝ) = -1 := by
  unfold xiPow
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hsplit : ((2 * (u2 : ℝ) - 1) * (r : ℝ)) / (2 * (r : ℝ)) =
      (-1 : ℝ) / 2 + (u2 : ℝ) := by
    field_simp [hr_ne]
    ring
  rw [hsplit, stdChar_add_int]
  unfold stdChar
  have hpi : (((2 * Real.pi * ((-1 : ℝ) / 2) : ℝ) : ℂ) * Complex.I) =
      -(Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hpi, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

/-- Algebraic version: for any `ξ : ℂ` satisfying `ξ^r = -1`, `ξ^r + 1 = 0`, so the ideal
`Ideal.span {X^r + 1}` is contained in the kernel of `aeval ξ : ℂ[X] →+* ℂ`, and `aeval ξ`
descends to a well-defined ring homomorphism `ϕ : ℂ[X] ⧸ Ideal.span {X^r + 1} →+* ℂ`. -/
noncomputable def phiQuotientRingHom (r : ℕ) (ξ : ℂ) (hξ : ξ ^ r = -1) :
    (ℂ[X] ⧸ Ideal.span ({X ^ r + 1} : Set ℂ[X])) →+* ℂ :=
  Ideal.Quotient.lift (Ideal.span ({X ^ r + 1} : Set ℂ[X]))
    (Polynomial.evalRingHom ξ)
    (by
      intro p hp
      rw [Ideal.mem_span_singleton] at hp
      rcases hp with ⟨q, rfl⟩
      simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one, hξ])

@[simp]
theorem phiQuotientRingHom_mk (r : ℕ) (ξ : ℂ) (hξ : ξ ^ r = -1) (P : ℂ[X]) :
    phiQuotientRingHom r ξ hξ (Ideal.Quotient.mk (Ideal.span ({X ^ r + 1} : Set ℂ[X])) P) =
      P.eval ξ :=
  rfl

/-! ## 2. Phase Identities for Pre-Twist, Post-Twist, and Synthetic Root Evaluation (`[MS]` §4.1) -/

/-- Post-twist combined with the 1D DFT kernel equals powers of the twisted root `ξ_{u_2}`:
`ζ^{-k_2} * e(k_2 u_2 / r) = ξ_{u_2}^{k_2}`. -/
theorem post_twist_mul_dft_kernel (r : ℕ) (hr : 0 < r) (u2 : ℤ) (k2 : ℝ) :
    zetaRoot r (-k2) * stdChar ((k2 * (u2 : ℝ)) / (r : ℝ)) = xiPow r u2 k2 := by
  unfold zetaRoot xiPow
  rw [← stdChar_add]
  congr 1
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  field_simp [hr_ne]
  ring

/-- Pre-twist multiplied by the twisted root power recovers the 2D DFT row kernel:
`ζ^{k_2} * ξ_{u_2}^{k_2} = e(k_2 u_2 / r)`. -/
theorem pre_twist_mul_xiPow (r : ℕ) (hr : 0 < r) (u2 : ℤ) (k2 : ℝ) :
    zetaRoot r k2 * xiPow r u2 k2 = stdChar ((k2 * (u2 : ℝ)) / (r : ℝ)) := by
  unfold zetaRoot xiPow
  rw [← stdChar_add]
  congr 1
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  field_simp [hr_ne]
  ring

/-- Evaluating the synthetic root power `y^{2 c_1 j_1 v_1}` at `y = ξ_{u_2}` when `c_1 * t_1 = r`
yields the 2D DFT column twiddle `e(j_1 * ((2 u_2 - 1) v_1) / t_1)`. -/
theorem xiPow_synthetic_twiddle (t1 r c1 : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (hc1 : c1 * t1 = r) (u2 j1 v1 : ℤ) :
    xiPow r u2 ((2 * (c1 : ℝ)) * (j1 : ℝ) * (v1 : ℝ)) =
      stdChar (((j1 : ℝ) * (((2 * u2 - 1) * v1 : ℤ) : ℝ)) / (t1 : ℝ)) := by
  unfold xiPow
  congr 1
  have ht1_ne : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hr_eq : (r : ℝ) = (c1 : ℝ) * (t1 : ℝ) := by exact_mod_cast hc1.symm
  have hc1_ne : (c1 : ℝ) ≠ 0 := fun h => hr_ne (by rw [hr_eq, h, zero_mul])
  push_cast
  rw [hr_eq]
  field_simp [ht1_ne, hc1_ne]

/-- Periodicity of `stdChar` modulo `t_1`: if `u_1 ≡ m (mod t_1)` (i.e. `m = u_1 + q * t_1`),
then `stdChar ((j_1 * m) / t_1) = stdChar ((j_1 * u_1) / t_1)`. -/
theorem stdChar_mod_t1_eq (t1 : ℕ) (ht1 : 0 < t1) (j1 u1 m q : ℤ)
    (hm : m = u1 + q * (t1 : ℤ)) :
    stdChar (((j1 : ℝ) * (m : ℝ)) / (t1 : ℝ)) =
      stdChar (((j1 : ℝ) * (u1 : ℝ)) / (t1 : ℝ)) := by
  have ht1_ne : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  have hm_real : (m : ℝ) = (u1 : ℝ) + (q : ℝ) * (t1 : ℝ) := by exact_mod_cast hm
  have hsplit : ((j1 : ℝ) * (m : ℝ)) / (t1 : ℝ) =
      ((j1 : ℝ) * (u1 : ℝ)) / (t1 : ℝ) + ((j1 * q : ℤ) : ℝ) := by
    rw [hm_real]
    push_cast
    field_simp [ht1_ne]
  rw [hsplit, stdChar_add_int]

/-! ## 3. `[MS]` Proposition 4.1: Polynomial-Transform Reduction (`F_{t_1, r} → t_1 F_r`, §4.1) -/

/-- The evaluated output `(q̂_{v_1})_{u_2}` of Step 4 in `[MS]` Proposition 4.1 (after Pre-twist, Synthetic FFT
evaluated via `ϕ_{u_2}`, Post-twist, and 1D DFT `F_r`). -/
noncomputable def twistedDualityStep4 (t1 r c1 : ℕ) (U : ℕ → ℕ → ℂ) (v1 u2 : ℕ) : ℂ :=
  (1 / (r : ℂ)) * (1 / (t1 : ℂ)) *
    ∑ j1 ∈ Finset.range t1,
      (∑ k2 ∈ Finset.range r,
        (zetaRoot r (k2 : ℝ) * U j1 k2) * xiPow r (u2 : ℤ) (k2 : ℝ)) *
      xiPow r (u2 : ℤ) ((2 * (c1 : ℝ)) * (j1 : ℝ) * (v1 : ℝ))

/-- **`[MS]` Proposition 4.1 (Polynomial-Transform / Twisted-Duality Reduction, §4.1)**:
Let `c_1 * t_1 = r` with `t_1, r > 0`. For any `v_1 < t_1` and `u_2 < r`, if `u_1 < t_1` satisfies
`(2 u_2 - 1) v_1 = u_1 + q * t_1` (i.e. `u_1 = (2 u_2 - 1) v_1 mod t_1`), then the Step 4 output
`twistedDualityStep4 t1 r c1 U v1 u2` equals the exact 2D DFT `(F_{t_1, r} U)_{u_1, u_2}`. -/
theorem theorem1_twisted_fourier_duality
    (t1 r c1 : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hc1 : c1 * t1 = r)
    (U : ℕ → ℕ → ℂ) (v1 u1 u2 : ℕ) (q : ℤ)
    (hu1 : (2 * (u2 : ℤ) - 1) * (v1 : ℤ) = (u1 : ℤ) + q * (t1 : ℤ)) :
    twistedDualityStep4 t1 r c1 U v1 u2 = dft2D t1 r U u1 u2 := by
  unfold twistedDualityStep4 dft2D
  have hcoeff : (1 / (r : ℂ)) * (1 / (t1 : ℂ)) = (1 / ((t1 * r : ℕ) : ℂ)) := by
    push_cast
    ring
  rw [hcoeff]
  congr 1
  refine Finset.sum_congr rfl fun j1 _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k2 _ => ?_
  have h1 : (zetaRoot r (k2 : ℝ) * U j1 k2) * xiPow r (u2 : ℤ) (k2 : ℝ) =
      U j1 k2 * (zetaRoot r (k2 : ℝ) * xiPow r (u2 : ℤ) (k2 : ℝ)) := by ring
  rw [h1, pre_twist_mul_xiPow r hr (u2 : ℤ) (k2 : ℝ)]
  have htwiddle :
      xiPow r (u2 : ℤ) (2 * (c1 : ℝ) * (j1 : ℝ) * (v1 : ℝ)) =
        stdChar (((j1 : ℝ) * (u1 : ℝ)) / (t1 : ℝ)) := by
    have htw := xiPow_synthetic_twiddle t1 r c1 ht1 hr hc1 (u2 : ℤ) (j1 : ℤ) (v1 : ℤ)
    have hmod := stdChar_mod_t1_eq t1 ht1 (j1 : ℤ) (u1 : ℤ) ((2 * (u2 : ℤ) - 1) * (v1 : ℤ)) q hu1
    have hcombined := htw.trans hmod
    simpa using hcombined
  rw [htwiddle]
  have hcast1 : ((j1 : ℝ) * (u1 : ℝ)) = ((j1 * u1 : ℕ) : ℝ) := by push_cast; ring
  have hcast2 : ((k2 : ℝ) * ((u2 : ℤ) : ℝ)) = ((k2 * u2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast1, hcast2]
  ring

/-- For any natural number `k : ℕ`, `xiPow r u2 (k : ℝ) = (xiPow r u2 1) ^ k`. -/
theorem xiPow_natCast_eq_pow (r : ℕ) (u2 : ℤ) (k : ℕ) :
    xiPow r u2 (k : ℝ) = (xiPow r u2 1) ^ k := by
  induction k with
  | zero =>
    unfold xiPow stdChar
    simp
  | succ k ih =>
    unfold xiPow at ih ⊢
    have h : ((2 * (u2 : ℝ) - 1) * ((k + 1 : ℕ) : ℝ)) / (2 * (r : ℝ)) =
        ((2 * (u2 : ℝ) - 1) * (k : ℝ)) / (2 * (r : ℝ)) +
        ((2 * (u2 : ℝ) - 1) * 1) / (2 * (r : ℝ)) := by
      push_cast
      ring
    rw [h, stdChar_add, ih, pow_succ]

/-- **`[MS]` Proposition 4.1 (Algorithmic Pipeline Equals `twistedDualityStep4`, §4.1)**:
Executing Step 1 (pre-twist `zetaRoot r k2 * U j1 k2`), Step 2 (multiplication-free Synthetic FFT
`syntheticDFT t1 r` over `R_r` using `negacyclicShiftIter`), Step 3 (post-twist `zetaRoot r (-k2)`),
and Step 4 (`dft1D r`) produces `twistedDualityStep4 t1 r c1 U v1 u2`. -/
theorem theorem1_pipeline_eq_step4
    (t1 r c1 : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hc1 : c1 * t1 = r)
    (U : ℕ → ℕ → ℂ) (v1 u2 : ℕ) :
    let P : ℕ → ℕ → ℂ := fun j1 k2 => zetaRoot r (k2 : ℝ) * U j1 k2
    let Q : ℕ → ℕ → ℂ := syntheticDFT t1 r P
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 => zetaRoot r (-(k2 : ℝ)) * Q v1 k2
    dft1D r (qPost v1) u2 = twistedDualityStep4 t1 r c1 U v1 u2 := by
  dsimp only
  unfold dft1D syntheticDFT twistedDualityStep4
  have hc1_div : r / t1 = c1 := by
    rw [← hc1, Nat.mul_div_cancel c1 ht1]
  rw [hc1_div]
  have hxi_r : (xiPow r (u2 : ℤ) 1) ^ r = -1 := by
    rw [← xiPow_natCast_eq_pow, xiPow_r_eq_neg_one r hr (u2 : ℤ)]
  have hsum :
      (∑ j ∈ Finset.range r,
        zetaRoot r (-(j : ℝ)) *
          (1 / (t1 : ℂ) * ∑ j1 ∈ Finset.range t1,
            negacyclicShiftIter r (2 * c1 * j1 * v1) (fun (k2 : ℕ) => zetaRoot r (k2 : ℝ) * U j1 k2) j) *
          stdChar ((j * u2 : ℕ) / (r : ℝ))) =
      (1 / (t1 : ℂ)) * ∑ j1 ∈ Finset.range t1,
        ∑ k2 ∈ Finset.range r,
          negacyclicShiftIter r (2 * c1 * j1 * v1) (fun (k : ℕ) => zetaRoot r (k : ℝ) * U j1 k) k2 *
            (xiPow r (u2 : ℤ) 1) ^ k2 := by
    calc (∑ j ∈ Finset.range r,
            zetaRoot r (-(j : ℝ)) *
              (1 / (t1 : ℂ) * ∑ j1 ∈ Finset.range t1,
                negacyclicShiftIter r (2 * c1 * j1 * v1) (fun (k2 : ℕ) => zetaRoot r (k2 : ℝ) * U j1 k2) j) *
              stdChar ((j * u2 : ℕ) / (r : ℝ)))
      _ = ∑ k2 ∈ Finset.range r,
            (1 / (t1 : ℂ)) * ∑ j1 ∈ Finset.range t1,
              negacyclicShiftIter r (2 * c1 * j1 * v1) (fun (k : ℕ) => zetaRoot r (k : ℝ) * U j1 k) k2 *
                (xiPow r (u2 : ℤ) 1) ^ k2 := by
          refine Finset.sum_congr rfl fun k2 _ => ?_
          have hpost := post_twist_mul_dft_kernel r hr (u2 : ℤ) (k2 : ℝ)
          have hcast : ((k2 * u2 : ℕ) : ℝ) / (r : ℝ) = ((k2 : ℝ) * ((u2 : ℤ) : ℝ)) / (r : ℝ) := by
            push_cast; ring
          rw [hcast, ← xiPow_natCast_eq_pow, ← hpost, ← Finset.sum_mul]
          ring
      _ = (1 / (t1 : ℂ)) * ∑ j1 ∈ Finset.range t1,
            ∑ k2 ∈ Finset.range r,
              negacyclicShiftIter r (2 * c1 * j1 * v1) (fun (k : ℕ) => zetaRoot r (k : ℝ) * U j1 k) k2 *
                (xiPow r (u2 : ℤ) 1) ^ k2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hsum, ← mul_assoc]
  congr 1
  refine Finset.sum_congr rfl fun j1 _ => ?_
  rw [negacyclicShiftIter_eval r (2 * c1 * j1 * v1) hr _ (xiPow r (u2 : ℤ) 1) hxi_r]
  have htw : (xiPow r (u2 : ℤ) 1) ^ (2 * c1 * j1 * v1) =
      xiPow r (u2 : ℤ) (2 * (c1 : ℝ) * (j1 : ℝ) * (v1 : ℝ)) := by
    rw [← xiPow_natCast_eq_pow]
    congr 1
    push_cast
    ring
  rw [htw, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun k2 _ => ?_
  rw [← xiPow_natCast_eq_pow]

/-- **`[MS]` Proposition 4.1 (Full Algorithmic Pipeline Computes `dft2D`, §4.1)**:
Composing Step 1 (pre-twist), Step 2 (`syntheticDFT` via `negacyclicShiftIter`), Step 3 (post-twist),
Step 4 (`dft1D r`), and Step 5 (odd-stride index `u1 ≡ (2 u2 - 1) v1 mod t1`) computes the exact
2D DFT `dft2D t1 r U u1 u2`. -/
theorem theorem1_pipeline_computes_dft2D
    (t1 r c1 : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hc1 : c1 * t1 = r)
    (U : ℕ → ℕ → ℂ) (v1 u1 u2 : ℕ) (q : ℤ)
    (hu1 : (2 * (u2 : ℤ) - 1) * (v1 : ℤ) = (u1 : ℤ) + q * (t1 : ℤ)) :
    let P : ℕ → ℕ → ℂ := fun j1 k2 => zetaRoot r (k2 : ℝ) * U j1 k2
    let Q : ℕ → ℕ → ℂ := syntheticDFT t1 r P
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 => zetaRoot r (-(k2 : ℝ)) * Q v1 k2
    dft1D r (qPost v1) u2 = dft2D t1 r U u1 u2 := by
  dsimp only
  rw [theorem1_pipeline_eq_step4 t1 r c1 ht1 hr hc1 U v1 u2,
      theorem1_twisted_fourier_duality t1 r c1 ht1 hr hc1 U v1 u1 u2 q hu1]

/-! ## 4. Bijectivity of the Odd-Stride Permutation `v_1 ↦ (2 u_2 + 1) v_1 mod 2^{k_1}` (`[MS]` §4.1, eq. (14)) -/

/-- Any odd natural number `2 * m + 1` is coprime to `2^{k_1}`. -/
theorem odd_coprime_two_pow (m k1 : ℕ) : Nat.Coprime (2 * m + 1) (2 ^ k1) := by
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_two_right]
  exact ⟨m, rfl⟩

/-- **`[MS]` Proposition 4.1 (Odd-Stride Column Bijection, §4.1, eq. (14))**:
For `t_1 = 2^{k_1}` and any odd stride `s = 2 m + 1`, the map `v_1 ↦ s * v_1` on `ZMod (2^{k_1})`
is a bijection (constructed as multiplication by a unit in `(ZMod (2^{k_1}))ˣ`). -/
def oddStrideEquiv (m k1 : ℕ) : ZMod (2 ^ k1) ≃ ZMod (2 ^ k1) :=
  let u : (ZMod (2 ^ k1))ˣ := ZMod.unitOfCoprime (2 * m + 1) (odd_coprime_two_pow m k1)
  { toFun := fun v1 => (u : ZMod (2 ^ k1)) * v1
    invFun := fun u1 => (↑u⁻¹ : ZMod (2 ^ k1)) * u1
    left_inv := fun v1 => by simp [← mul_assoc]
    right_inv := fun u1 => by simp [← mul_assoc] }

theorem oddStrideEquiv_bijective (m k1 : ℕ) :
    Function.Bijective (oddStrideEquiv m k1) :=
  (oddStrideEquiv m k1).bijective

/-- Concrete inverse of the odd-stride column permutation `v_1 ↦ (2 u_2 - 1) v_1 mod 2^{k_1}` (`[MS]` §4.1, eq. (14)):
maps `(u2, u1)` to `v1 < 2^{k_1}` such that `(2 u_2 - 1) v_1 ≡ u_1 (mod 2^{k_1})`. -/
def oddStrideInvPow2 (k1 u2 u1 : ℕ) : ℕ :=
  match u2 with
  | 0 => (-(u1 : ZMod (2 ^ k1))).val
  | m + 1 => ((oddStrideEquiv m k1).symm (u1 : ZMod (2 ^ k1))).val

/-- For any `k1, u2, u1 : ℕ`, `oddStrideInvPow2 k1 u2 u1` satisfies the odd-stride congruence
`(2 * u_2 - 1) * oddStrideInvPow2 k_1 u_2 u_1 = u_1 + q * 2^{k_1}` for some `q : ℤ`. -/
theorem oddStrideInvPow2_congr (k1 u2 u1 : ℕ) :
    ∃ q : ℤ,
      (2 * (u2 : ℤ) - 1) * (oddStrideInvPow2 k1 u2 u1 : ℤ) =
        (u1 : ℤ) + q * ((2 ^ k1 : ℕ) : ℤ) := by
  haveI : NeZero (2 ^ k1) := ⟨pow_ne_zero k1 (by decide)⟩
  have hz : (((2 * (u2 : ℤ) - 1) * (oddStrideInvPow2 k1 u2 u1 : ℤ) : ℤ) : ZMod (2 ^ k1)) =
      ((u1 : ℤ) : ZMod (2 ^ k1)) := by
    cases u2 with
    | zero =>
      dsimp [oddStrideInvPow2]
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    | succ m =>
      dsimp [oddStrideInvPow2]
      push_cast
      rw [ZMod.natCast_zmod_val]
      have h2m1 : (2 * ((m : ZMod (2 ^ k1)) + 1) - 1 : ZMod (2 ^ k1)) =
          ((2 * m + 1 : ℕ) : ZMod (2 ^ k1)) := by
        push_cast
        ring
      rw [h2m1]
      exact (oddStrideEquiv m k1).apply_symm_apply (u1 : ZMod (2 ^ k1))
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hz
  rcases hz with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  linarith

/-! ## 5. Multi-Stage Radix-2 Cooley-Tukey Synthetic FFT Equivalence (`syntheticFFTRadix2C` = `syntheticDFT`, `[MS]` §3.5, Lemma 3.5) -/

/-- `negacyclicShiftStep` is additive in the polynomial `B : ℕ → ℂ`. -/
theorem negacyclicShiftStep_add (r : ℕ) (A B : ℕ → ℂ) :
    negacyclicShiftStep r (fun k2 => A k2 + B k2) =
      fun k2 => negacyclicShiftStep r A k2 + negacyclicShiftStep r B k2 := by
  funext k2
  unfold negacyclicShiftStep
  split_ifs <;> ring

/-- `negacyclicShiftStep` commutes with scalar multiplication over `ℂ`. -/
theorem negacyclicShiftStep_smul (r : ℕ) (c : ℂ) (B : ℕ → ℂ) :
    negacyclicShiftStep r (fun k2 => c * B k2) =
      fun k2 => c * negacyclicShiftStep r B k2 := by
  funext k2
  unfold negacyclicShiftStep
  split_ifs <;> ring

/-- `negacyclicShiftIter` is additive in the polynomial `B : ℕ → ℂ`. -/
theorem negacyclicShiftIter_add (r s : ℕ) (A B : ℕ → ℂ) (k2 : ℕ) :
    negacyclicShiftIter r s (fun m => A m + B m) k2 =
      negacyclicShiftIter r s A k2 + negacyclicShiftIter r s B k2 := by
  induction s generalizing A B k2 with
  | zero => rfl
  | succ s ih =>
    simp only [negacyclicShiftIter, Function.iterate_succ_apply]
    rw [negacyclicShiftStep_add]
    exact ih _ _ k2

/-- `negacyclicShiftIter` commutes with scalar multiplication over `ℂ`. -/
theorem negacyclicShiftIter_smul (r s : ℕ) (c : ℂ) (B : ℕ → ℂ) (k2 : ℕ) :
    negacyclicShiftIter r s (fun m => c * B m) k2 =
      c * negacyclicShiftIter r s B k2 := by
  induction s generalizing B k2 with
  | zero => rfl
  | succ s ih =>
    simp only [negacyclicShiftIter, Function.iterate_succ_apply]
    rw [negacyclicShiftStep_smul]
    exact ih _ k2

/-- `negacyclicShiftIter` commutes with finite sums over `ℂ`. -/
theorem negacyclicShiftIter_sum {ι : Type*} (r s : ℕ) (S : Finset ι) (f : ι → ℕ → ℂ) (k2 : ℕ) :
    negacyclicShiftIter r s (fun m => ∑ i ∈ S, f i m) k2 =
      ∑ i ∈ S, negacyclicShiftIter r s (f i) k2 := by
  induction S using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    have := negacyclicShiftIter_smul r s 0 (fun _ => 0) k2
    simpa using this
  | cons a S ha ih =>
    simp only [Finset.sum_cons]
    rw [negacyclicShiftIter_add, ih]

/-- Iterated negacyclic shift satisfies the semigroup law: `s1 + s2` steps equals `s1` steps after `s2` steps. -/
theorem negacyclicShiftIter_add_steps (r s1 s2 : ℕ) (B : ℕ → ℂ) (k2 : ℕ) :
    negacyclicShiftIter r (s1 + s2) B k2 =
      negacyclicShiftIter r s1 (negacyclicShiftIter r s2 B) k2 := by
  unfold negacyclicShiftIter
  rw [Function.iterate_add_apply]

/-- Splitting a finite sum over `Finset.range (2 * n)` into even indices `2 * j` and odd indices `2 * j + 1`. -/
theorem sum_range_two_mul_even_odd {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∑ j ∈ Finset.range (2 * n), f j) =
      (∑ j ∈ Finset.range n, f (2 * j)) + (∑ j ∈ Finset.range n, f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    exact add_add_add_comm _ _ _ _

/-- Multi-stage Radix-2 Cooley-Tukey Synthetic FFT of depth `k` (`t_1 = 2^k`) over `ℂ[y]/(y^r + 1)`
with stride parameter `c1`:
recursively transforms the even-indexed (`P(2 j_1)`) and odd-indexed (`P(2 j_1 + 1)`) sub-arrays
with doubled stride `2 * c1`, and combines them via the addition-only negacyclic shift butterfly. -/
noncomputable def syntheticFFTRadix2C (r : ℕ) : ℕ → ℕ → (ℕ → ℕ → ℂ) → ℕ → ℕ → ℂ
  | 0, _, P, _, k2 => P 0 k2
  | k + 1, c1, P, v1, k2 =>
    let Y0 := syntheticFFTRadix2C r k (2 * c1) (fun j1 => P (2 * j1)) v1
    let Y1 := syntheticFFTRadix2C r k (2 * c1) (fun j1 => P (2 * j1 + 1)) v1
    (Y0 k2 + negacyclicShiftIter r (2 * c1 * v1) Y1 k2) / 2

/-- Direct 1D Synthetic DFT sum over `ℂ[y]/(y^r + 1)` parameterized by explicit stride `c1`:
`(1 / t_1) ∑_{j_1 < t_1} y^{2 c_1 j_1 v_1} P(j_1)(y) mod (y^r + 1)`. -/
noncomputable def syntheticDFTWithStride (t1 r c1 : ℕ) (P : ℕ → ℕ → ℂ) (v1 k2 : ℕ) : ℂ :=
  (1 / (t1 : ℂ)) * ∑ j1 ∈ Finset.range t1,
    negacyclicShiftIter r (2 * c1 * j1 * v1) (P j1) k2

/-- **Cooley-Tukey Radix-2 Synthetic FFT Equivalence (`syntheticFFTRadix2C` = `syntheticDFTWithStride`)**:
For any recursion depth `k1`, ring dimension `r`, stride `c1`, and polynomial array `P : ℕ → ℕ → ℂ`,
the `k1`-stage addition-only Radix-2 Cooley-Tukey Synthetic FFT `syntheticFFTRadix2C r k1 c1 P`
computes `syntheticDFTWithStride (2 ^ k1) r c1 P` identically. -/
theorem syntheticFFTRadix2C_eq_syntheticDFTWithStride
    (r k1 c1 : ℕ) (P : ℕ → ℕ → ℂ) (v1 k2 : ℕ) :
    syntheticFFTRadix2C r k1 c1 P v1 k2 =
      syntheticDFTWithStride (2 ^ k1) r c1 P v1 k2 := by
  induction k1 generalizing c1 P v1 k2 with
  | zero =>
    simp [syntheticFFTRadix2C, syntheticDFTWithStride, negacyclicShiftIter]
  | succ k ih =>
    dsimp only [syntheticFFTRadix2C]
    have hY0 : syntheticFFTRadix2C r k (2 * c1) (fun j1 => P (2 * j1)) v1 k2 =
        (1 / ((2 ^ k : ℕ) : ℂ)) * ∑ j1 ∈ Finset.range (2 ^ k),
          negacyclicShiftIter r (2 * c1 * (2 * j1) * v1) (P (2 * j1)) k2 := by
      rw [ih (2 * c1) (fun j1 => P (2 * j1)) v1 k2]
      unfold syntheticDFTWithStride
      congr 1
      refine Finset.sum_congr rfl fun j1 _ => ?_
      have hexp : 2 * (2 * c1) * j1 * v1 = 2 * c1 * (2 * j1) * v1 := by ring
      rw [hexp]
    have hY1_fun : syntheticFFTRadix2C r k (2 * c1) (fun j1 => P (2 * j1 + 1)) v1 =
        fun m => (1 / ((2 ^ k : ℕ) : ℂ)) * ∑ j1 ∈ Finset.range (2 ^ k),
          negacyclicShiftIter r (2 * (2 * c1) * j1 * v1) (P (2 * j1 + 1)) m := by
      funext m
      exact ih (2 * c1) (fun j1 => P (2 * j1 + 1)) v1 m
    have hY1 : negacyclicShiftIter r (2 * c1 * v1)
        (syntheticFFTRadix2C r k (2 * c1) (fun j1 => P (2 * j1 + 1)) v1) k2 =
        (1 / ((2 ^ k : ℕ) : ℂ)) * ∑ j1 ∈ Finset.range (2 ^ k),
          negacyclicShiftIter r (2 * c1 * (2 * j1 + 1) * v1) (P (2 * j1 + 1)) k2 := by
      rw [hY1_fun, negacyclicShiftIter_smul, negacyclicShiftIter_sum]
      congr 1
      refine Finset.sum_congr rfl fun j1 _ => ?_
      rw [← negacyclicShiftIter_add_steps]
      have hexp : 2 * c1 * v1 + 2 * (2 * c1) * j1 * v1 = 2 * c1 * (2 * j1 + 1) * v1 := by ring
      rw [hexp]
    rw [hY0, hY1]
    unfold syntheticDFTWithStride
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hpow, sum_range_two_mul_even_odd (2 ^ k)
      (fun j1 => negacyclicShiftIter r (2 * c1 * j1 * v1) (P j1) k2)]
    push_cast
    ring

/-- **Main Radix-2 Cooley-Tukey Synthetic FFT Equivalence (`syntheticFFTRadix2C` = `syntheticDFT`)**:
At `c1 = r / 2 ^ k1`, the `k1`-stage addition-only Radix-2 Cooley-Tukey Synthetic FFT
`syntheticFFTRadix2C r k1 (r / 2 ^ k1) P` equals `syntheticDFT (2 ^ k1) r P` identically. -/
theorem syntheticFFTRadix2C_eq_syntheticDFT
    (k1 r : ℕ) (P : ℕ → ℕ → ℂ) (v1 k2 : ℕ) :
    syntheticFFTRadix2C r k1 (r / 2 ^ k1) P v1 k2 =
      syntheticDFT (2 ^ k1) r P v1 k2 :=
  syntheticFFTRadix2C_eq_syntheticDFTWithStride r k1 (r / 2 ^ k1) P v1 k2

/-- Multi-stage per-stage-rounded Radix-2 Cooley-Tukey Synthetic FFT of depth `k` (`t_1 = 2^k`)
over `ℂ[y]/(y^r + 1)` with stride parameter `c1` and stage-rounding precision `pSub`:
recursively transforms the even-indexed (`P(2 j_1)`) and odd-indexed (`P(2 j_1 + 1)`) sub-arrays
with doubled stride `2 * c1`, and combines them via the addition-only negacyclic shift butterfly
followed by `complexQuantize pSub` at every butterfly stage (`[MS]` Lemma 3.5, §3.5 & Proposition 4.1, §4.1). -/
noncomputable def syntheticFFTRadix2Quantized (pSub r : ℕ) : ℕ → ℕ → (ℕ → ℕ → ℂ) → ℕ → ℕ → ℂ
  | 0, _, P, _, k2 => P 0 k2
  | k + 1, c1, P, v1, k2 =>
    let Y0 := syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1)) v1
    let Y1 := syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1 + 1)) v1
    complexQuantize pSub ((Y0 k2 + negacyclicShiftIter r (2 * c1 * v1) Y1 k2) / 2)

/-- **Multi-Stage Butterfly Rounding Error Bound for `syntheticFFTRadix2Quantized` (`[MS]` Lemma 3.5, §3.5, eq. (13) & Lemma 6.5, §6.3, Term B3)**:
Across `k` Radix-2 Synthetic FFT butterfly stages over `ℂ[y]/(y^r + 1)` (`0 < r`), if the input
array `P` satisfies `∀ j1 < 2 ^ k, ∀ m < r, ‖P j1 m - P_unq j1 m‖ ≤ ε0`, then each stage
averages two `ℓ_∞`-nonexpansive sub-results and rounds via `complexQuantize pSub`, accumulating at most
`k * complexQuantizeMaxErr pSub` additional rounding error:
`‖syntheticFFTRadix2Quantized pSub r k c1 P v1 k2 - syntheticFFTRadix2C r k c1 P_unq v1 k2‖ ≤ ε0 + (k : ℝ) * complexQuantizeMaxErr pSub`. -/
theorem norm_syntheticFFTRadix2Quantized_sub_le
    (pSub r k c1 : ℕ) (hr : 0 < r) (P P_unq : ℕ → ℕ → ℂ) (ε0 : ℝ)
    (hP : ∀ j1 < 2 ^ k, ∀ m < r, ‖P j1 m - P_unq j1 m‖ ≤ ε0)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    ‖syntheticFFTRadix2Quantized pSub r k c1 P v1 k2 -
      syntheticFFTRadix2C r k c1 P_unq v1 k2‖ ≤
      ε0 + (k : ℝ) * complexQuantizeMaxErr pSub := by
  induction k generalizing c1 P P_unq k2 with
  | zero =>
    simp only [syntheticFFTRadix2Quantized, syntheticFFTRadix2C, Nat.cast_zero, zero_mul, add_zero]
    exact hP 0 (by simp) k2 hk2
  | succ k ih =>
    dsimp only [syntheticFFTRadix2Quantized, syntheticFFTRadix2C]
    set Y0 := syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1)) v1
    set Y1 := syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1 + 1)) v1
    set Y0_unq := syntheticFFTRadix2C r k (2 * c1) (fun j1 => P_unq (2 * j1)) v1
    set Y1_unq := syntheticFFTRadix2C r k (2 * c1) (fun j1 => P_unq (2 * j1 + 1)) v1
    have hY0 : ‖Y0 k2 - Y0_unq k2‖ ≤ ε0 + (k : ℝ) * complexQuantizeMaxErr pSub := by
      refine ih (2 * c1) (fun j1 => P (2 * j1)) (fun j1 => P_unq (2 * j1)) (fun j1 hj1 m hm => ?_) k2 hk2
      exact hP (2 * j1) (by rw [pow_succ']; omega) m hm
    have hY1 : ∀ m < r, ‖Y1 m - Y1_unq m‖ ≤ ε0 + (k : ℝ) * complexQuantizeMaxErr pSub := by
      intro m hm
      refine ih (2 * c1) (fun j1 => P (2 * j1 + 1)) (fun j1 => P_unq (2 * j1 + 1)) (fun j1 hj1 m' hm' => ?_) m hm
      exact hP (2 * j1 + 1) (by rw [pow_succ']; omega) m' hm'
    have hshift :
        ‖negacyclicShiftIter r (2 * c1 * v1) Y1 k2 -
          negacyclicShiftIter r (2 * c1 * v1) Y1_unq k2‖ ≤
          ε0 + (k : ℝ) * complexQuantizeMaxErr pSub := by
      rw [negacyclicShiftIter_sub]
      exact norm_negacyclicShiftIter_le r (2 * c1 * v1) hr (fun m => Y1 m - Y1_unq m)
        (ε0 + (k : ℝ) * complexQuantizeMaxErr pSub) hY1 k2 hk2
    set avg := (Y0 k2 + negacyclicShiftIter r (2 * c1 * v1) Y1 k2) / 2
    set avg_unq := (Y0_unq k2 + negacyclicShiftIter r (2 * c1 * v1) Y1_unq k2) / 2
    have havg_diff :
        avg - avg_unq =
          ((Y0 k2 - Y0_unq k2) +
            (negacyclicShiftIter r (2 * c1 * v1) Y1 k2 -
              negacyclicShiftIter r (2 * c1 * v1) Y1_unq k2)) / 2 := by
      dsimp [avg, avg_unq]
      ring
    have havg_norm : ‖avg - avg_unq‖ ≤ ε0 + (k : ℝ) * complexQuantizeMaxErr pSub := by
      rw [havg_diff, norm_div, Complex.norm_ofNat]
      have htri := norm_add_le (Y0 k2 - Y0_unq k2)
        (negacyclicShiftIter r (2 * c1 * v1) Y1 k2 - negacyclicShiftIter r (2 * c1 * v1) Y1_unq k2)
      linarith
    have hq : ‖complexQuantize pSub avg - avg‖ ≤ complexQuantizeMaxErr pSub :=
      norm_complexQuantize_sub_le pSub avg
    have hsplit : complexQuantize pSub avg - avg_unq =
        (complexQuantize pSub avg - avg) + (avg - avg_unq) := by ring
    have htri2 := norm_add_le (complexQuantize pSub avg - avg) (avg - avg_unq)
    rw [← hsplit] at htri2
    push_cast
    linarith

/-- **Multi-Stage Norm Bound for `syntheticFFTRadix2Quantized` (`[MS]` Lemma 3.5, §3.5 & Lemma 6.5, §6.3)**:
Across `k` Radix-2 Synthetic FFT butterfly stages over `ℂ[y]/(y^r + 1)` (`0 < r`), if the input
array `P` satisfies `∀ j1 < 2 ^ k, ∀ m < r, ‖P j1 m‖ ≤ M_P`, then for all `k2 < r`,
`‖syntheticFFTRadix2Quantized pSub r k c1 P v1 k2‖ ≤ M_P + (k : ℝ) * complexQuantizeMaxErr pSub`. -/
theorem norm_syntheticFFTRadix2Quantized_le
    (pSub r k c1 : ℕ) (hr : 0 < r) (P : ℕ → ℕ → ℂ) (M_P : ℝ)
    (hP : ∀ j1 < 2 ^ k, ∀ m < r, ‖P j1 m‖ ≤ M_P)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    ‖syntheticFFTRadix2Quantized pSub r k c1 P v1 k2‖ ≤
      M_P + (k : ℝ) * complexQuantizeMaxErr pSub := by
  induction k generalizing c1 P k2 with
  | zero =>
    simp only [syntheticFFTRadix2Quantized, Nat.cast_zero, zero_mul, add_zero]
    exact hP 0 (by simp) k2 hk2
  | succ k ih =>
    dsimp only [syntheticFFTRadix2Quantized]
    set Y0 := syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1)) v1
    set Y1 := syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1 + 1)) v1
    have hY0 : ‖Y0 k2‖ ≤ M_P + (k : ℝ) * complexQuantizeMaxErr pSub :=
      ih (2 * c1) (fun j1 => P (2 * j1))
        (fun j1 hj1 m hm => hP (2 * j1) (by rw [pow_succ']; omega) m hm) k2 hk2
    have hY1 : ∀ m < r, ‖Y1 m‖ ≤ M_P + (k : ℝ) * complexQuantizeMaxErr pSub :=
      fun m hm => ih (2 * c1) (fun j1 => P (2 * j1 + 1))
        (fun j1 hj1 m' hm' => hP (2 * j1 + 1) (by rw [pow_succ']; omega) m' hm') m hm
    have hshift : ‖negacyclicShiftIter r (2 * c1 * v1) Y1 k2‖ ≤
        M_P + (k : ℝ) * complexQuantizeMaxErr pSub :=
      norm_negacyclicShiftIter_le r (2 * c1 * v1) hr Y1
        (M_P + (k : ℝ) * complexQuantizeMaxErr pSub) hY1 k2 hk2
    set avg := (Y0 k2 + negacyclicShiftIter r (2 * c1 * v1) Y1 k2) / 2
    have havg : ‖avg‖ ≤ M_P + (k : ℝ) * complexQuantizeMaxErr pSub := by
      dsimp [avg]
      rw [norm_div, Complex.norm_ofNat]
      have htri := norm_add_le (Y0 k2) (negacyclicShiftIter r (2 * c1 * v1) Y1 k2)
      linarith
    have hq : ‖complexQuantize pSub avg - avg‖ ≤ complexQuantizeMaxErr pSub :=
      norm_complexQuantize_sub_le pSub avg
    have htri2 := norm_add_le (complexQuantize pSub avg - avg) avg
    rw [sub_add_cancel] at htri2
    push_cast
    linarith

/-- **Multi-Stage `syntheticFFTRadix2Quantized` vs. Exact `syntheticDFT` Error Bound (`norm_syntheticFFTRadix2Quantized_sub_syntheticDFT_le`)**:
When `2 ^ (Nat.log2 t1) = t1` and `0 < r`, if `∀ j1 < t1, ∀ m < r, ‖P j1 m - P_unq j1 m‖ ≤ ε0`, then for all `k2 < r`,
`‖complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2) - syntheticDFT t1 r P_unq v1 k2‖ ≤ ε0 + ((Nat.log2 t1 : ℝ) + 1) * complexQuantizeMaxErr pSub`. -/
theorem norm_syntheticFFTRadix2Quantized_sub_syntheticDFT_le
    (pSub t1 r : ℕ) (ht1_pow : 2 ^ (Nat.log2 t1) = t1) (hr : 0 < r)
    (P P_unq : ℕ → ℕ → ℂ) (ε0 : ℝ)
    (hP : ∀ j1 < t1, ∀ m < r, ‖P j1 m - P_unq j1 m‖ ≤ ε0)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    ‖complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2) -
      syntheticDFT t1 r P_unq v1 k2‖ ≤
      ε0 + ((Nat.log2 t1 : ℝ) + 1) * complexQuantizeMaxErr pSub := by
  have h_eq : syntheticDFT t1 r P_unq v1 k2 =
      syntheticFFTRadix2C r (Nat.log2 t1) (r / t1) P_unq v1 k2 := by
    have h1 := (syntheticFFTRadix2C_eq_syntheticDFT (Nat.log2 t1) r P_unq v1 k2).symm
    rwa [ht1_pow] at h1
  rw [h_eq]
  set w := syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2
  set w_unq := syntheticFFTRadix2C r (Nat.log2 t1) (r / t1) P_unq v1 k2
  have h1 : ‖complexQuantize pSub w - w‖ ≤ complexQuantizeMaxErr pSub :=
    norm_complexQuantize_sub_le pSub w
  have h2 : ‖w - w_unq‖ ≤ ε0 + (Nat.log2 t1 : ℝ) * complexQuantizeMaxErr pSub :=
    norm_syntheticFFTRadix2Quantized_sub_le pSub r (Nat.log2 t1) (r / t1) hr P P_unq ε0
      (fun j1 hj1 m hm => hP j1 (ht1_pow ▸ hj1) m hm) v1 k2 hk2
  have hsplit : complexQuantize pSub w - w_unq = (complexQuantize pSub w - w) + (w - w_unq) := by
    ring
  have htri := norm_add_le (complexQuantize pSub w - w) (w - w_unq)
  rw [← hsplit] at htri
  linarith

end IntMul
