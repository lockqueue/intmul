import IntMul.Preliminaries
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Group.Integral

/-!
# `[MS]` Section 4.2: Theorem 4.2 — CRT-Free Fractional-Shift Poisson Identity (`F_{t_1 r} ↔ F_{t_1, r}`)

This module is part of our independent formalization of `[MS]` Section 4.2 (Theorem 4.2)
(companion manuscript `[MS]`, *Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*):

1. **Windowed Sinc-Gaussian (Cardinal Box-Gaussian) Kernel (`[MS]` §4.2, eq. (15))**:
   - `normSinc t = sin(π t) / (π t)` (`normSinc 0 = 1`), proved even and bounded by `1 / (π |t|)`.
   - `sincGaussian α t = normSinc t * exp(-π t^2 / α^2)`, proved even with `sincGaussian α 0 = 1`.
2. **Lattice Folding Periodicity (`stdChar_lattice_fold`)**:
   - `stdChar (((k2 + l * r) * u2) / r) = stdChar ((k2 * u2) / r)` for all `l ∈ ℤ`.
3. **Shift-Modulation Phase Factorization (`shift_modulation_phase_factor`)**:
   - For `z, ξ, m, t : ℝ`, `stdChar ((ξ - m) * t) = stdChar (-(ξ - m) * (z - t)) * stdChar ((ξ - m) * z)`.
4. **2D-to-1D Fractional-Shift Phase Congruence (`fractional_shift_phase_identity`)**:
   - For `R = t_1 r` and `u_1 - m = u_1_tilde + q * t_1`,
     `stdChar (j_1 u_1 / t_1) * stdChar ((j_2 + j_1 / t_1) * (u_2 / r - m)) =
      stdChar (((j_1 + t_1 j_2) * (u_2 + r u_1_tilde)) / (t_1 r))`.
5. **`[MS]` Theorem 4.2 (`theorem2_fractional_shift_poisson_identity`, `theorem2_continuous_poisson_to_dft1DGrid`; historical `theorem2_*` identifier retained)**:
   - Proves that under the 1D fractional-shift Poisson summation expansion along the second
     coordinate, the 2D DFT `(F_{t_1, r} x̃)_{u_1, u_2}` equals the Poisson alias series of the 1D
     DFT `(F_{t_1 r} x)_{u_2 + r ((u_1 - m) mod t_1)}`.
6. **Discrete Fourier Orthogonality, Idealized 2-Term Passband Spreading, & Midpoint Orthogonality**:
   - `stdChar_orthogonality_range`, `spreadArray2Tap`, `dft2D_spreadArray2Tap_eq`, and
     `dft1DGrid_alternating_sum_eq_midpoint`.
-/

namespace IntMul

open scoped BigOperators FourierTransform
open Complex Real MeasureTheory

/-! ## 1. The Windowed Sinc-Gaussian (Cardinal Box-Gaussian) Kernel (`[MS]` §4.2, eqs. (15)–(16)) -/

/-- Normalized cardinal sine `sinc(t) = sin(π t) / (π t)` with `sinc(0) = 1`. -/
noncomputable def normSinc (t : ℝ) : ℝ :=
  if t = 0 then 1 else Real.sin (Real.pi * t) / (Real.pi * t)

@[simp]
theorem normSinc_zero : normSinc 0 = 1 := by
  simp [normSinc]

/-- `normSinc` is an even function: `normSinc (-t) = normSinc t`. -/
theorem normSinc_even (t : ℝ) : normSinc (-t) = normSinc t := by
  unfold normSinc
  by_cases ht : t = 0
  · simp [ht]
  · have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
    simp only [ht, hnt, ↓reduceIte, mul_neg, Real.sin_neg, neg_div_neg_eq]

/-- For `t ≠ 0`, `|normSinc t| ≤ 1 / (π * |t|)` (used in `[MS]` Lemma 6.1's spatial tail bound, §6.1). -/
theorem abs_normSinc_le_inv_pi_abs (t : ℝ) (ht : t ≠ 0) :
    |normSinc t| ≤ 1 / (Real.pi * |t|) := by
  unfold normSinc
  rw [if_neg ht, abs_div, abs_mul, abs_of_pos Real.pi_pos]
  have hdenom : 0 < Real.pi * |t| := mul_pos Real.pi_pos (abs_pos.mpr ht)
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one (Real.pi * t)) hdenom.le

/-- The Windowed Sinc-Gaussian (Cardinal Box-Gaussian) Kernel (`[MS]` §4.2, eq. (15)):
`g(t) = sinc(t) * exp(-(π / α^2) * t^2)`. -/
noncomputable def sincGaussian (α t : ℝ) : ℝ :=
  normSinc t * Real.exp (-(Real.pi / α ^ 2) * t ^ 2)

@[simp]
theorem sincGaussian_zero (α : ℝ) : sincGaussian α 0 = 1 := by
  simp [sincGaussian]

/-- `sincGaussian α` is an even function: `sincGaussian α (-t) = sincGaussian α t`. -/
theorem sincGaussian_even (α t : ℝ) : sincGaussian α (-t) = sincGaussian α t := by
  unfold sincGaussian
  rw [normSinc_even, neg_sq]

/-- For `t ≠ 0`, `|sincGaussian α t| ≤ (1 / (π * |t|)) * exp(-(π / α^2) * t^2)`. -/
theorem abs_sincGaussian_le (α t : ℝ) (ht : t ≠ 0) :
    |sincGaussian α t| ≤ (1 / (Real.pi * |t|)) * Real.exp (-(Real.pi / α ^ 2) * t ^ 2) := by
  unfold sincGaussian
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (abs_normSinc_le_inv_pi_abs t ht) (Real.exp_pos _).le

/-- Alias `realSinc` for the normalized cardinal sine `normSinc`. -/
noncomputable abbrev realSinc : ℝ → ℝ := normSinc

/-- `normSinc t` equals `Real.sinc (π * t)`. -/
theorem normSinc_eq_sinc (t : ℝ) : normSinc t = Real.sinc (Real.pi * t) := by
  unfold normSinc Real.sinc
  have h : Real.pi * t = 0 ↔ t = 0 := mul_eq_zero_iff_left Real.pi_ne_zero
  simp [h]

/-- Uniform bound `|realSinc t| ≤ 1` for all `t : ℝ`. -/
theorem abs_realSinc_le_one (t : ℝ) : |realSinc t| ≤ 1 := by
  unfold realSinc
  rw [normSinc_eq_sinc]
  exact Real.abs_sinc_le_one (Real.pi * t)

/-- Continuity of `realSinc` on `ℝ`. -/
theorem continuous_realSinc : Continuous realSinc := by
  have h : realSinc = fun t => Real.sinc (Real.pi * t) := funext normSinc_eq_sinc
  rw [h]
  exact Real.continuous_sinc.comp (continuous_const.mul continuous_id)

/-- **Interval Integral Representation of `realSinc` (`[MS]` §4.2, proof of Theorem 4.2)**:
For all `t : ℝ`, the normalized cardinal sine `realSinc t = sin(π t) / (π t)` equals the Fourier
transform of the unit box `1_{[-1/2, 1/2]}`:
`(realSinc t : ℂ) = ∫ ν in (-1/2)..(1/2), exp(2π i t ν)`. -/
theorem realSinc_eq_intervalIntegral (t : ℝ) :
    (realSinc t : ℂ) =
      ∫ ν in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (ν : ℂ)) := by
  by_cases ht : t = 0
  · subst ht
    simp [realSinc, normSinc]
    norm_num
  · unfold realSinc normSinc
    rw [if_neg ht]
    set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
    have hc : c ≠ 0 := by
      dsimp [c]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact Complex.ofReal_ne_zero.mpr ht
    have hint := integral_exp_mul_complex (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) hc
    have hcongr :
        (∫ ν in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (ν : ℂ))) =
        ∫ ν in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Complex.exp (c * (ν : ℂ)) := rfl
    rw [hcongr, hint]
    have h1 : c * ((1 / 2 : ℝ) : ℂ) = ((Real.pi : ℂ) * (t : ℂ)) * Complex.I := by
      dsimp [c]; push_cast; ring
    have h2 : c * ((-1 / 2 : ℝ) : ℂ) = (-((Real.pi : ℂ) * (t : ℂ))) * Complex.I := by
      dsimp [c]; push_cast; ring
    rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    dsimp [c]
    have hpi_c : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have ht_c : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp [hpi_c, ht_c, hI]
    ring

/-- Mathlib's continuous Fourier transform `𝓕 g w` equals the Lebesgue integral
`∫ t : ℝ, stdChar (-(t * w)) * g t`. -/
theorem fourier_eq_integral_stdChar (g : ℝ → ℂ) (w : ℝ) :
    𝓕 g w = ∫ t : ℝ, stdChar (-(t * w)) * g t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1 with t
  rw [smul_eq_mul]
  congr 1
  unfold stdChar
  congr 1
  push_cast
  ring

/-- **Continuous Fourier Transform of `sincGaussian` Equals the Box-Gaussian Integral (`[MS]` §4.2, eq. (16))**:
For `α > 0` and `ξ : ℝ`, the continuous Lebesgue Fourier transform `𝓕 (sincGaussian α) ξ` equals
the Box-Gaussian interval integral
`(1 / √π) ∫_{√π α (ξ - 1/2)}^{√π α (ξ + 1/2)} exp(-u^2) du`.
Proved from first principles via `realSinc_eq_intervalIntegral`, Fubini's theorem
(`MeasureTheory.intervalIntegral_integral_swap`), and the complex quadratic Gaussian integral
(`integral_cexp_quadratic`). -/
theorem fourier_sincGaussian_eq_box_gaussian_integral (α ξ : ℝ) (hα : 0 < α) :
    (𝓕 fun t : ℝ => (sincGaussian α t : ℂ)) ξ =
      (((1 / Real.sqrt Real.pi) *
        ∫ u in (Real.sqrt Real.pi * α * (ξ - 1 / 2))..(Real.sqrt Real.pi * α * (ξ + 1 / 2)),
          Real.exp (-(u ^ 2)) : ℝ) : ℂ) := by
  rw [fourier_eq_integral_stdChar]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  set a : ℝ := Real.pi / α ^ 2
  have ha : 0 < a := div_pos hpi (sq_pos_of_pos hα)
  let H : ℝ → ℝ → ℂ := fun ν t =>
    Complex.exp ((-a : ℂ) * (t : ℂ) ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I * ((ν : ℂ) - (ξ : ℂ))) * (t : ℂ) + 0)
  have h_inner_rep : ∀ t : ℝ,
      stdChar (-(t * ξ)) * (sincGaussian α t : ℂ) =
        ∫ ν in (-1 / 2 : ℝ)..(1 / 2 : ℝ), H ν t := by
    intro t
    unfold sincGaussian
    rw [Complex.ofReal_mul]
    change stdChar (-(t * ξ)) * ((realSinc t : ℂ) * ((Real.exp (-a * t ^ 2) : ℝ) : ℂ)) = _
    rw [realSinc_eq_intervalIntegral t, Complex.ofReal_exp, ← mul_assoc,
        ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun ν _ => ?_
    unfold stdChar
    dsimp [H]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h_inner_rep]
  let μ : Measure ℝ := volume.restrict (Set.uIoc (-1 / 2 : ℝ) (1 / 2 : ℝ))
  have h_int : Integrable (Function.uncurry H) (μ.prod volume) := by
    have hcont_H : Continuous (Function.uncurry H) := by
      unfold Function.uncurry
      dsimp [H]
      fun_prop
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrableOn_const (by simp)
    have h2 : Integrable (fun t : ℝ => Real.exp (-a * t ^ 2)) volume :=
      integrable_exp_neg_mul_sq ha
    refine (h1.mul_prod h2).mono' hcont_H.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have hsplit : Function.uncurry H p =
        Complex.exp (((-a * p.2 ^ 2 : ℝ) : ℂ)) *
          Complex.exp (((2 * Real.pi * (p.1 - ξ) * p.2 : ℝ) : ℂ) * Complex.I) := by
      dsimp [Function.uncurry, H]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit, norm_mul, ← Complex.ofReal_exp, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_exp_ofReal_mul_I, mul_one, one_mul]
  rw [← intervalIntegral_integral_swap h_int]
  have h_eval_t : ∀ ν : ℝ,
      (∫ t : ℝ, H ν t) =
        ((α * Real.exp (-((Real.sqrt Real.pi * α * (ξ - ν)) ^ 2)) : ℝ) : ℂ) := by
    intro ν
    dsimp [H]
    have hb_re : (-a : ℂ).re < 0 := by simpa using ha
    rw [integral_cexp_quadratic hb_re
      (2 * (Real.pi : ℂ) * Complex.I * ((ν : ℂ) - (ξ : ℂ))) 0]
    have h_prefactor : ((Real.pi : ℂ) / -(-a : ℂ)) ^ (1 / 2 : ℂ) = (α : ℂ) := by
      have hdiv : (Real.pi : ℂ) / -(-a : ℂ) = ((α ^ 2 : ℝ) : ℂ) := by
        dsimp [a]
        push_cast
        have hpi_c : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
        have hα_c : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
        field_simp [hpi_c, hα_c]
      rw [hdiv]
      have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hhalf, ← Complex.ofReal_cpow (sq_nonneg α), ← Real.sqrt_eq_rpow, Real.sqrt_sq hα.le]
    have h_exp_arg :
        0 - (2 * (Real.pi : ℂ) * Complex.I * ((ν : ℂ) - (ξ : ℂ))) ^ 2 / (4 * (-a : ℂ)) =
        ((-((Real.sqrt Real.pi * α * (ξ - ν)) ^ 2) : ℝ) : ℂ) := by
      dsimp [a]
      have hsq_pi : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt hpi.le
      have hrew : (Real.sqrt Real.pi * α * (ξ - ν)) ^ 2 = Real.pi * α ^ 2 * (ξ - ν) ^ 2 := by
        calc (Real.sqrt Real.pi * α * (ξ - ν)) ^ 2
            = (Real.sqrt Real.pi) ^ 2 * α ^ 2 * (ξ - ν) ^ 2 := by ring
          _ = Real.pi * α ^ 2 * (ξ - ν) ^ 2 := by rw [hsq_pi]
      rw [hrew]
      push_cast
      have hpi_c : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      have hα_c : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
      have hI2 : (2 * (Real.pi : ℂ) * Complex.I * ((ν : ℂ) - (ξ : ℂ))) ^ 2 =
          -4 * (Real.pi : ℂ) ^ 2 * ((ν : ℂ) - (ξ : ℂ)) ^ 2 := by
        calc (2 * (Real.pi : ℂ) * Complex.I * ((ν : ℂ) - (ξ : ℂ))) ^ 2
            = 4 * (Real.pi : ℂ) ^ 2 * Complex.I ^ 2 * ((ν : ℂ) - (ξ : ℂ)) ^ 2 := by ring
          _ = -4 * (Real.pi : ℂ) ^ 2 * ((ν : ℂ) - (ξ : ℂ)) ^ 2 := by rw [Complex.I_sq]; ring
      rw [hI2]
      field_simp [hpi_c, hα_c]
      ring
    rw [h_prefactor, h_exp_arg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  simp_rw [h_eval_t, intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_sub_left
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (fun w : ℝ => Real.exp (-((Real.sqrt Real.pi * α * w) ^ 2))) ξ
  have h_sub_top : ξ - (-1 / 2 : ℝ) = ξ + 1 / 2 := by ring
  rw [hsub, h_sub_top]
  have hc_ne : Real.sqrt Real.pi * α ≠ 0 := (mul_pos hsqrt_pi hα).ne'
  have hmul := intervalIntegral.integral_comp_mul_left
    (a := ξ - 1 / 2) (b := ξ + 1 / 2)
    (fun u : ℝ => Real.exp (-(u ^ 2))) hc_ne
  rw [hmul, smul_eq_mul]
  have hpi_ne : Real.sqrt Real.pi ≠ 0 := hsqrt_pi.ne'
  have hα_ne : α ≠ 0 := hα.ne'
  field_simp [hpi_ne, hα_ne]

/-- **Unconditional Spatial Norm-Summability of Modulated `sincGaussian` over `ℤ` (`[MS]` §4.2, Theorem 4.2 & §6.1, Lemma 6.1)**:
For any `α > 0` and `x0, y : ℝ`, the spatial lattice series
`k ↦ ‖(sincGaussian α (x0 - k) : ℂ) * stdChar (y * k)‖` is unconditionally summable over `ℤ`. -/
theorem summable_norm_sincGaussian_modulated (α x0 y : ℝ) (hα : 0 < α) :
    Summable (fun k : ℤ =>
      ‖(sincGaussian α (x0 - (k : ℝ)) : ℂ) * stdChar (y * (k : ℝ))‖) := by
  set a : ℝ := Real.pi / α ^ 2
  have ha : 0 < a := div_pos Real.pi_pos (sq_pos_of_pos hα)
  have hle : ∀ k : ℤ,
      ‖(sincGaussian α (x0 - (k : ℝ)) : ℂ) * stdChar (y * (k : ℝ))‖ ≤
        Real.exp (-a * (x0 - (k : ℝ)) ^ 2) := by
    intro k
    rw [norm_mul, norm_stdChar, mul_one, Complex.norm_real, Real.norm_eq_abs]
    unfold sincGaussian
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |realSinc (x0 - (k : ℝ))| * Real.exp (-a * (x0 - (k : ℝ)) ^ 2)
        ≤ 1 * Real.exp (-a * (x0 - (k : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_right (abs_realSinc_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-a * (x0 - (k : ℝ)) ^ 2) := one_mul _
  have h_quad_o :
      (fun t : ℝ => Complex.exp ((-a : ℂ) * (t : ℂ) ^ 2 + ((2 * a * x0 : ℝ) : ℂ) * (t : ℂ)))
        =o[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-2 : ℝ)) :=
    cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (by simpa using ha)
      ((2 * a * x0 : ℝ) : ℂ) (-2 : ℝ)
  have h_real_O :
      (fun t : ℝ => Real.exp (-a * t ^ 2 + (2 * a * x0) * t))
        =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-2 : ℝ)) := by
    convert h_quad_o.isBigO.norm_left with t
    have hexp : (-a : ℂ) * (t : ℂ) ^ 2 + ((2 * a * x0 : ℝ) : ℂ) * (t : ℂ) =
        ((-a * t ^ 2 + (2 * a * x0) * t : ℝ) : ℂ) := by push_cast; ring
    rw [hexp, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h_shift_O :
      (fun t : ℝ => Real.exp (-a * (x0 - t) ^ 2))
        =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-2 : ℝ)) := by
    have hsplit : (fun t : ℝ => Real.exp (-a * (x0 - t) ^ 2)) =
        fun t : ℝ => Real.exp (-a * x0 ^ 2) * Real.exp (-a * t ^ 2 + (2 * a * x0) * t) := by
      ext t
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    exact h_real_O.const_mul_left (Real.exp (-a * x0 ^ 2))
  have hsum_gauss : Summable (fun k : ℤ => Real.exp (-a * (x0 - (k : ℝ)) ^ 2)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (h_shift_O.comp_tendsto Int.tendsto_coe_cofinite)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum_gauss

/-- Continuity of `sincGaussian α` on `ℝ`. -/
theorem continuous_sincGaussian (α : ℝ) : Continuous (sincGaussian α) := by
  unfold sincGaussian
  exact continuous_realSinc.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2)))

/-- Continuity of `stdChar` on `ℝ`. -/
theorem continuous_stdChar : Continuous stdChar := by
  unfold stdChar
  fun_prop

/-- Bundled continuous map `t ↦ (sincGaussian α (z - t) : ℂ) * stdChar (ξ * t)` for Poisson summation. -/
noncomputable def sincGaussianModulatedMap (α z ξ : ℝ) : C(ℝ, ℂ) :=
  ⟨fun t : ℝ => (sincGaussian α (z - t) : ℂ) * stdChar (ξ * t),
    (Complex.continuous_ofReal.comp ((continuous_sincGaussian α).comp (continuous_const.sub continuous_id))).mul
      (continuous_stdChar.comp (continuous_const.mul continuous_id))⟩

@[simp]
theorem sincGaussianModulatedMap_apply (α z ξ t : ℝ) :
    sincGaussianModulatedMap α z ξ t = (sincGaussian α (z - t) : ℂ) * stdChar (ξ * t) :=
  rfl

/-- Rapid `O(|t|^{-2})` decay of `sincGaussianModulatedMap α z ξ` along `cocompact ℝ` for `α > 0`. -/
theorem isBigO_sincGaussian_modulated_cocompact (α z ξ : ℝ) (hα : 0 < α) :
    (fun t : ℝ => (sincGaussian α (z - t) : ℂ) * stdChar (ξ * t))
      =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-2 : ℝ)) := by
  set a : ℝ := Real.pi / α ^ 2
  have ha : 0 < a := div_pos Real.pi_pos (sq_pos_of_pos hα)
  have hle : ∀ t : ℝ,
      ‖(sincGaussian α (z - t) : ℂ) * stdChar (ξ * t)‖ ≤
        1 * ‖Real.exp (-a * (z - t) ^ 2)‖ := by
    intro t
    rw [norm_mul, norm_stdChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    unfold sincGaussian
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |realSinc (z - t)| * Real.exp (-a * (z - t) ^ 2)
        ≤ 1 * Real.exp (-a * (z - t) ^ 2) :=
          mul_le_mul_of_nonneg_right (abs_realSinc_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-a * (z - t) ^ 2) := one_mul _
  have h_bound_O :
      (fun t : ℝ => (sincGaussian α (z - t) : ℂ) * stdChar (ξ * t))
        =O[Filter.cocompact ℝ] (fun t : ℝ => Real.exp (-a * (z - t) ^ 2)) :=
    Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall hle)
  have h_quad_o :
      (fun t : ℝ => Complex.exp ((-a : ℂ) * (t : ℂ) ^ 2 + ((2 * a * z : ℝ) : ℂ) * (t : ℂ)))
        =o[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-2 : ℝ)) :=
    cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (by simpa using ha)
      ((2 * a * z : ℝ) : ℂ) (-2 : ℝ)
  have h_real_O :
      (fun t : ℝ => Real.exp (-a * t ^ 2 + (2 * a * z) * t))
        =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-2 : ℝ)) := by
    convert h_quad_o.isBigO.norm_left with t
    have hexp : (-a : ℂ) * (t : ℂ) ^ 2 + ((2 * a * z : ℝ) : ℂ) * (t : ℂ) =
        ((-a * t ^ 2 + (2 * a * z) * t : ℝ) : ℂ) := by push_cast; ring
    rw [hexp, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h_shift_O :
      (fun t : ℝ => Real.exp (-a * (z - t) ^ 2))
        =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-2 : ℝ)) := by
    have hsplit : (fun t : ℝ => Real.exp (-a * (z - t) ^ 2)) =
        fun t : ℝ => Real.exp (-a * z ^ 2) * Real.exp (-a * t ^ 2 + (2 * a * z) * t) := by
      ext t
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    exact h_real_O.const_mul_left (Real.exp (-a * z ^ 2))
  exact h_bound_O.trans h_shift_O

/-- **Unconditional Compact-Restriction Norm-Summability (`h_norm`) for `sincGaussianModulatedMap` (`[MS]` §4.2)**:
Discharges Mathlib's `h_norm` hypothesis in `Real.tsum_eq_tsum_fourier` for the shifted/modulated
Sinc-Gaussian kernel at any `α > 0` and any compact set `K : Compacts ℝ`. -/
theorem summable_norm_restrict_sincGaussian_modulated
    (α z ξ : ℝ) (hα : 0 < α) (K : TopologicalSpace.Compacts ℝ) :
    Summable fun n : ℤ => ‖((sincGaussianModulatedMap α z ξ).comp (ContinuousMap.addRight n)).restrict K‖ :=
  summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((isBigO_norm_restrict_cocompact (sincGaussianModulatedMap α z ξ) zero_lt_two
      (isBigO_sincGaussian_modulated_cocompact α z ξ hα) K).comp_tendsto Int.tendsto_coe_cofinite)

/-! ## 2. Lattice Folding, Shift-Modulation, and 2D-to-1D Phase Identities (`[MS]` §4.2) -/

/-- Periodicity of the `r`-point DFT character under integer multiples of `r`:
`e((k_2 + l * r) u_2 / r) = e(k_2 u_2 / r)`. -/
theorem stdChar_lattice_fold (r : ℕ) (hr : 0 < r) (k2 l u2 : ℤ) :
    stdChar ((((k2 + l * (r : ℤ) : ℤ) : ℝ) * (u2 : ℝ)) / (r : ℝ)) =
      stdChar (((k2 : ℝ) * (u2 : ℝ)) / (r : ℝ)) := by
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hsplit : (((k2 + l * (r : ℤ) : ℤ) : ℝ) * (u2 : ℝ)) / (r : ℝ) =
      ((k2 : ℝ) * (u2 : ℝ)) / (r : ℝ) + ((l * u2 : ℤ) : ℝ) := by
    push_cast
    field_simp [hr_ne]
  rw [hsplit, stdChar_add_int]

/-- Phase factorization in the continuous Fourier transform of `f(t) = g(z - t) e(ξ t)` (`[MS]` §4.2):
substituting `s = z - t` splits `e((ξ - m) t)` into `e(-(ξ - m) (z - t)) * e((ξ - m) z)`. -/
theorem shift_modulation_phase_factor (z ξ m t : ℝ) :
    stdChar ((ξ - m) * t) = stdChar (-(ξ - m) * (z - t)) * stdChar ((ξ - m) * z) := by
  rw [← stdChar_add]
  congr 1
  ring

/-- **Continuous Fourier Transform of the Shifted-Modulated Kernel (`[MS]` §4.2, proof of Theorem 4.2)**:
For any kernel `g : ℝ → ℂ` and parameters `z, ξ, m ∈ ℝ`, the continuous Lebesgue Fourier
transform of `t ↦ g(z - t) e(ξ t)` at frequency `m` equals `e((ξ - m) z) * (𝓕 g)(ξ - m)`.
Proved from first principles via Lebesgue translation-reflection invariance
(`MeasureTheory.integral_sub_left_eq_self`). -/
theorem fourier_modulated_shift (g : ℝ → ℂ) (z ξ m : ℝ) :
    𝓕 (fun t : ℝ => g (z - t) * stdChar (ξ * t)) m =
      stdChar ((ξ - m) * z) * 𝓕 g (ξ - m) := by
  rw [fourier_eq_integral_stdChar, fourier_eq_integral_stdChar]
  have h_integrand :
      (fun t : ℝ => stdChar (-(t * m)) * (g (z - t) * stdChar (ξ * t))) =
      (fun t : ℝ => stdChar ((ξ - m) * z) * (stdChar (-((z - t) * (ξ - m))) * g (z - t))) := by
    ext t
    have hphase : stdChar (-(t * m)) * stdChar (ξ * t) =
        stdChar ((ξ - m) * z) * stdChar (-((z - t) * (ξ - m))) := by
      rw [← stdChar_add, ← stdChar_add]
      congr 1
      ring
    calc stdChar (-(t * m)) * (g (z - t) * stdChar (ξ * t))
        = (stdChar (-(t * m)) * stdChar (ξ * t)) * g (z - t) := by ring
      _ = (stdChar ((ξ - m) * z) * stdChar (-((z - t) * (ξ - m)))) * g (z - t) := by rw [hphase]
      _ = stdChar ((ξ - m) * z) * (stdChar (-((z - t) * (ξ - m))) * g (z - t)) := by ring
  rw [h_integrand, MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_sub_left_eq_self
    (fun s : ℝ => stdChar (-(s * (ξ - m))) * g s) MeasureTheory.volume z

/-- **Continuous 1D Poisson Summation for the Shifted-Modulated Kernel (`[MS]` §4.2, proof of Theorem 4.2)**:
For any kernel `g : ℝ → ℂ` and `z, ξ ∈ ℝ` such that `f(t) = g(z - t) e(ξ t)` satisfies the
Poisson summation hypotheses (`Real.tsum_eq_tsum_fourier`), the infinite lattice sum over `ℤ`
satisfies:
`∑' k : ℤ, g(z - k) e(ξ k) = ∑' m : ℤ, (𝓕 g)(ξ - m) e((ξ - m) z)`. -/
theorem continuous_modulated_poisson_summation
    (g : ℝ → ℂ) (z ξ : ℝ)
    (f : C(ℝ, ℂ))
    (hf_eq : ∀ t : ℝ, f t = g (z - t) * stdChar (ξ * t))
    (h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖)
    (h_sum : Summable fun m : ℤ => 𝓕 (f : ℝ → ℂ) m) :
    (∑' k : ℤ, g (z - (k : ℝ)) * stdChar (ξ * (k : ℝ))) =
      ∑' m : ℤ, 𝓕 g (ξ - (m : ℝ)) * stdChar ((ξ - (m : ℝ)) * z) := by
  have hP := Real.tsum_eq_tsum_fourier h_norm h_sum 0
  have hlhs : (∑' n : ℤ, f (0 + (n : ℝ))) =
      ∑' k : ℤ, g (z - (k : ℝ)) * stdChar (ξ * (k : ℝ)) := by
    congr 1 with k
    rw [zero_add, hf_eq]
  have hrhs : (∑' m : ℤ, 𝓕 (f : ℝ → ℂ) m * fourier m ((0 : ℝ) : UnitAddCircle)) =
      ∑' m : ℤ, 𝓕 g (ξ - (m : ℝ)) * stdChar ((ξ - (m : ℝ)) * z) := by
    congr 1 with m
    have hf_fun : (f : ℝ → ℂ) = fun t : ℝ => g (z - t) * stdChar (ξ * t) := funext hf_eq
    have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := rfl
    rw [h0, fourier_eval_zero, mul_one, hf_fun, fourier_modulated_shift, mul_comm]
  rw [← hlhs, hP, hrhs]

/-- **Key 2D-to-1D Fractional-Shift Phase Congruence (`[MS]` Theorem 4.2, §4.2)**:
For `t_1, r > 0`, `j_1, j_2, u_1, u_2, m, u_1_tilde, q ∈ ℤ` with
`u_1 - m = u_1_tilde + q * t_1` (i.e. `u_1_tilde = (u_1 - m) mod t_1`), the product of the outer
column character `e(j_1 u_1 / t_1)` and the fractional-shift Poisson character
`e((j_2 + j_1 / t_1) (u_2 / r - m))` equals the 1D DFT character
`e(((j_1 + t_1 j_2) (u_2 + r u_1_tilde)) / (t_1 r))`. -/
theorem fractional_shift_phase_identity
    (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (j1 j2 u1 u2 m u1_tilde q : ℤ)
    (hu1 : u1 - m = u1_tilde + q * (t1 : ℤ)) :
    stdChar (((j1 : ℝ) * (u1 : ℝ)) / (t1 : ℝ)) *
      stdChar (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) * ((u2 : ℝ) / (r : ℝ) - (m : ℝ))) =
    stdChar ((((j1 + (t1 : ℤ) * j2 : ℤ) : ℝ) * ((u2 + (r : ℤ) * u1_tilde : ℤ) : ℝ)) /
      (((t1 * r : ℕ) : ℝ))) := by
  rw [← stdChar_add]
  have ht1_ne : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hu1_real : (u1 : ℝ) - (m : ℝ) = (u1_tilde : ℝ) + (q : ℝ) * (t1 : ℝ) := by
    exact_mod_cast hu1
  have hexp :
      ((j1 : ℝ) * (u1 : ℝ)) / (t1 : ℝ) +
        ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) * ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) =
      ((((j1 + (t1 : ℤ) * j2 : ℤ) : ℝ) * ((u2 + (r : ℤ) * u1_tilde : ℤ) : ℝ)) /
        (((t1 * r : ℕ) : ℝ))) +
        ((j1 * q - j2 * m - j2 * u1_tilde : ℤ) : ℝ) := by
    push_cast
    have h_u1 : (u1 : ℝ) = (m : ℝ) + (u1_tilde : ℝ) + (q : ℝ) * (t1 : ℝ) := by
      linarith [hu1_real]
    rw [h_u1]
    field_simp [ht1_ne, hr_ne]
    ring
  rw [hexp, stdChar_add_int]

/-! ## 3. `[MS]` Theorem 4.2: CRT-Free Fractional-Shift Poisson Identity (§4.2, eq. (18)) -/

/-- The 2D-indexed 1D DFT at frequency `u_2 + r * u_1_tilde`:
`(1 / (t_1 r)) ∑_{j_1=0}^{t_1-1} ∑_{j_2=0}^{r-1} x(j_1 + t_1 j_2) e((j_1 + t_1 j_2)(u_2 + r u_1_tilde) / (t_1 r))`. -/
noncomputable def dft1DGrid (t1 r : ℕ) (x : ℕ → ℂ) (u2 u1_tilde : ℕ) : ℂ :=
  (1 / ((t1 * r : ℕ) : ℂ)) *
    ∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r,
      x (j1 + t1 * j2) *
        stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde : ℕ) : ℝ)) /
          ((t1 * r : ℕ) : ℝ))

/-- **`[MS]` Theorem 4.2 (CRT-Free Fractional-Shift Poisson Identity, §4.2, eq. (18))**:
Let `t_1, r > 0`. Given input `x : ℕ → ℂ` and Fourier coefficients `gHat : ℤ → ℂ` (representing
`m ↦ ĝ(u_2 / r - m)` on a finite or truncated alias support `M_set : Finset ℤ`), if the inner
row-spread Fourier sum `S(j_1, j_2, u_2)` satisfies the 1D Poisson summation identity
`S(j_1, j_2, u_2) = ∑_{m ∈ M_set} gHat m * stdChar ((j_2 + j_1 / t_1) * (u_2 / r - m))`,
and `u1_tilde : ℤ → ℕ`, `q : ℤ → ℤ` satisfy `u_1 - m = u1_tilde m + q m * t_1` for all `m ∈ M_set`,
then the 2D DFT of `x̃` equals:
`∑_{m ∈ M_set} gHat m * dft1DGrid t1 r x u2 (u1_tilde m)`. -/
theorem theorem2_fractional_shift_poisson_identity
    (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M_set : Finset ℤ) (gHat : ℤ → ℂ)
    (u1 u2 : ℕ) (u1_tilde : ℤ → ℕ) (q : ℤ → ℤ)
    (hu1 : ∀ m ∈ M_set, (u1 : ℤ) - m = (u1_tilde m : ℤ) + q m * (t1 : ℤ))
    (S : ℕ → ℕ → ℂ)
    (hPoisson : ∀ j1 ∈ Finset.range t1, ∀ j2 ∈ Finset.range r,
      S j1 j2 = ∑ m ∈ M_set,
        gHat m * stdChar (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) * ((u2 : ℝ) / (r : ℝ) - (m : ℝ)))) :
    (1 / ((t1 * r : ℕ) : ℂ)) *
      (∑ j1 ∈ Finset.range t1, stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
        ∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * S j1 j2) =
    ∑ m ∈ M_set, gHat m * dft1DGrid t1 r x u2 (u1_tilde m) := by
  have h1 :
      ∑ j1 ∈ Finset.range t1, stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
        (∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * S j1 j2) =
      ∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r, ∑ m ∈ M_set,
        gHat m * (x (j1 + t1 * j2) *
          stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
            ((t1 * r : ℕ) : ℝ))) := by
    refine Finset.sum_congr rfl fun j1 hj1 => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j2 hj2 => ?_
    rw [hPoisson j1 hj1 j2 hj2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hphase := fractional_shift_phase_identity t1 r ht1 hr
      (j1 : ℤ) (j2 : ℤ) (u1 : ℤ) (u2 : ℤ) m (u1_tilde m : ℤ) (q m) (hu1 m hm)
    push_cast at hphase
    have hcast_lhs : (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) =
        ((j1 : ℝ) * (u1 : ℝ)) / (t1 : ℝ) := by push_cast; ring
    have hcast_rhs :
        (((j1 : ℝ) + (t1 : ℝ) * (j2 : ℝ)) *
          ((u2 : ℝ) + (r : ℝ) * (u1_tilde m : ℝ))) / ((t1 : ℝ) * (r : ℝ)) =
        ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
          ((t1 * r : ℕ) : ℝ)) := by push_cast; ring
    calc stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
          (x (j1 + t1 * j2) *
            (gHat m * stdChar (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) * ((u2 : ℝ) / (r : ℝ) - (m : ℝ)))))
        = gHat m * (x (j1 + t1 * j2) *
            (stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
              stdChar (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) * ((u2 : ℝ) / (r : ℝ) - (m : ℝ))))) := by
          ring
      _ = gHat m * (x (j1 + t1 * j2) *
            stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
              ((t1 * r : ℕ) : ℝ))) := by
          rw [hcast_lhs, hphase, hcast_rhs]
  rw [h1]
  unfold dft1DGrid
  have h_rhs :
      (∑ m ∈ M_set, gHat m * ((1 / ((t1 * r : ℕ) : ℂ)) *
        ∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r,
          x (j1 + t1 * j2) *
            stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
              ((t1 * r : ℕ) : ℝ)))) =
      (1 / ((t1 * r : ℕ) : ℂ)) *
        ∑ m ∈ M_set, ∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r,
          gHat m * (x (j1 + t1 * j2) *
            stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
              ((t1 * r : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← mul_assoc, mul_comm (gHat m), mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j1 _ => ?_
    rw [Finset.mul_sum]
  rw [h_rhs]
  congr 1
  trans (∑ j1 ∈ Finset.range t1, ∑ m ∈ M_set, ∑ j2 ∈ Finset.range r,
    gHat m * (x (j1 + t1 * j2) *
      stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
        ((t1 * r : ℕ) : ℝ))))
  · refine Finset.sum_congr rfl fun j1 _ => Finset.sum_comm
  · exact Finset.sum_comm

/-- **`[MS]` Theorem 4.2 from Continuous 1D Poisson Summation (`continuous_modulated_poisson_summation` → `theorem2`)**:
Combining `continuous_modulated_poisson_summation` (for the infinite spatial spread series
`∑' k : ℤ, g(j_2 + j_1 / t_1 - k) e((u_2 / r) k)`) with `fractional_shift_phase_identity`
yields the exact infinite `ℤ`-series 2D-to-1D mode expansion in terms of Mathlib's continuous
Fourier transform `𝓕 g`. -/
theorem theorem2_continuous_poisson_to_dft1DGrid
    (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (g : ℝ → ℂ) (x : ℕ → ℂ)
    (u1 u2 : ℕ) (u1_tilde : ℤ → ℕ) (q : ℤ → ℤ)
    (hu1 : ∀ m : ℤ, (u1 : ℤ) - m = (u1_tilde m : ℤ) + q m * (t1 : ℤ))
    (f : ℕ → ℕ → C(ℝ, ℂ))
    (hf_eq : ∀ j1 j2 t, f j1 j2 t =
      g (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) - t) * stdChar (((u2 : ℝ) / (r : ℝ)) * t))
    (h_norm : ∀ j1 j2 (K : TopologicalSpace.Compacts ℝ),
      Summable fun n : ℤ => ‖((f j1 j2).comp (ContinuousMap.addRight n)).restrict K‖)
    (h_sum : ∀ j1 j2, Summable fun m : ℤ => 𝓕 (f j1 j2 : ℝ → ℂ) m) :
    (1 / ((t1 * r : ℕ) : ℂ)) *
      (∑ j1 ∈ Finset.range t1, stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
        ∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) *
          (∑' k : ℤ, g (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) - (k : ℝ)) *
            stdChar (((u2 : ℝ) / (r : ℝ)) * (k : ℝ)))) =
    ∑' m : ℤ, 𝓕 g ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) * dft1DGrid t1 r x u2 (u1_tilde m) := by
  let term : ℕ → ℕ → ℤ → ℂ := fun j1 j2 m =>
    𝓕 g ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) *
      (x (j1 + t1 * j2) *
        stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
          ((t1 * r : ℕ) : ℝ)))
  have hterm_eq : ∀ j1 j2 m,
      term j1 j2 m =
        (stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) * x (j1 + t1 * j2)) *
          (𝓕 g ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) *
            stdChar (((u2 : ℝ) / (r : ℝ) - (m : ℝ)) * ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)))) := by
    intro j1 j2 m
    dsimp [term]
    have hphase := fractional_shift_phase_identity t1 r ht1 hr
      (j1 : ℤ) (j2 : ℤ) (u1 : ℤ) (u2 : ℤ) m (u1_tilde m : ℤ) (q m) (hu1 m)
    push_cast at hphase
    have hcast_lhs : (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) =
        ((j1 : ℝ) * (u1 : ℝ)) / (t1 : ℝ) := by push_cast; ring
    have hcast_rhs :
        (((j1 : ℝ) + (t1 : ℝ) * (j2 : ℝ)) *
          ((u2 : ℝ) + (r : ℝ) * (u1_tilde m : ℝ))) / ((t1 : ℝ) * (r : ℝ)) =
        ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
          ((t1 * r : ℕ) : ℝ)) := by push_cast; ring
    have hcomm : ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) * ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) =
        ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) * ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) := mul_comm _ _
    rw [hcomm, ← hcast_rhs, ← hphase, ← hcast_lhs]
    ring
  have hterm_sum : ∀ j1 j2, Summable (term j1 j2) := by
    intro j1 j2
    have hf_fun : (f j1 j2 : ℝ → ℂ) = fun t : ℝ =>
        g (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) - t) * stdChar (((u2 : ℝ) / (r : ℝ)) * t) :=
      funext (hf_eq j1 j2)
    have h1 : (fun m : ℤ => 𝓕 g ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) *
        stdChar (((u2 : ℝ) / (r : ℝ) - (m : ℝ)) * ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)))) =
        fun m : ℤ => 𝓕 (f j1 j2 : ℝ → ℂ) m := by
      ext m
      rw [hf_fun, fourier_modulated_shift, mul_comm]
    have h2 : term j1 j2 = fun m : ℤ =>
        (stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) * x (j1 + t1 * j2)) * 𝓕 (f j1 j2 : ℝ → ℂ) m := by
      ext m
      rw [hterm_eq, ← congrFun h1 m]
    rw [h2]
    exact (h_sum j1 j2).mul_left _
  have hlhs :
      (∑ j1 ∈ Finset.range t1, stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
        ∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) *
          (∑' k : ℤ, g (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) - (k : ℝ)) *
            stdChar (((u2 : ℝ) / (r : ℝ)) * (k : ℝ)))) =
      ∑' m : ℤ, ∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r, term j1 j2 m := by
    trans (∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r, ∑' m : ℤ, term j1 j2 m)
    · refine Finset.sum_congr rfl fun j1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j2 _ => ?_
      rw [continuous_modulated_poisson_summation g ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ))
        ((u2 : ℝ) / (r : ℝ)) (f j1 j2) (hf_eq j1 j2) (h_norm j1 j2) (h_sum j1 j2)]
      rw [← tsum_mul_left, ← tsum_mul_left]
      congr 1 with m
      rw [hterm_eq]
      ring
    · trans (∑ j1 ∈ Finset.range t1, ∑' m : ℤ, ∑ j2 ∈ Finset.range r, term j1 j2 m)
      · refine Finset.sum_congr rfl fun j1 _ => ?_
        exact (Summable.tsum_finsetSum fun j2 _ => hterm_sum j1 j2).symm
      · exact (Summable.tsum_finsetSum fun j1 _ =>
          summable_sum fun j2 _ => hterm_sum j1 j2).symm
  rw [hlhs, ← tsum_mul_left]
  congr 1 with m
  unfold dft1DGrid
  dsimp [term]
  have hpull :
      (∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r,
        𝓕 g ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) *
          (x (j1 + t1 * j2) *
            stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
              ((t1 * r : ℕ) : ℝ)))) =
      𝓕 g ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) *
        ∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r,
          x (j1 + t1 * j2) *
            stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1_tilde m : ℕ) : ℝ)) /
              ((t1 * r : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j1 _ => ?_
    rw [Finset.mul_sum]
  rw [hpull]
  ring

/-! ## 4. Mixed-Radix Grid Equivalence & Exact 2-Tap Spatial Spreading (`[MS]` §4.2) -/

/-- Summing `f (j_1 + t_1 * j_2)` over `(j_1, j_2) ∈ range t_1 × range r` equals summing `f j`
over `j ∈ range (t_1 * r)`. -/
theorem sum_range_grid_eq_sum_range_mul (t1 r : ℕ) (f : ℕ → ℂ) :
    (∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r, f (j1 + t1 * j2)) =
      ∑ j ∈ Finset.range (t1 * r), f j := by
  rw [Finset.sum_comm]
  induction r with
  | zero =>
    simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j1 _ => ?_
    rw [add_comm (t1 * r) j1]

/-- **Mixed-Radix Equivalence (`dft1DGrid` = `dft1D`)**:
For any `t_1, r : ℕ` and frequency index `u : ℕ`, evaluating `dft1DGrid t1 r x` at
`(u % r, u / r)` equals `dft1D (t1 * r) x u`. -/
theorem dft1DGrid_eq_dft1D (t1 r : ℕ) (x : ℕ → ℂ) (u : ℕ) :
    dft1DGrid t1 r x (u % r) (u / r) = dft1D (t1 * r) x u := by
  unfold dft1DGrid dft1D
  rw [Nat.mod_add_div u r]
  congr 1
  have h := sum_range_grid_eq_sum_range_mul t1 r
    (fun j => x j * stdChar (((j * u : ℕ) : ℝ) / ((t1 * r : ℕ) : ℝ)))
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
  push_cast
  rfl

/-- For any `k : ℕ` and `x : ℝ`, `stdChar ((k : ℝ) * x) = (stdChar x) ^ k`. -/
theorem stdChar_nat_mul (k : ℕ) (x : ℝ) :
    stdChar ((k : ℝ) * x) = (stdChar x) ^ k := by
  induction k with
  | zero =>
    simp [stdChar]
  | succ k ih =>
    have h : ((k + 1 : ℕ) : ℝ) * x = (k : ℝ) * x + x := by
      push_cast
      ring
    rw [h, stdChar_add, ih, pow_succ]

/-- **Discrete Fourier Orthogonality on `Finset.range r`**:
For `r > 0` and `v2, u2 < r`,
`∑_{k_2 < r} e(-k_2 v_2 / r) e(k_2 u_2 / r) = if v2 = u2 then r else 0`. -/
theorem stdChar_orthogonality_range (r : ℕ) (hr : 0 < r) (v2 u2 : ℕ)
    (hv2 : v2 < r) (hu2 : u2 < r) :
    (∑ k2 ∈ Finset.range r,
      stdChar (-(((k2 : ℝ) * (v2 : ℝ)) / (r : ℝ))) *
        stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))) =
      if v2 = u2 then (r : ℂ) else 0 := by
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set δ : ℝ := ((u2 : ℝ) - (v2 : ℝ)) / (r : ℝ)
  set ω : ℂ := stdChar δ
  have hterm : ∀ k2 : ℕ,
      stdChar (-(((k2 : ℝ) * (v2 : ℝ)) / (r : ℝ))) *
        stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ)) = ω ^ k2 := by
    intro k2
    rw [← stdChar_add, ← stdChar_nat_mul]
    congr 1
    dsimp [δ]
    push_cast
    ring
  simp_rw [hterm]
  by_cases hvu : v2 = u2
  · subst hvu
    have hω1 : ω = 1 := by
      dsimp [ω, δ]
      rw [sub_self, zero_div]
      simp [stdChar]
    simp [hω1]
  · rw [if_neg hvu]
    have hω_pow : ω ^ r = 1 := by
      dsimp [ω]
      rw [← stdChar_nat_mul]
      have hrδ : (r : ℝ) * δ = (((u2 : ℤ) - (v2 : ℤ) : ℤ) : ℝ) := by
        dsimp [δ]
        push_cast
        field_simp [hr_ne]
      rw [hrδ, stdChar_int]
    have hgeom : (∑ k2 ∈ Finset.range r, ω ^ k2) * (ω - 1) = 0 := by
      rw [geom_sum_mul, hω_pow, sub_self]
    have hω_ne : ω - 1 ≠ 0 := by
      intro hsub
      have hω1 : ω = 1 := sub_eq_zero.mp hsub
      dsimp [ω, stdChar] at hω1
      rw [Complex.exp_eq_one_iff] at hω1
      rcases hω1 with ⟨n, hn⟩
      have hn1 : ((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I =
          (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
        calc ((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I
          _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
          _ = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      have him : 2 * Real.pi * δ = (n : ℝ) * (2 * Real.pi) :=
        Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hn1)
      have hpi : 0 < Real.pi := Real.pi_pos
      have hδ_eq : δ = (n : ℝ) := by nlinarith
      have hdiff_real : (u2 : ℝ) - (v2 : ℝ) = (n : ℝ) * (r : ℝ) := by
        dsimp [δ] at hδ_eq
        exact (div_eq_iff hr_ne).mp hδ_eq
      have hdiff_int : (u2 : ℤ) - (v2 : ℤ) = n * (r : ℤ) := by
        exact_mod_cast hdiff_real
      have hu2_int : (u2 : ℤ) < (r : ℤ) := by exact_mod_cast hu2
      have hv2_int : (v2 : ℤ) < (r : ℤ) := by exact_mod_cast hv2
      have hn_lt : n < 1 := by nlinarith
      have hn_gt : -1 < n := by nlinarith
      have hn0 : n = 0 := by omega
      rw [hn0, zero_mul] at hdiff_int
      have huv_eq : u2 = v2 := by omega
      exact hvu huv_eq.symm
    exact (mul_eq_zero.mp hgeom).resolve_right hω_ne

/-- Idealized 2-term passband Poisson row kernel `S(j_1, j_2, v_2)` at passband modes `m ∈ {0, 1}`:
`c_0(v_2) e((j_2 + j_1 / t_1)(v_2 / r)) + c_1(v_2) e((j_2 + j_1 / t_1)(v_2 / r - 1))`. -/
noncomputable def twoTapRowKernel (t1 r : ℕ) (c0 c1 : ℕ → ℂ) (j1 j2 v2 : ℕ) : ℂ :=
  c0 v2 * stdChar (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) * ((v2 : ℝ) / (r : ℝ) - ((0 : ℤ) : ℝ))) +
  c1 v2 * stdChar (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) * ((v2 : ℝ) / (r : ℝ) - ((1 : ℤ) : ℝ)))

/-- Idealized frequency-domain 2-term-passband spread array `U(j_1, k_2)` on the `t_1 × r` grid (`[MS]` §4.2):
synthesized from the row sums `∑_{j_2 < r} x(j_1 + t_1 j_2) S(j_1, j_2, v_2)` via length-`r`
inverse 1D DFT so that its 2D DFT realizes the exact 2-term passband alias combination. -/
noncomputable def spreadArray2Tap (t1 r : ℕ) (c0 c1 : ℕ → ℂ) (x : ℕ → ℂ) (j1 k2 : ℕ) : ℂ :=
  (1 / (r : ℂ)) * ∑ v2 ∈ Finset.range r,
    (∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * twoTapRowKernel t1 r c0 c1 j1 j2 v2) *
      stdChar (-(((k2 : ℝ) * (v2 : ℝ)) / (r : ℝ)))

/-- Row-wise 1D Fourier sum of `spreadArray2Tap` recovers the exact 2-term row sum for `u2 < r`. -/
theorem spreadArray2Tap_row_sum_eq (t1 r : ℕ) (hr : 0 < r) (c0 c1 : ℕ → ℂ) (x : ℕ → ℂ)
    (j1 u2 : ℕ) (hu2 : u2 < r) :
    (∑ k2 ∈ Finset.range r,
      spreadArray2Tap t1 r c0 c1 x j1 k2 * stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))) =
    ∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * twoTapRowKernel t1 r c0 c1 j1 j2 u2 := by
  unfold spreadArray2Tap
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hswap :
      (∑ k2 ∈ Finset.range r,
        ((1 / (r : ℂ)) * ∑ v2 ∈ Finset.range r,
          (∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * twoTapRowKernel t1 r c0 c1 j1 j2 v2) *
            stdChar (-(((k2 : ℝ) * (v2 : ℝ)) / (r : ℝ)))) *
          stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))) =
      (1 / (r : ℂ)) * ∑ v2 ∈ Finset.range r,
        (∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * twoTapRowKernel t1 r c0 c1 j1 j2 v2) *
          ∑ k2 ∈ Finset.range r,
            stdChar (-(((k2 : ℝ) * (v2 : ℝ)) / (r : ℝ))) *
              stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ)) := by
    rw [Finset.mul_sum]
    trans (∑ k2 ∈ Finset.range r, ∑ v2 ∈ Finset.range r,
      (1 / (r : ℂ)) * ((∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * twoTapRowKernel t1 r c0 c1 j1 j2 v2) *
        (stdChar (-(((k2 : ℝ) * (v2 : ℝ)) / (r : ℝ))) * stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ)))))
    · refine Finset.sum_congr rfl fun k2 _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun v2 _ => by ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v2 _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hswap]
  have horth :
      (∑ v2 ∈ Finset.range r,
        (∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * twoTapRowKernel t1 r c0 c1 j1 j2 v2) *
          ∑ k2 ∈ Finset.range r,
            stdChar (-(((k2 : ℝ) * (v2 : ℝ)) / (r : ℝ))) *
              stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))) =
      ∑ v2 ∈ Finset.range r,
        if v2 = u2 then
          (∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * twoTapRowKernel t1 r c0 c1 j1 j2 v2) * (r : ℂ)
        else 0 := by
    refine Finset.sum_congr rfl fun v2 hv2 => ?_
    rw [stdChar_orthogonality_range r hr v2 u2 (Finset.mem_range.mp hv2) hu2]
    split_ifs <;> ring
  rw [horth, Finset.sum_ite_eq' (Finset.range r) u2, if_pos (Finset.mem_range.mpr hu2)]
  field_simp [hr_ne]

/-- **2D DFT of `spreadArray2Tap` Equals 2-Term Passband Combination**:
For any `t_1, r > 0`, `u_1 < t_1`, and `u_2 < r`, the 2D DFT of `spreadArray2Tap` satisfies:
- At `u_1 = 0`: `dft2D = c_0(u_2) * dft1DGrid u_2 0 + c_1(u_2) * dft1DGrid u_2 (t_1 - 1)`
- At `0 < u_1 < t_1`: `dft2D = c_0(u_2) * dft1DGrid u_2 u_1 + c_1(u_2) * dft1DGrid u_2 (u_1 - 1)`. -/
theorem dft2D_spreadArray2Tap_eq (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (c0 c1 : ℕ → ℂ) (x : ℕ → ℂ) (u1 u2 : ℕ) (hu2 : u2 < r) :
    dft2D t1 r (spreadArray2Tap t1 r c0 c1 x) u1 u2 =
      c0 u2 * dft1DGrid t1 r x u2 u1 +
      c1 u2 * dft1DGrid t1 r x u2 (if u1 = 0 then t1 - 1 else u1 - 1) := by
  unfold dft2D
  have hrow :
      (∑ j1 ∈ Finset.range t1, ∑ k2 ∈ Finset.range r,
        spreadArray2Tap t1 r c0 c1 x j1 k2 *
          stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
          stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))) =
      ∑ j1 ∈ Finset.range t1, stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
        ∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) * twoTapRowKernel t1 r c0 c1 j1 j2 u2 := by
    refine Finset.sum_congr rfl fun j1 _ => ?_
    rw [← spreadArray2Tap_row_sum_eq t1 r hr c0 c1 x j1 u2 hu2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k2 _ => by ring
  rw [hrow]
  let M_set : Finset ℤ := {0, 1}
  let gHat : ℤ → ℂ := fun m => if m = 0 then c0 u2 else c1 u2
  let u1_tilde : ℤ → ℕ := fun m =>
    if m = 0 then u1 else (if u1 = 0 then t1 - 1 else u1 - 1)
  let q : ℤ → ℤ := fun m =>
    if m = 0 then 0 else (if u1 = 0 then -1 else 0)
  have hu1_mod : ∀ m ∈ M_set, (u1 : ℤ) - m = (u1_tilde m : ℤ) + q m * (t1 : ℤ) := by
    intro m hm
    simp only [M_set, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · simp [u1_tilde, q]
    · dsimp [u1_tilde, q]
      split_ifs with h0
      · subst h0
        omega
      · omega
  have hP := theorem2_fractional_shift_poisson_identity t1 r ht1 hr x M_set gHat u1 u2
    u1_tilde q hu1_mod (fun j1 j2 => twoTapRowKernel t1 r c0 c1 j1 j2 u2) (by
      intro j1 _ j2 _
      dsimp [M_set, gHat, twoTapRowKernel]
      rw [Finset.sum_pair (by decide : (0 : ℤ) ≠ 1)]
      simp)
  rw [hP]
  dsimp [M_set, gHat, u1_tilde]
  rw [Finset.sum_pair (by decide : (0 : ℤ) ≠ 1)]
  simp

/-- For even `t_1 > 0` (`t1 % 2 = 0`), `(-1 : ℂ) ^ u1 = stdChar (-((u1 : ℝ) * (t1 / 2 : ℕ) / (t1 : ℝ)))`. -/
theorem neg_one_pow_eq_stdChar_div_two (t1 : ℕ) (ht1 : 0 < t1) (heven : t1 % 2 = 0) (u1 : ℕ) :
    (-1 : ℂ) ^ u1 = stdChar (-(((u1 : ℝ) * ((t1 / 2 : ℕ) : ℝ)) / (t1 : ℝ))) := by
  have ht1_ne : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  have hdiv : (2 : ℕ) * (t1 / 2) = t1 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)
  have hdiv_real : ((t1 / 2 : ℕ) : ℝ) / (t1 : ℝ) = 1 / 2 := by
    have h2 : (2 : ℝ) * ((t1 / 2 : ℕ) : ℝ) = (t1 : ℝ) := by exact_mod_cast hdiv
    exact (div_eq_iff ht1_ne).mpr (by linarith)
  have harg : -(((u1 : ℝ) * ((t1 / 2 : ℕ) : ℝ)) / (t1 : ℝ)) = (u1 : ℝ) * (-(1 / 2 : ℝ)) := by
    calc -(((u1 : ℝ) * ((t1 / 2 : ℕ) : ℝ)) / (t1 : ℝ))
      _ = -(u1 : ℝ) * (((t1 / 2 : ℕ) : ℝ) / (t1 : ℝ)) := by ring
      _ = -(u1 : ℝ) * (1 / 2 : ℝ) := by rw [hdiv_real]
      _ = (u1 : ℝ) * (-(1 / 2 : ℝ)) := by ring
  rw [harg, stdChar_nat_mul]
  congr 1
  unfold stdChar
  have hexp : ((2 * Real.pi * -(1 / 2 : ℝ) : ℝ) : ℂ) * Complex.I = -(Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hexp, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

/-- **Character-Orthogonality Identity for the Nyquist Alternating Sum (`[MS]` §5.1, Theorem 5.1(3), eq. (25))**:
For even `t_1 > 0` (`t1 % 2 = 0`) and `r > 0`, summing `(-1)^{u_1} * dft1DGrid t1 r x u2 u1`
over `u1 ∈ range t1` annihilates all rows `j_1 ≠ t_1 / 2` by discrete Fourier orthogonality
(`stdChar_orthogonality_range`) and isolates the midpoint row `j_1 = t_1 / 2`:
`∑_{u_1 < t_1} (-1)^{u_1} X(u_2, u_1) = (1 / r) ∑_{j_2 < r} x(t_1 / 2 + t_1 j_2) e((t_1 / 2 + t_1 j_2) u_2 / (t_1 r))`. -/
theorem dft1DGrid_alternating_sum_eq_midpoint (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (heven : t1 % 2 = 0) (x : ℕ → ℂ) (u2 : ℕ) :
    (∑ u1 ∈ Finset.range t1, (-1 : ℂ) ^ u1 * dft1DGrid t1 r x u2 u1) =
      (1 / (r : ℂ)) * ∑ j2 ∈ Finset.range r,
        x (t1 / 2 + t1 * j2) *
          stdChar ((((t1 / 2 + t1 * j2 : ℕ) : ℝ) * (u2 : ℝ)) / ((t1 * r : ℕ) : ℝ)) := by
  unfold dft1DGrid
  have ht1_ne : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have ht1_c : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  have hr_c : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hphase : ∀ j1 j2 u1 : ℕ,
      (-1 : ℂ) ^ u1 *
        stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1 : ℕ) : ℝ)) / ((t1 * r : ℕ) : ℝ)) =
      stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * (u2 : ℝ)) / ((t1 * r : ℕ) : ℝ)) *
        (stdChar (-(((u1 : ℝ) * ((t1 / 2 : ℕ) : ℝ)) / (t1 : ℝ))) *
          stdChar (((u1 * j1 : ℕ) : ℝ) / (t1 : ℝ))) := by
    intro j1 j2 u1
    rw [neg_one_pow_eq_stdChar_div_two t1 ht1 heven u1]
    have hsplit :
        (((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1 : ℕ) : ℝ)) / ((t1 * r : ℕ) : ℝ) =
        ((((j1 + t1 * j2 : ℕ) : ℝ) * (u2 : ℝ)) / ((t1 * r : ℕ) : ℝ) +
          (((u1 * j1 : ℕ) : ℝ) / (t1 : ℝ))) +
          (((j2 * u1 : ℕ) : ℤ) : ℝ) := by
      push_cast
      field_simp [ht1_ne, hr_ne]
      ring
    rw [hsplit, stdChar_add_int, stdChar_add]
    ring
  have hswap :
      (∑ u1 ∈ Finset.range t1,
        (-1 : ℂ) ^ u1 *
          ((1 / ((t1 * r : ℕ) : ℂ)) *
            ∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r,
              x (j1 + t1 * j2) *
                stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * ((u2 + r * u1 : ℕ) : ℝ)) /
                  ((t1 * r : ℕ) : ℝ)))) =
      (1 / ((t1 * r : ℕ) : ℂ)) *
        ∑ j1 ∈ Finset.range t1,
          (∑ j2 ∈ Finset.range r,
            x (j1 + t1 * j2) *
              stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * (u2 : ℝ)) / ((t1 * r : ℕ) : ℝ))) *
          ∑ u1 ∈ Finset.range t1,
            stdChar (-(((u1 : ℝ) * ((t1 / 2 : ℕ) : ℝ)) / (t1 : ℝ))) *
              stdChar (((u1 * j1 : ℕ) : ℝ) / (t1 : ℝ)) := by
    rw [Finset.mul_sum]
    trans (∑ u1 ∈ Finset.range t1, ∑ j1 ∈ Finset.range t1,
      (1 / ((t1 * r : ℕ) : ℂ)) *
        ((∑ j2 ∈ Finset.range r,
          x (j1 + t1 * j2) *
            stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * (u2 : ℝ)) / ((t1 * r : ℕ) : ℝ))) *
          (stdChar (-(((u1 : ℝ) * ((t1 / 2 : ℕ) : ℝ)) / (t1 : ℝ))) *
            stdChar (((u1 * j1 : ℕ) : ℝ) / (t1 : ℝ)))))
    · refine Finset.sum_congr rfl fun u1 _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j1 _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j2 _ => ?_
      have hp := hphase j1 j2 u1
      linear_combination (1 / ((t1 * r : ℕ) : ℂ)) * x (j1 + t1 * j2) * hp
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j1 _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hswap]
  have hmid_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
  have horth :
      (∑ j1 ∈ Finset.range t1,
        (∑ j2 ∈ Finset.range r,
          x (j1 + t1 * j2) *
            stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * (u2 : ℝ)) / ((t1 * r : ℕ) : ℝ))) *
        ∑ u1 ∈ Finset.range t1,
          stdChar (-(((u1 : ℝ) * ((t1 / 2 : ℕ) : ℝ)) / (t1 : ℝ))) *
            stdChar (((u1 * j1 : ℕ) : ℝ) / (t1 : ℝ))) =
      ∑ j1 ∈ Finset.range t1,
        if t1 / 2 = j1 then
          (∑ j2 ∈ Finset.range r,
            x (j1 + t1 * j2) *
              stdChar ((((j1 + t1 * j2 : ℕ) : ℝ) * (u2 : ℝ)) / ((t1 * r : ℕ) : ℝ))) * (t1 : ℂ)
        else 0 := by
    refine Finset.sum_congr rfl fun j1 hj1 => ?_
    rw [stdChar_orthogonality_range t1 ht1 (t1 / 2) j1 hmid_lt (Finset.mem_range.mp hj1)]
    split_ifs <;> ring
  rw [horth, Finset.sum_ite_eq (Finset.range t1) (t1 / 2), if_pos (Finset.mem_range.mpr hmid_lt)]
  have hcast : ((t1 * r : ℕ) : ℂ) = (t1 : ℂ) * (r : ℂ) := Nat.cast_mul t1 r
  rw [hcast]
  field_simp [ht1_c, hr_c]
  refine Finset.sum_congr rfl fun j2 _ => ?_
  rw [mul_comm (u2 : ℝ)]

end IntMul
