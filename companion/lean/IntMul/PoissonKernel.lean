import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Windowed Sinc-Gaussian Kernel & Fractional-Shift Poisson Identity (`IntMul.PoissonKernel`)

This module formalizes the windowed sinc-Gaussian kernel, the fractional-shift Poisson identity,
the passband/stopband/wrap-around deconvolution estimates, and the filter $\ell_1$-norm and
spatial truncation bounds of the paper (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`),
Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`), Section 6.1 (`sec:filter-norms`),
Lemma 6.1 (`lem:filter-norms`)):
1. The windowed sinc-Gaussian kernel $g_\alpha(t) = \operatorname{sinc}(t) e^{-\pi t^2 / \alpha^2}$ and its
   Fourier transform $\hat{g}_\alpha(\xi)$ in terms of the error function $\operatorname{erf}$
   (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`)).
2. Fractional-shift periodic, untruncated, and truncated filters $h^{(j_1)}$
   (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`), Theorem 6.3 (`thm:spread`)).
3. Theorem 4.2 (`thm:poisson`): Exact 2D-to-1D DFT factorization, character mode-isolation identity, and the
   fractional-shift Poisson identity with spatial truncation and stopband residual bounds (Section 4.2 (`sec:poisson`)).
4. Lemma 6.1 (`lem:filter-norms`): Logarithmic filter $\ell_1$-norm bound $\|h^{(j_1)}\|_1 \le \frac{2}{\pi}\ln\alpha + 1.62$
   and spatial truncation tail bound $\sum_{|d| > m_1} |g_\alpha(d \pm \delta)| < 0.4 \cdot 2^{-p}$
   (Section 6.1 (`sec:filter-norms`), Appendix C.2 (`app:filter-norms-proof`), Table 3 (`tab:lean-map`)).
-/

open scoped BigOperators
open MeasureTheory

namespace IntMul

/-! ## 1. Windowed Sinc-Gaussian Kernel $g_\alpha(t)$ and its Fourier Transform $\hat{g}_\alpha(\xi)$ -/

/-- Normalized cardinal sine $\operatorname{sinc}(t) = \frac{\sin(\pi t)}{\pi t}$ for $t \ne 0$, and $1$ at $t = 0$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def sinc (t : ℝ) : ℝ :=
  if t = 0 then 1 else Real.sin (Real.pi * t) / (Real.pi * t)

@[simp]
theorem sinc_zero : sinc 0 = 1 := by
  simp [sinc]

theorem sinc_of_ne_zero {t : ℝ} (ht : t ≠ 0) :
    sinc t = Real.sin (Real.pi * t) / (Real.pi * t) := by
  simp [sinc, ht]

theorem sinc_eq_real_sinc (t : ℝ) : sinc t = Real.sinc (Real.pi * t) := by
  by_cases ht : t = 0
  · simp [ht]
  · have hpi : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
    rw [sinc_of_ne_zero ht, Real.sinc_of_ne_zero hpi]

/-- Frequency-boxcar integral representation of `Real.sinc (Real.pi * t)`:
$\operatorname{sinc}(\pi t) = \int_{-1/2}^{1/2} \cos(2\pi \nu t) \, d\nu$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
theorem sinc_pi_eq_intervalIntegral_cos (t : ℝ) :
    Real.sinc (Real.pi * t) =
      ∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (2 * Real.pi * nu * t) := by
  by_cases ht : t = 0
  · subst ht
    simp
    norm_num
  · have hpi_t : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
    have hc : 2 * Real.pi * t ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) ht
    have hfun : (fun nu : ℝ => Real.cos (2 * Real.pi * nu * t)) =
        (fun nu : ℝ => Real.cos (nu * (2 * Real.pi * t))) := by
      ext nu; ring_nf
    rw [hfun, intervalIntegral.integral_comp_mul_right Real.cos hc, integral_cos, smul_eq_mul]
    have h1 : (1 / 2 : ℝ) * (2 * Real.pi * t) = Real.pi * t := by ring
    have h2 : (-1 / 2 : ℝ) * (2 * Real.pi * t) = -(Real.pi * t) := by ring
    rw [h1, h2, Real.sin_neg, Real.sinc_of_ne_zero hpi_t]
    field_simp [hpi_t]
    ring

/-- Frequency-boxcar integral representation of `sinc t`:
$\operatorname{sinc}(t) = \int_{-1/2}^{1/2} \cos(2\pi \nu t) \, d\nu$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
theorem sinc_eq_intervalIntegral_cos (t : ℝ) :
    sinc t = ∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (2 * Real.pi * nu * t) := by
  rw [sinc_eq_real_sinc, sinc_pi_eq_intervalIntegral_cos]

@[simp]
theorem sinc_even (t : ℝ) : sinc (-t) = sinc t := by
  rw [sinc_eq_real_sinc, sinc_eq_real_sinc, mul_neg, Real.sinc_neg]

theorem abs_sinc_le_one (t : ℝ) : |sinc t| ≤ 1 := by
  rw [sinc_eq_real_sinc]
  exact Real.abs_sinc_le_one (Real.pi * t)

theorem abs_sinc_le_inv_pi_mul_abs {t : ℝ} (ht : t ≠ 0) :
    |sinc t| ≤ 1 / (Real.pi * |t|) := by
  rw [sinc_of_ne_zero ht, abs_div, abs_mul, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one (Real.pi * t))
    (mul_nonneg Real.pi_pos.le (abs_nonneg t))

/-- Windowed Sinc-Gaussian (Cardinal Box-Gaussian) Kernel
$g_\alpha(t) = \operatorname{sinc}(t) e^{-\pi t^2 / \alpha^2}$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), equation (15) (`eq:sinc-gauss`)). -/
noncomputable def sincGaussian (alpha t : ℝ) : ℝ :=
  sinc t * Real.exp (-Real.pi * t ^ 2 / alpha ^ 2)

@[simp]
theorem sincGaussian_zero (alpha : ℝ) : sincGaussian alpha 0 = 1 := by
  simp [sincGaussian]

@[simp]
theorem sincGaussian_even (alpha t : ℝ) : sincGaussian alpha (-t) = sincGaussian alpha t := by
  simp [sincGaussian, sinc_even]

theorem abs_sincGaussian_le_exp (alpha t : ℝ) :
    |sincGaussian alpha t| ≤ Real.exp (-Real.pi * t ^ 2 / alpha ^ 2) := by
  rw [sincGaussian, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (abs_sinc_le_one t)

theorem abs_sincGaussian_le_one (alpha t : ℝ) : |sincGaussian alpha t| ≤ 1 := by
  refine (abs_sincGaussian_le_exp alpha t).trans ?_
  rw [Real.exp_le_one_iff]
  have h1 : -Real.pi * t ^ 2 ≤ 0 := by
    nlinarith [Real.pi_pos, sq_nonneg t]
  exact div_nonpos_of_nonpos_of_nonneg h1 (sq_nonneg alpha)

theorem abs_sincGaussian_le_abs_sinc (alpha t : ℝ) :
    |sincGaussian alpha t| ≤ |sinc t| := by
  rw [sincGaussian, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-Real.pi * t ^ 2 / alpha ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos, sq_nonneg t]) (sq_nonneg alpha)
  exact mul_le_of_le_one_right (abs_nonneg _) hexp

theorem abs_sincGaussian_le_inv_pi_mul_exp {alpha t : ℝ} (ht : t ≠ 0) :
    |sincGaussian alpha t| ≤
      (1 / (Real.pi * |t|)) * Real.exp (-Real.pi * t ^ 2 / alpha ^ 2) := by
  rw [sincGaussian, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (abs_sinc_le_inv_pi_mul_abs ht) (Real.exp_pos _).le

/-- Gaussian exponent linear lower bound: when $\alpha > 0$ and $|t| \ge \alpha^2$,
$\pi t^2 / \alpha^2 \ge \pi |t| > |t|$. -/
theorem gaussian_exponent_ge_pi_mul_abs {alpha t : ℝ} (halpha : 0 < alpha)
    (ht : alpha ^ 2 ≤ |t|) :
    Real.pi * |t| ≤ Real.pi * t ^ 2 / alpha ^ 2 := by
  have halpha2 : 0 < alpha ^ 2 := sq_pos_of_pos halpha
  rw [le_div_iff₀ halpha2]
  have hsq : |t| * alpha ^ 2 ≤ t ^ 2 := by
    calc |t| * alpha ^ 2 ≤ |t| * |t| := mul_le_mul_of_nonneg_left ht (abs_nonneg t)
      _ = t ^ 2 := by rw [← sq, sq_abs]
  nlinarith [Real.pi_pos]

theorem gaussian_exponent_gt_abs {alpha t : ℝ} (halpha : 0 < alpha)
    (ht : alpha ^ 2 ≤ |t|) :
    |t| < Real.pi * t ^ 2 / alpha ^ 2 := by
  have hpos : 0 < |t| := lt_of_lt_of_le (sq_pos_of_pos halpha) ht
  have hpi : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hlt : |t| < Real.pi * |t| := by nlinarith
  exact hlt.trans_le (gaussian_exponent_ge_pi_mul_abs halpha ht)

theorem abs_sincGaussian_le_exp_neg_pi_abs {alpha t : ℝ} (halpha : 0 < alpha)
    (ht : alpha ^ 2 ≤ |t|) :
    |sincGaussian alpha t| ≤ Real.exp (-Real.pi * |t|) := by
  refine (abs_sincGaussian_le_exp alpha t).trans ?_
  rw [Real.exp_le_exp]
  have h := gaussian_exponent_ge_pi_mul_abs halpha ht
  linarith [show -Real.pi * t ^ 2 / alpha ^ 2 = -(Real.pi * t ^ 2 / alpha ^ 2) by ring]

/-- Error function $\operatorname{erf}(z) = \frac{2}{\sqrt{\pi}} \int_0^z e^{-t^2} dt$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`)). -/
noncomputable def erf (z : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))

/-- Complementary error function $\operatorname{erfc}(z) = 1 - \operatorname{erf}(z)$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`)). -/
noncomputable def erfc (z : ℝ) : ℝ :=
  1 - erf z

@[simp]
theorem erf_zero : erf 0 = 0 := by
  simp [erf]

@[simp]
theorem erf_odd (z : ℝ) : erf (-z) = -erf z := by
  unfold erf
  have hcomp : (∫ t in (0 : ℝ)..(-z), Real.exp (-(t ^ 2))) =
      ∫ t in (0 : ℝ)..(-z), Real.exp (-((-t) ^ 2)) := by
    congr 1; ext t; rw [neg_sq]
  rw [hcomp, intervalIntegral.integral_comp_neg (f := fun t => Real.exp (-(t ^ 2))),
    neg_zero, neg_neg, intervalIntegral.integral_symm]
  ring

/-- Continuous Fourier transform $\hat{g}_\alpha(\xi)$ of the Sinc-Gaussian kernel (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), equation (16) (`eq:ghat`)):
$\hat{g}_\alpha(\xi) = \frac{1}{2}\left[\operatorname{erf}(\sqrt{\pi}\alpha(1/2 - \xi)) + \operatorname{erf}(\sqrt{\pi}\alpha(1/2 + \xi))\right]$. -/
noncomputable def gHat (alpha xi : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (erf (Real.sqrt Real.pi * alpha * (1 / 2 - xi)) +
    erf (Real.sqrt Real.pi * alpha * (1 / 2 + xi)))

@[simp]
theorem gHat_even (alpha xi : ℝ) : gHat alpha (-xi) = gHat alpha xi := by
  unfold gHat
  have h1 : 1 / 2 - -xi = 1 / 2 + xi := by ring
  have h2 : 1 / 2 + -xi = 1 / 2 - xi := by ring
  rw [h1, h2, add_comm]

/-- Equivalence with the difference-of-erf formula in Theorem 4.2 (`thm:poisson`), equation (16) (`eq:ghat`):
$\hat{g}_\alpha(\xi) = \frac{1}{2}\left[\operatorname{erf}(\sqrt{\pi}\alpha(\xi + 1/2)) - \operatorname{erf}(\sqrt{\pi}\alpha(\xi - 1/2))\right]$. -/
theorem gHat_eq_sub (alpha xi : ℝ) :
    gHat alpha xi =
      (1 / 2 : ℝ) * (erf (Real.sqrt Real.pi * alpha * (xi + 1 / 2)) -
        erf (Real.sqrt Real.pi * alpha * (xi - 1 / 2))) := by
  unfold gHat
  have h1 : Real.sqrt Real.pi * alpha * (1 / 2 - xi) =
      -(Real.sqrt Real.pi * alpha * (xi - 1 / 2)) := by ring
  have h2 : Real.sqrt Real.pi * alpha * (1 / 2 + xi) =
      Real.sqrt Real.pi * alpha * (xi + 1 / 2) := by ring
  rw [h1, h2, erf_odd]
  ring

/-- Analytical boxcar-Gaussian convolution identity for $\hat{g}_\alpha(\xi)$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), equation (16) (`eq:ghat`)):
for $\alpha \ne 0$, the boxcar-convolved Gaussian frequency integral
$\int_{-1/2}^{1/2} \alpha e^{-\pi \alpha^2 (\xi - \nu)^2} \, d\nu$ equals $\hat{g}_\alpha(\xi)$. -/
theorem integral_boxcar_gaussian_eq_gHat (alpha xi : ℝ) (halpha : alpha ≠ 0) :
    (∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      alpha * Real.exp (-Real.pi * alpha ^ 2 * (xi - nu) ^ 2)) =
    gHat alpha xi := by
  have hsqrt_pi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  set c : ℝ := Real.sqrt Real.pi * alpha
  set d : ℝ := Real.sqrt Real.pi * alpha * xi
  have hc : c ≠ 0 := mul_ne_zero hsqrt_pi halpha
  have hsq : c ^ 2 = Real.pi * alpha ^ 2 := by
    dsimp [c]
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have hfun : (fun nu : ℝ => alpha * Real.exp (-Real.pi * alpha ^ 2 * (xi - nu) ^ 2)) =
      (fun nu : ℝ => alpha * Real.exp (-((d - c * nu) ^ 2))) := by
    ext nu
    congr 2
    have h1 : d - c * nu = c * (xi - nu) := by dsimp [c, d]; ring
    rw [h1, mul_pow, hsq]
    ring
  rw [hfun, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_mul (f := fun t => Real.exp (-(t ^ 2))) hc d,
    smul_eq_mul]
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    fun_prop
  have hsplit := intervalIntegral.integral_interval_sub_left
    (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := d - c * (-1 / 2 : ℝ)) (c := d - c * (1 / 2 : ℝ))
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [← hsplit, gHat_eq_sub]
  unfold erf
  have hb : d - c * (-1 / 2 : ℝ) = Real.sqrt Real.pi * alpha * (xi + 1 / 2) := by
    dsimp [c, d]; ring
  have hc' : d - c * (1 / 2 : ℝ) = Real.sqrt Real.pi * alpha * (xi - 1 / 2) := by
    dsimp [c, d]; ring
  rw [hb, hc']
  dsimp [c]
  field_simp [hsqrt_pi, halpha]

/-- Closed-form telescoping identity for the passband sum $c_0(y) + c_1(y) = \hat{g}_\alpha(y) + \hat{g}_\alpha(1 - y)$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1(1) (`thm:deconv`)). -/
theorem gHat_add_gHat_one_sub (alpha y : ℝ) :
    gHat alpha y + gHat alpha (1 - y) =
      (1 / 2 : ℝ) * (erf (Real.sqrt Real.pi * alpha * (y + 1 / 2)) +
        erf (Real.sqrt Real.pi * alpha * (3 / 2 - y))) := by
  unfold gHat
  have h1 : Real.sqrt Real.pi * alpha * (1 / 2 - (1 - y)) =
      -(Real.sqrt Real.pi * alpha * (1 / 2 - y)) := by ring
  have h2 : Real.sqrt Real.pi * alpha * (1 / 2 + (1 - y)) =
      Real.sqrt Real.pi * alpha * (3 / 2 - y) := by ring
  have h3 : Real.sqrt Real.pi * alpha * (1 / 2 + y) =
      Real.sqrt Real.pi * alpha * (y + 1 / 2) := by ring
  rw [h1, h2, h3, erf_odd]
  ring

/-- Closed-form stopband alias identity $1 - \hat{g}_\alpha(y) - \hat{g}_\alpha(1 - y) = \frac{1}{2}\operatorname{erfc}(\sqrt{\pi}\alpha(y + 1/2)) + \frac{1}{2}\operatorname{erfc}(\sqrt{\pi}\alpha(3/2 - y))$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1(1) (`thm:deconv`), equation (21) (`eq:stopband`)). -/
theorem one_sub_gHat_sub_gHat_one_sub (alpha y : ℝ) :
    1 - gHat alpha y - gHat alpha (1 - y) =
      (1 / 2 : ℝ) * erfc (Real.sqrt Real.pi * alpha * (y + 1 / 2)) +
        (1 / 2 : ℝ) * erfc (Real.sqrt Real.pi * alpha * (3 / 2 - y)) := by
  have h := gHat_add_gHat_one_sub alpha y
  unfold erfc
  linarith

/-- Symmetry of $\hat{g}_\alpha$ around $1$: $\hat{g}_\alpha(y - 1) = \hat{g}_\alpha(1 - y)$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`), equation (19) (`eq:c0-c1`)). -/
@[simp]
theorem gHat_symm_one (alpha y : ℝ) : gHat alpha (y - 1) = gHat alpha (1 - y) := by
  have h : y - 1 = -(1 - y) := by ring
  rw [h, gHat_even]

/-- Strict positivity of $\hat{g}_\alpha(\xi)$ for $\alpha > 0$ and all $\xi \in \mathbb{R}$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`)). -/
theorem gHat_pos (alpha : ℝ) (halpha : 0 < alpha) (xi : ℝ) : 0 < gHat alpha xi := by
  rw [← integral_boxcar_gaussian_eq_gHat alpha xi halpha.ne']
  have hcont : Continuous (fun nu : ℝ => alpha * Real.exp (-Real.pi * alpha ^ 2 * (xi - nu) ^ 2)) := by
    fun_prop
  exact intervalIntegral.intervalIntegral_pos_of_pos (hcont.intervalIntegrable _ _)
    (fun _ => mul_pos halpha (Real.exp_pos _)) (by norm_num)

/-- Non-negativity of $\hat{g}_\alpha(\xi)$ for $\alpha \ge 0$ and all $\xi \in \mathbb{R}$. -/
theorem gHat_nonneg (alpha : ℝ) (halpha : 0 ≤ alpha) (xi : ℝ) : 0 ≤ gHat alpha xi := by
  rcases eq_or_lt_of_le halpha with rfl | hpos
  · simp [gHat]
  · exact (gHat_pos alpha hpos xi).le

/-- Shifted complex Gaussian Fourier integral: for $\alpha > 0$,
$\int_{\mathbb{R}} e^{-\pi t^2 / \alpha^2 + 2\pi i (\nu - \xi) t} \, dt = \alpha e^{-\pi \alpha^2 (\xi - \nu)^2}$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
theorem fourier_gaussian_shift_integral (alpha : ℝ) (halpha : 0 < alpha) (xi nu : ℝ) :
    (∫ t : ℝ,
      Complex.exp (-Real.pi * (t : ℂ) ^ 2 / (alpha : ℂ) ^ 2 +
        2 * Real.pi * Complex.I * ((nu - xi : ℝ) : ℂ) * (t : ℂ))) =
    (alpha : ℂ) * Complex.exp (-Real.pi * (alpha : ℂ) ^ 2 * ((xi - nu : ℝ) : ℂ) ^ 2) := by
  set b : ℂ := ((Real.pi / alpha ^ 2 : ℝ) : ℂ)
  set w : ℂ := 2 * (Real.pi : ℂ) * ((nu - xi : ℝ) : ℂ)
  have hb_pos : 0 < Real.pi / alpha ^ 2 := div_pos Real.pi_pos (sq_pos_of_pos halpha)
  have hb_re : 0 < b.re := by
    dsimp [b]
    exact hb_pos
  have hfun :
      (fun t : ℝ =>
        Complex.exp (-Real.pi * (t : ℂ) ^ 2 / (alpha : ℂ) ^ 2 +
          2 * Real.pi * Complex.I * ((nu - xi : ℝ) : ℂ) * (t : ℂ))) =
      (fun t : ℝ =>
        Complex.exp (Complex.I * w * (t : ℂ)) * Complex.exp (-b * (t : ℂ) ^ 2)) := by
    ext t
    rw [← Complex.exp_add]
    congr 1
    dsimp [b, w]
    push_cast
    ring
  rw [hfun, fourierIntegral_gaussian hb_re w]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have halpha_ne : (alpha : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr halpha.ne'
  congr 1
  · have hdiv : (Real.pi : ℂ) / b = ((alpha ^ 2 : ℝ) : ℂ) := by
      dsimp [b]
      push_cast
      field_simp [hpi_ne, halpha_ne]
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hdiv, hhalf, ← Complex.ofReal_cpow (sq_nonneg alpha)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq halpha.le]
  · congr 1
    dsimp [b, w]
    push_cast
    field_simp [hpi_ne, halpha_ne]
    ring

/-- Iterated frequency-boxcar integral of the shifted Gaussian Fourier integral equals $\hat{g}_\alpha(\xi)$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
theorem integral_boxcar_fourier_gaussian_shift_eq_gHat (alpha : ℝ) (halpha : 0 < alpha) (xi : ℝ) :
    (∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      ∫ t : ℝ,
        Complex.exp (-Real.pi * (t : ℂ) ^ 2 / (alpha : ℂ) ^ 2 +
          2 * Real.pi * Complex.I * ((nu - xi : ℝ) : ℂ) * (t : ℂ))) =
    (gHat alpha xi : ℂ) := by
  simp_rw [fourier_gaussian_shift_integral alpha halpha xi]
  have hreal :
      (fun nu : ℝ => (alpha : ℂ) * Complex.exp (-Real.pi * (alpha : ℂ) ^ 2 * ((xi - nu : ℝ) : ℂ) ^ 2)) =
      (fun nu : ℝ => ((alpha * Real.exp (-Real.pi * alpha ^ 2 * (xi - nu) ^ 2) : ℝ) : ℂ)) := by
    ext nu
    push_cast
    rfl
  rw [hreal, intervalIntegral.integral_ofReal, integral_boxcar_gaussian_eq_gHat alpha xi halpha.ne']

/-- Shifted Gaussian interval integral representation of `gHat alpha (xi - (m : ℝ))` for $\alpha > 0$. -/
theorem gHat_sub_int_eq_intervalIntegral (alpha : ℝ) (halpha : 0 < alpha) (xi : ℝ) (m : ℤ) :
    gHat alpha (xi - (m : ℝ)) =
      ∫ u in (-xi - 1 / 2) + (m : ℝ)..(-xi - 1 / 2) + (m : ℝ) + 1,
        alpha * Real.exp (-Real.pi * alpha ^ 2 * u ^ 2) := by
  rw [← integral_boxcar_gaussian_eq_gHat alpha (xi - (m : ℝ)) halpha.ne']
  let f : ℝ → ℝ := fun u => alpha * Real.exp (-Real.pi * alpha ^ 2 * u ^ 2)
  have hcomp :
      (fun nu : ℝ => alpha * Real.exp (-Real.pi * alpha ^ 2 * (xi - (m : ℝ) - nu) ^ 2)) =
      (fun nu : ℝ => f (nu + (-xi + (m : ℝ)))) := by
    ext nu
    dsimp [f]
    congr 2
    ring
  rw [hcomp, intervalIntegral.integral_comp_add_right f (-xi + (m : ℝ))]
  have h1 : (-1 / 2 : ℝ) + (-xi + (m : ℝ)) = (-xi - 1 / 2) + (m : ℝ) := by ring
  have h2 : (1 / 2 : ℝ) + (-xi + (m : ℝ)) = (-xi - 1 / 2) + (m : ℝ) + 1 := by ring
  rw [h1, h2]

/-- Partition-of-unity `HasSum` identity for $\hat{g}_\alpha$: for $\alpha > 0$ and $\xi \in \mathbb{R}$,
$\sum_{m \in \mathbb{Z}} \hat{g}_\alpha(\xi - m) = 1$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1(1) (`thm:deconv`)). -/
theorem hasSum_gHat_sub_int_eq_one (alpha : ℝ) (halpha : 0 < alpha) (xi : ℝ) :
    HasSum (fun m : ℤ => gHat alpha (xi - (m : ℝ))) 1 := by
  simp_rw [gHat_sub_int_eq_intervalIntegral alpha halpha xi]
  have hb : 0 < Real.pi * alpha ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos halpha)
  have hint : Integrable (fun u : ℝ => alpha * Real.exp (-Real.pi * alpha ^ 2 * u ^ 2)) := by
    have h1 : (fun u : ℝ => alpha * Real.exp (-Real.pi * alpha ^ 2 * u ^ 2)) =
        (fun u : ℝ => alpha * Real.exp (-(Real.pi * alpha ^ 2) * u ^ 2)) := by
      ext u; ring_nf
    rw [h1]
    exact (integrable_exp_neg_mul_sq hb).const_mul alpha
  have hsum := hint.hasSum_intervalIntegral (-xi - 1 / 2)
  have hint_val : (∫ u : ℝ, alpha * Real.exp (-Real.pi * alpha ^ 2 * u ^ 2)) = 1 := by
    have h1 : (fun u : ℝ => alpha * Real.exp (-Real.pi * alpha ^ 2 * u ^ 2)) =
        (fun u : ℝ => alpha * Real.exp (-(Real.pi * alpha ^ 2) * u ^ 2)) := by
      ext u; ring_nf
    rw [h1, MeasureTheory.integral_const_mul, integral_gaussian (Real.pi * alpha ^ 2)]
    have hdiv : Real.pi / (Real.pi * alpha ^ 2) = (alpha ^ 2)⁻¹ := by
      rw [div_mul_eq_div_div, div_self Real.pi_ne_zero, one_div]
    rw [hdiv, Real.sqrt_inv, Real.sqrt_sq halpha.le, mul_inv_cancel₀ halpha.ne']
  rwa [hint_val] at hsum

/-- Summability of `m ↦ gHat alpha (xi - (m : ℝ))` for $\alpha > 0$. -/
theorem summable_gHat_sub_int (alpha : ℝ) (halpha : 0 < alpha) (xi : ℝ) :
    Summable (fun m : ℤ => gHat alpha (xi - (m : ℝ))) :=
  (hasSum_gHat_sub_int_eq_one alpha halpha xi).summable

/-- **Partition of Unity for $\hat{g}_\alpha$ (`tsum_gHat_sub_int_eq_one`, Section 5.1 (`sec:deconv-thm`), Theorem 5.1(1) (`thm:deconv`))**:
For $\alpha > 0$ and $\xi \in \mathbb{R}$, $\sum'_{m : \mathbb{Z}} \hat{g}_\alpha(\xi - m) = 1$. -/
theorem tsum_gHat_sub_int_eq_one (alpha : ℝ) (halpha : 0 < alpha) (xi : ℝ) :
    (∑' m : ℤ, gHat alpha (xi - (m : ℝ))) = 1 :=
  (hasSum_gHat_sub_int_eq_one alpha halpha xi).tsum_eq

/-- Integral representation of `erfc z` on `(z, +∞)` for $z \ge 0$:
$\operatorname{erfc}(z) = \frac{2}{\sqrt{\pi}} \int_{z}^{\infty} e^{-t^2} \, dt$. -/
theorem erfc_eq_integral_Ioi {z : ℝ} (hz : 0 ≤ z) :
    erfc z = (2 / Real.sqrt Real.pi) * ∫ t in Set.Ioi z, Real.exp (-(t ^ 2)) := by
  have hint : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq zero_lt_one
  have hIoi0 : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 := by
    simpa only [neg_one_mul, div_one] using integral_gaussian_Ioi 1
  have hunion :
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2))) =
        (∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))) + ∫ t in Set.Ioi z, Real.exp (-(t ^ 2)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hz,
      MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        hint.integrableOn hint.integrableOn,
      intervalIntegral.integral_of_le hz]
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hone : (2 / Real.sqrt Real.pi) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2)) = 1 := by
    rw [hIoi0]
    field_simp [hsqrt_ne]
  unfold erfc erf
  rw [← hone, hunion, mul_add]
  ring

/-- Non-negativity of `erfc z` for $z \ge 0$. -/
theorem erfc_nonneg_of_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ erfc z := by
  rw [erfc_eq_integral_Ioi hz]
  refine mul_nonneg (by positivity) ?_
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun _ _ => (Real.exp_pos _).le)

/-- `erf z` is non-negative for $z \ge 0$. -/
theorem erf_nonneg_of_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ erf z := by
  unfold erf
  refine mul_nonneg (by positivity) ?_
  exact intervalIntegral.integral_nonneg hz (fun _ _ => (Real.exp_pos _).le)

/-- `erf z ≤ 1` for all $z \in \mathbb{R}$. -/
theorem erf_le_one (z : ℝ) : erf z ≤ 1 := by
  rcases le_or_gt 0 z with hz | hz
  · have h := erfc_nonneg_of_nonneg hz
    unfold erfc at h
    linarith
  · have h := erf_nonneg_of_nonneg (by linarith : 0 ≤ -z)
    rw [erf_odd] at h
    linarith

/-- Non-negativity of `erfc z` for all $z \in \mathbb{R}$. -/
theorem erfc_nonneg (z : ℝ) : 0 ≤ erfc z := by
  unfold erfc
  linarith [erf_le_one z]

/-- Exact tail integral $\int_z^\infty 2 t e^{-t^2} \, dt = e^{-z^2}$. -/
theorem integral_Ioi_two_mul_exp_neg_sq (z : ℝ) :
    (∫ t in Set.Ioi z, (2 * t * Real.exp (-(t ^ 2)))) = Real.exp (-(z ^ 2)) := by
  have hderiv : ∀ x ∈ Set.Ici z,
      HasDerivAt (fun t : ℝ => -Real.exp (-(t ^ 2))) (2 * x * Real.exp (-(x ^ 2))) x := by
    intro x _
    exact (((hasDerivAt_pow 2 x).neg).exp).neg.congr_deriv (by dsimp; ring)
  have hf_int : IntegrableOn (fun t : ℝ => 2 * t * Real.exp (-(t ^ 2))) (Set.Ioi z) := by
    have hfun : (fun t : ℝ => 2 * t * Real.exp (-(t ^ 2))) =
        (fun t : ℝ => 2 * (t * Real.exp (-1 * t ^ 2))) := by
      ext t; ring_nf
    rw [hfun]
    exact ((integrable_mul_exp_neg_mul_sq zero_lt_one).const_mul 2).integrableOn
  have hlim : Filter.Tendsto (fun t : ℝ => -Real.exp (-(t ^ 2))) Filter.atTop (nhds 0) := by
    rw [← neg_zero]
    refine Filter.Tendsto.neg ?_
    have h1 : (fun t : ℝ => Real.exp (-(t ^ 2))) = (fun t : ℝ => Real.exp (-1 * t ^ 2)) := by
      ext t; ring_nf
    rw [h1]
    exact Real.tendsto_exp_atBot.comp
      ((Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop_of_neg (by norm_num))
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hf_int hlim]
  ring

/-- Gaussian tail integral bound: for $z > 0$,
$\int_z^\infty e^{-t^2} \, dt \le \frac{1}{2z} e^{-z^2}$. -/
theorem integral_Ioi_exp_neg_sq_le {z : ℝ} (hz : 0 < z) :
    (∫ t in Set.Ioi z, Real.exp (-(t ^ 2))) ≤ (1 / (2 * z)) * Real.exp (-(z ^ 2)) := by
  rw [← integral_Ioi_two_mul_exp_neg_sq z, ← MeasureTheory.integral_const_mul]
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Set.Ioi z) := by
    simpa only [neg_one_mul] using (integrable_exp_neg_mul_sq zero_lt_one).integrableOn
  have hint2 : IntegrableOn (fun t : ℝ => (1 / (2 * z)) * (2 * t * Real.exp (-(t ^ 2)))) (Set.Ioi z) := by
    have hfun : (fun t : ℝ => (1 / (2 * z)) * (2 * t * Real.exp (-(t ^ 2)))) =
        (fun t : ℝ => (1 / z) * (t * Real.exp (-1 * t ^ 2))) := by
      ext t; field_simp [hz.ne']
    rw [hfun]
    exact ((integrable_mul_exp_neg_mul_sq zero_lt_one).const_mul (1 / z)).integrableOn
  refine MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Ioi (fun t ht => ?_)
  have hzt : z ≤ t := (Set.mem_Ioi.mp ht).le
  have h1 : 1 ≤ (1 / (2 * z)) * (2 * t) :=
    calc (1 : ℝ) = (1 / (2 * z)) * (2 * z) := (one_div_mul_cancel (by positivity)).symm
      _ ≤ (1 / (2 * z)) * (2 * t) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc Real.exp (-(t ^ 2))
      = 1 * Real.exp (-(t ^ 2)) := (one_mul _).symm
    _ ≤ ((1 / (2 * z)) * (2 * t)) * Real.exp (-(t ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (1 / (2 * z)) * (2 * t * Real.exp (-(t ^ 2))) := by ring

/-- Complementary error function Gaussian tail bound (Section 5.1 (`sec:deconv-thm`), Theorem 5.1(1) (`thm:deconv`)):
for $z > 0$, $\operatorname{erfc}(z) \le \frac{e^{-z^2}}{\sqrt{\pi} z}$. -/
theorem erfc_le_inv_sqrt_pi_mul_exp {z : ℝ} (hz : 0 < z) :
    erfc z ≤ (1 / (Real.sqrt Real.pi * z)) * Real.exp (-(z ^ 2)) := by
  rw [erfc_eq_integral_Ioi hz.le]
  calc (2 / Real.sqrt Real.pi) * (∫ t in Set.Ioi z, Real.exp (-(t ^ 2)))
      ≤ (2 / Real.sqrt Real.pi) * ((1 / (2 * z)) * Real.exp (-(z ^ 2))) :=
        mul_le_mul_of_nonneg_left (integral_Ioi_exp_neg_sq_le hz) (by positivity)
    _ = (1 / (Real.sqrt Real.pi * z)) * Real.exp (-(z ^ 2)) := by
        have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
        field_simp [hpi, hz.ne']

/-- On $[0, 1/2]$, $\hat{g}_\alpha(y)$ is bounded below by its Nyquist value $\hat{g}_\alpha(1/2)$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1(1) (`thm:deconv`), equation (20) (`eq:passband`)). -/
theorem gHat_half_le_of_le_half {alpha y : ℝ} (halpha : 0 ≤ alpha) (hy0 : 0 ≤ y) (hyhalf : y ≤ 1 / 2) :
    gHat alpha (1 / 2) ≤ gHat alpha y := by
  set c : ℝ := Real.sqrt Real.pi * alpha
  have hc : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) halpha
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by fun_prop
  have hsub := intervalIntegral.integral_interval_sub_left
    (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := c) (c := c * (1 / 2 + y))
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hshift :
      (∫ t in (c * (1 / 2 + y))..c, Real.exp (-(t ^ 2))) =
        ∫ u in (0 : ℝ)..(c * (1 / 2 - y)), Real.exp (-((u + c * (1 / 2 + y)) ^ 2)) := by
    have hcomp := intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := c * (1 / 2 - y))
      (fun t : ℝ => Real.exp (-(t ^ 2))) (c * (1 / 2 + y))
    have h1 : (0 : ℝ) + c * (1 / 2 + y) = c * (1 / 2 + y) := by ring
    have h2 : c * (1 / 2 - y) + c * (1 / 2 + y) = c := by ring
    rw [h1, h2] at hcomp
    exact hcomp.symm
  have hmono :
      (∫ u in (0 : ℝ)..(c * (1 / 2 - y)), Real.exp (-((u + c * (1 / 2 + y)) ^ 2))) ≤
        ∫ u in (0 : ℝ)..(c * (1 / 2 - y)), Real.exp (-(u ^ 2)) := by
    have hlen : 0 ≤ c * (1 / 2 - y) := mul_nonneg hc (by linarith)
    have hcont2 : Continuous (fun u : ℝ => Real.exp (-((u + c * (1 / 2 + y)) ^ 2))) := by fun_prop
    refine intervalIntegral.integral_mono_on hlen
      (hcont2.intervalIntegrable _ _) (hcont.intervalIntegrable _ _) (fun u hu => ?_)
    have hu0 : 0 ≤ u := hu.1
    have hshift_nonneg : 0 ≤ c * (1 / 2 + y) := mul_nonneg hc (by linarith)
    rw [Real.exp_le_exp]
    nlinarith
  have herf : erf c - erf (c * (1 / 2 + y)) ≤ erf (c * (1 / 2 - y)) := by
    unfold erf
    rw [← mul_sub, hsub, hshift]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  unfold gHat
  have h0 : c * (1 / 2 - (1 / 2 : ℝ)) = 0 := by ring
  have h1 : c * (1 / 2 + (1 / 2 : ℝ)) = c := by ring
  change (1 / 2 : ℝ) * (erf (c * (1 / 2 - 1 / 2)) + erf (c * (1 / 2 + 1 / 2))) ≤
    (1 / 2 : ℝ) * (erf (c * (1 / 2 - y)) + erf (c * (1 / 2 + y)))
  rw [h0, h1, erf_zero, zero_add]
  linarith

/-- Upper bound $\hat{g}_\alpha(\xi) \le 1$ for all $\alpha, \xi \in \mathbb{R}$. -/
theorem gHat_le_one (alpha xi : ℝ) : gHat alpha xi ≤ 1 := by
  unfold gHat
  have h1 := erf_le_one (Real.sqrt Real.pi * alpha * (1 / 2 - xi))
  have h2 := erf_le_one (Real.sqrt Real.pi * alpha * (1 / 2 + xi))
  linarith

/-! ## 2. Fractional-Shift Periodic, Untruncated, and Truncated Filters (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`)) -/

/-- Row fractional shift $\delta(j_1) = j_1 / t_1 \in [0, 1)$ for $j_1 \in \operatorname{Fin} t_1$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def fractionalShift {t1 : ℕ} (j1 : Fin t1) : ℝ :=
  (j1.val : ℝ) / (t1 : ℝ)

theorem fractionalShift_nonneg {t1 : ℕ} (j1 : Fin t1) : 0 ≤ fractionalShift j1 := by
  unfold fractionalShift
  positivity

theorem fractionalShift_lt_one {t1 : ℕ} (j1 : Fin t1) : fractionalShift j1 < 1 := by
  unfold fractionalShift
  have ht1 : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr j1.pos
  rw [div_lt_one ht1]
  exact Nat.cast_lt.mpr j1.isLt

theorem fractionalShift_le_one {t1 : ℕ} (j1 : Fin t1) : fractionalShift j1 ≤ 1 :=
  (fractionalShift_lt_one j1).le

/-- Untruncated infinite fractional-shift filter tap $h^{\infty,(j_1)}_d = g_\alpha(d - j_1/t_1)$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)).

**Sign-Convention Note (Section 4.2 (`sec:poisson`), equation (17) (`eq:u-ideal`), and Section 6.1 (`sec:filter-norms`))**:
In backward cyclic convolution $\sum_d x((k_2 - d) \bmod r) f_{j_1}(d)$ (`spreadArray`, `rawCyclicConv`),
evaluating the tap at $(d : \mathbb{R}) - j_1 / t_1$ is identical to the forward-shift correlation
$\sum_\delta x((k_2 + \delta) \bmod r) g_\alpha(\delta + j_1 / t_1)$ (`forwardShiftConv`): under the index
reflection $d = -\delta$, $(k_2 - d) \bmod r = (k_2 + \delta) \bmod r$, and by evenness of `sincGaussian`
(`sincGaussian_even`), $g_\alpha(d - j_1/t_1) = g_\alpha(-\delta - j_1/t_1) = g_\alpha(\delta + j_1/t_1)$. -/
noncomputable def untruncatedFilterTap (alpha : ℝ) (t1 : ℕ) (j1 : Fin t1) (d : ℤ) : ℝ :=
  sincGaussian alpha ((d : ℝ) - fractionalShift j1)

/-- Truncated fractional-shift filter tap supported on $|d| \le W$ (Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`), Theorem 6.3 (`thm:spread`)).

**Sign-Convention Note (Section 4.2 (`sec:poisson`) and Section 6.1 (`sec:filter-norms`))**:
In backward cyclic convolution $\sum_{|d| \le W} x((k_2 - d) \bmod r) f_{j_1}(d)$, the argument
$(d : \mathbb{R}) - j_1 / t_1$ corresponds via $d = -\delta$ and `sincGaussian_even` to the forward
correlation kernel $g_\alpha(\delta + j_1 / t_1)$ in $\sum_{|\delta| \le W} x((k_2 + \delta) \bmod r) g_\alpha(\delta + j_1 / t_1)$. -/
noncomputable def filterTap (alpha : ℝ) (W t1 : ℕ) (j1 : Fin t1) (d : ℤ) : ℝ :=
  if |d| ≤ (W : ℤ) then sincGaussian alpha ((d : ℝ) - fractionalShift j1) else 0

/-- Exact equivalence between `untruncatedFilterTap` at $d = -\delta$ and $g_\alpha(\delta + j_1/t_1)$. -/
theorem untruncatedFilterTap_neg_eq_sincGaussian_add (alpha : ℝ) (t1 : ℕ) (j1 : Fin t1) (delta : ℤ) :
    untruncatedFilterTap alpha t1 j1 (-delta) =
      sincGaussian alpha ((delta : ℝ) + fractionalShift j1) := by
  unfold untruncatedFilterTap
  have h : ((-delta : ℤ) : ℝ) - fractionalShift j1 = -((delta : ℝ) + fractionalShift j1) := by
    push_cast; ring
  rw [h, sincGaussian_even]

theorem filterTap_of_abs_le {alpha : ℝ} {W t1 : ℕ} {j1 : Fin t1} {d : ℤ} (hd : |d| ≤ (W : ℤ)) :
    filterTap alpha W t1 j1 d = sincGaussian alpha ((d : ℝ) - fractionalShift j1) := by
  simp [filterTap, hd]

theorem filterTap_of_gt {alpha : ℝ} {W t1 : ℕ} {j1 : Fin t1} {d : ℤ} (hd : (W : ℤ) < |d|) :
    filterTap alpha W t1 j1 d = 0 := by
  simp [filterTap, not_le.mpr hd]

/-- Every filter tap satisfies $|h^{(j_1)}_d| \le 1$ (`abs_sincGaussian_le_one`). -/
theorem abs_filterTap_le_one (alpha : ℝ) (W t1 : ℕ) (j1 : Fin t1) (d : ℤ) :
    |filterTap alpha W t1 j1 d| ≤ 1 := by
  unfold filterTap
  split_ifs
  · exact abs_sincGaussian_le_one alpha _
  · simp

/-- **Unclamped Filter Mantissa Width Bound (`fitsSignedWord_quantizeRealMantissa_filterTap`, Section 6.1 (`sec:filter-norms`), Section 6.2 (`sec:kronecker`))**:
Because `|filterTap alpha W t1 j1 d| ≤ 1`, its $q$-bit rounded mantissa has magnitude at most
$2^q < 2^{q + 1}$ and therefore satisfies `FitsSignedWord (q + 1)` with zero clamping distortion
(preserving the central tap $g_\alpha(0) = 1 \mapsto 2^q$ exactly). -/
theorem fitsSignedWord_quantizeRealMantissa_filterTap (q : ℕ) (alpha : ℝ)
    (_halpha : 0 ≤ alpha) (W t1 : ℕ) (j1 : Fin t1) (d : ℤ) :
    FitsSignedWord (q + 1) (quantizeRealMantissa q (filterTap alpha W t1 j1 d)) := by
  unfold FitsSignedWord
  set x := filterTap alpha W t1 j1 d
  have hx : |x| ≤ 1 := abs_filterTap_le_one alpha W t1 j1 d
  have h2q : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hmul : |x * (2 : ℝ) ^ q| ≤ (2 : ℝ) ^ q := by
    rw [abs_mul, abs_of_pos h2q]
    exact mul_le_of_le_one_left h2q.le hx
  have herr := abs_quantizeRealMantissa_sub_le q x
  have htri : |(quantizeRealMantissa q x : ℝ)| ≤
      |(quantizeRealMantissa q x : ℝ) - x * (2 : ℝ) ^ q| + |x * (2 : ℝ) ^ q| := by
    simpa using abs_add_le ((quantizeRealMantissa q x : ℝ) - x * (2 : ℝ) ^ q) (x * (2 : ℝ) ^ q)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
  have hlt : |(quantizeRealMantissa q x : ℝ)| < (2 : ℝ) ^ (q + 1) := by
    rw [pow_succ]
    linarith
  exact_mod_cast hlt

/-- Periodic wrapped filter on $\operatorname{Fin} r$ obtained by folding the truncated filter modulo $r$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Section 6.1 (`sec:filter-norms`), Theorem 6.3 (`thm:spread`)). -/
noncomputable def periodicFilterTap (alpha : ℝ) (W t1 r : ℕ) (j1 : Fin t1) (m : Fin r) : ℝ :=
  ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
    if ((d + (r : ℤ) * ((W : ℤ) + 1)) % (r : ℤ)).toNat = m.val then
      sincGaussian alpha ((d : ℝ) - fractionalShift j1)
    else 0

/-! ## 3. Theorem 4.2 (`thm:poisson`): Exact 1D Poisson Fractional-Shift Identity & 2D-to-1D DFT Factorization (Section 4.2 (`sec:poisson`)) -/

/-- Canonical modular reduction of an integer `z : ℤ` into `Fin r` for `0 < r`. -/
def intModFin (r : ℕ) (hr : 0 < r) (z : ℤ) : Fin r :=
  ⟨(z % (r : ℤ)).toNat, by
    have hpos : (0 : ℤ) < (r : ℤ) := Nat.cast_pos.mpr hr
    have h0 : 0 ≤ z % (r : ℤ) := Int.emod_nonneg z hpos.ne'
    have hlt : z % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos z hpos
    omega⟩

@[simp]
theorem intModFin_coe (r : ℕ) (hr : 0 < r) (z : ℤ) :
    ((intModFin r hr z).val : ℤ) = z % (r : ℤ) := by
  have hpos : (0 : ℤ) < (r : ℤ) := Nat.cast_pos.mpr hr
  have h0 : 0 ≤ z % (r : ℤ) := Int.emod_nonneg z hpos.ne'
  exact Int.toNat_of_nonneg h0

@[simp]
theorem intModFin_nat_coe (r : ℕ) (hr : 0 < r) (m : Fin r) :
    intModFin r hr (m.val : ℤ) = m := by
  apply Fin.ext
  apply Nat.cast_injective (R := ℤ)
  rw [intModFin_coe]
  exact Int.emod_eq_of_lt (Nat.cast_nonneg _) (Nat.cast_lt.mpr m.isLt)

/-- Cyclic shift equivalence `k2 ↦ (k2 - d) mod r` on `Fin r`. -/
def cyclicShiftEquiv (r : ℕ) (hr : 0 < r) (d : ℤ) : Fin r ≃ Fin r where
  toFun k2 := intModFin r hr ((k2.val : ℤ) - d)
  invFun m := intModFin r hr ((m.val : ℤ) + d)
  left_inv k2 := by
    apply Fin.ext
    apply Nat.cast_injective (R := ℤ)
    dsimp only
    rw [intModFin_coe, intModFin_coe, Int.add_emod, Int.emod_emod, ← Int.add_emod, sub_add_cancel]
    exact Int.emod_eq_of_lt (Nat.cast_nonneg _) (Nat.cast_lt.mpr k2.isLt)
  right_inv m := by
    apply Fin.ext
    apply Nat.cast_injective (R := ℤ)
    dsimp only
    rw [intModFin_coe, intModFin_coe, Int.sub_emod, Int.emod_emod, ← Int.sub_emod, add_sub_cancel_right]
    exact Int.emod_eq_of_lt (Nat.cast_nonneg _) (Nat.cast_lt.mpr m.isLt)

/-- Stride-$t_1$ index $j_1 + m t_1 \in \operatorname{Fin}(t_1 r)$ for $j_1 \in \operatorname{Fin} t_1, m \in \operatorname{Fin} r$. -/
def strideFin {t1 r : ℕ} (j1 : Fin t1) (m : Fin r) : Fin (t1 * r) :=
  ⟨j1.val + m.val * t1, by
    have h1 : j1.val + 1 ≤ t1 := j1.isLt
    have h2 : m.val + 1 ≤ r := m.isLt
    have h3 : (m.val + 1) * t1 ≤ r * t1 := Nat.mul_le_mul_right t1 h2
    linarith⟩

/-- Frequency index $u_2 + r u_1 \in \operatorname{Fin}(t_1 r)$ for $u_1 \in \operatorname{Fin} t_1, u_2 \in \operatorname{Fin} r$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
def freqFin {t1 r : ℕ} (u1 : Fin t1) (u2 : Fin r) : Fin (t1 * r) :=
  ⟨u2.val + r * u1.val, by
    have h1 : u1.val + 1 ≤ t1 := u1.isLt
    have h2 : u2.val + 1 ≤ r := u2.isLt
    have h3 : r * (u1.val + 1) ≤ r * t1 := Nat.mul_le_mul_left r h1
    linarith⟩

/-- Equivalence `(j1, m) ↦ j1 + m * t1` between `Fin t1 × Fin r` and `Fin (t1 * r)`. -/
def strideFinEquiv (t1 r : ℕ) : Fin t1 × Fin r ≃ Fin (t1 * r) where
  toFun p := strideFin p.1 p.2
  invFun k :=
    have ht1 : 0 < t1 := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero k.val (by simpa using k.isLt))
    (⟨k.val % t1, Nat.mod_lt _ ht1⟩,
     ⟨k.val / t1, Nat.div_lt_of_lt_mul k.isLt⟩)
  left_inv p := by
    rcases p with ⟨j1, m⟩
    have ht1 : 0 < t1 := j1.pos
    ext
    · dsimp [strideFin]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j1.isLt]
    · dsimp [strideFin]
      rw [Nat.add_mul_div_right _ _ ht1, Nat.div_eq_of_lt j1.isLt, zero_add]
  right_inv k := by
    ext
    dsimp [strideFin]
    have h := Nat.mod_add_div k.val t1
    linarith [mul_comm t1 (k.val / t1)]

@[simp]
private theorem expTwoPiI_zero : expTwoPiI 0 = 1 := by
  simp [expTwoPiI]

@[simp]
private theorem expNegTwoPiI_zero : expNegTwoPiI 0 = 1 := by
  simp [expNegTwoPiI]

private theorem expTwoPiI_add (x y : ℝ) : expTwoPiI (x + y) = expTwoPiI x * expTwoPiI y := by
  unfold expTwoPiI
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem expNegTwoPiI_add (x y : ℝ) : expNegTwoPiI (x + y) = expNegTwoPiI x * expNegTwoPiI y := by
  unfold expNegTwoPiI
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem expTwoPiI_int (k : ℤ) : expTwoPiI (k : ℝ) = 1 := by
  unfold expTwoPiI
  have h : (2 : ℂ) * (Real.pi : ℂ) * ((k : ℝ) : ℂ) * Complex.I =
      (k : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private theorem expNegTwoPiI_int (k : ℤ) : expNegTwoPiI (k : ℝ) = 1 := by
  unfold expNegTwoPiI
  have h : (-2 : ℂ) * (Real.pi : ℂ) * ((k : ℝ) : ℂ) * Complex.I =
      ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private theorem expTwoPiI_add_int (x : ℝ) (k : ℤ) : expTwoPiI (x + (k : ℝ)) = expTwoPiI x := by
  rw [expTwoPiI_add, expTwoPiI_int, mul_one]

private theorem expNegTwoPiI_add_int (x : ℝ) (k : ℤ) : expNegTwoPiI (x + (k : ℝ)) = expNegTwoPiI x := by
  rw [expNegTwoPiI_add, expNegTwoPiI_int, mul_one]

private theorem expTwoPiI_nat_mul (x : ℝ) (n : ℕ) : expTwoPiI ((n : ℝ) * x) = (expTwoPiI x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, one_mul, expTwoPiI_add, ih, pow_succ]

private theorem expNegTwoPiI_nat_mul (x : ℝ) (n : ℕ) : expNegTwoPiI ((n : ℝ) * x) = (expNegTwoPiI x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, one_mul, expNegTwoPiI_add, ih, pow_succ]

private theorem norm_expTwoPiI (x : ℝ) : ‖expTwoPiI x‖ = 1 := by
  unfold expTwoPiI
  have h : (2 : ℂ) * (Real.pi : ℂ) * (x : ℂ) * Complex.I =
      ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem norm_expNegTwoPiI (x : ℝ) : ‖expNegTwoPiI x‖ = 1 := by
  unfold expNegTwoPiI
  have h : (-2 : ℂ) * (Real.pi : ℂ) * (x : ℂ) * Complex.I =
      ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem expTwoPiI_intModFin_mul_div (r : ℕ) (hr : 0 < r) (z u : ℤ) :
    expTwoPiI ((((intModFin r hr z).val : ℝ) * (u : ℝ)) / (r : ℝ)) =
      expTwoPiI (((z : ℝ) * (u : ℝ)) / (r : ℝ)) := by
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hcast : ((intModFin r hr z).val : ℝ) = ((z % (r : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast intModFin_coe r hr z
  have hdiv : (z % (r : ℤ) : ℤ) = z - (r : ℤ) * (z / (r : ℤ)) :=
    (Int.emod_def z (r : ℤ))
  have hsplit : (((intModFin r hr z).val : ℝ) * (u : ℝ)) / (r : ℝ) =
      ((z : ℝ) * (u : ℝ)) / (r : ℝ) + ((-(z / (r : ℤ)) * u : ℤ) : ℝ) := by
    rw [hcast, hdiv]
    push_cast
    field_simp [hrR]
    ring
  rw [hsplit, expTwoPiI_add_int]

/-- Character orthogonality / mode-isolation sum identity on $\operatorname{Fin} t_1$ with $e^{-2\pi i}$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
theorem mode_isolation_sum_expNegTwoPiI {t1 : ℕ} (ht1 : 0 < t1) (k : ℤ) :
    (((t1 : ℝ)⁻¹ : ℂ) *
      ∑ j1 : Fin t1, expNegTwoPiI (((j1.val : ℝ) * (k : ℝ)) / (t1 : ℝ))) =
      if (t1 : ℤ) ∣ k then 1 else 0 := by
  have ht1R : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  have ht1C : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  set ω := expNegTwoPiI ((k : ℝ) / (t1 : ℝ))
  have hterm : ∀ j1 : Fin t1,
      expNegTwoPiI (((j1.val : ℝ) * (k : ℝ)) / (t1 : ℝ)) = ω ^ j1.val := by
    intro j1
    rw [mul_div_assoc, expNegTwoPiI_nat_mul]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun j => ω ^ j)]
  split_ifs with hdvd
  · rcases hdvd with ⟨q, rfl⟩
    have hω : ω = 1 := by
      dsimp [ω]
      have hq : (((t1 : ℤ) * q : ℤ) : ℝ) / (t1 : ℝ) = (q : ℝ) := by
        push_cast
        exact mul_div_cancel_left₀ (q : ℝ) ht1R
      rw [hq, expNegTwoPiI_int]
    simp [hω]
    exact inv_mul_cancel₀ ht1C
  · have hω_ne : ω ≠ 1 := by
      intro h1
      dsimp [ω, expNegTwoPiI] at h1
      rw [Complex.exp_eq_one_iff] at h1
      rcases h1 with ⟨n, hn⟩
      have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
      have hmul : (((-((k : ℝ) / (t1 : ℝ)) : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) =
          (((n : ℤ) : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [Complex.ofReal_neg, Complex.ofReal_intCast]
        linear_combination hn
      have hreal : -((k : ℝ) / (t1 : ℝ)) = ((n : ℤ) : ℝ) :=
        Complex.ofReal_injective (mul_right_cancel₀ h2pi hmul)
      have hdiv : (k : ℝ) / (t1 : ℝ) = -((n : ℤ) : ℝ) := neg_eq_iff_eq_neg.mp hreal
      have hkR : (k : ℝ) = (((t1 : ℤ) * (-n) : ℤ) : ℝ) := by
        have hdiv' := (div_eq_iff ht1R).mp hdiv
        push_cast at hdiv' ⊢
        linarith
      have hkZ : k = (t1 : ℤ) * (-n) := Int.cast_injective hkR
      exact hdvd ⟨-n, hkZ⟩
    have hω_pow : ω ^ t1 = 1 := by
      dsimp [ω]
      rw [← expNegTwoPiI_nat_mul, mul_div_cancel₀ _ ht1R, expNegTwoPiI_int]
    rw [geom_sum_eq hω_ne, hω_pow, sub_self, zero_div, mul_zero]

/-- Character orthogonality / mode-isolation sum identity for $k = u_1 - (u_2 - m r)$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
theorem mode_isolation_sum_sub {t1 r : ℕ} (ht1 : 0 < t1) (u1 : Fin t1) (u2 : Fin r) (m : ℤ) :
    (((t1 : ℝ)⁻¹ : ℂ) *
      ∑ j1 : Fin t1,
        expNegTwoPiI (((j1.val : ℝ) * ((u1.val : ℝ) - ((u2.val : ℝ) - (m : ℝ) * (r : ℝ)))) / (t1 : ℝ))) =
      if (t1 : ℤ) ∣ ((u1.val : ℤ) - ((u2.val : ℤ) - m * (r : ℤ))) then 1 else 0 := by
  have hcast : ((u1.val : ℝ) - ((u2.val : ℝ) - (m : ℝ) * (r : ℝ))) =
      ((((u1.val : ℤ) - ((u2.val : ℤ) - m * (r : ℤ)) : ℤ)) : ℝ) := by push_cast; ring
  rw [hcast]
  exact mode_isolation_sum_expNegTwoPiI ht1 _

/-- Spread 2D array $\tilde{x}_{j_1, k_2} = \sum_{d = -W}^{W} x_{j_1 + ((k_2 - d) \bmod r) t_1} f_{j_1}(d)$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Section 6.1 (`sec:filter-norms`)). -/
noncomputable def spreadArray {t1 r : ℕ} (hr : 0 < r) (W : ℕ)
    (x : Fin (t1 * r) → ℂ) (f : Fin t1 → ℤ → ℂ) (j1 : Fin t1) (k2 : Fin r) : ℂ :=
  ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
    x (strideFin j1 (intModFin r hr ((k2.val : ℤ) - d))) * f j1 d

/-- Modular fiber condition in `periodicFilterTap` is equivalent to `intModFin r hr d = m`. -/
theorem periodicFilterTap_cond_iff {r : ℕ} (hr : 0 < r) (W : ℕ) (d : ℤ) (m : Fin r) :
    (((d + (r : ℤ) * ((W : ℤ) + 1)) % (r : ℤ)).toNat = m.val) ↔ intModFin r hr d = m := by
  rw [Int.add_mul_emod_self_left]
  change (intModFin r hr d).val = m.val ↔ intModFin r hr d = m
  exact Fin.ext_iff.symm

/-- `spreadArray` with the truncated Sinc-Gaussian filter `filterTap` equals cyclic convolution
on `Fin r` with the folded periodic filter `periodicFilterTap` (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Section 6.1 (`sec:filter-norms`), Theorem 6.3 (`thm:spread`)). -/
theorem spreadArray_filterTap_eq_periodicFilterTap_conv (alpha : ℝ) (W : ℕ)
    {t1 r : ℕ} (hr : 0 < r) (x : Fin (t1 * r) → ℂ) (j1 : Fin t1) (k2 : Fin r) :
    spreadArray hr W x (fun j d => (filterTap alpha W t1 j d : ℂ)) j1 k2 =
      ∑ m : Fin r,
        x (strideFin j1 (intModFin r hr ((k2.val : ℤ) - (m.val : ℤ)))) *
          (periodicFilterTap alpha W t1 r j1 m : ℂ) := by
  unfold spreadArray periodicFilterTap
  have hmod_sub : ∀ d : ℤ,
      intModFin r hr ((k2.val : ℤ) - ((intModFin r hr d).val : ℤ)) =
        intModFin r hr ((k2.val : ℤ) - d) := by
    intro d
    apply Fin.ext
    apply Nat.cast_injective (R := ℤ)
    rw [intModFin_coe, intModFin_coe, intModFin_coe, Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
  have hrhs :
      (∑ m : Fin r,
        x (strideFin j1 (intModFin r hr ((k2.val : ℤ) - (m.val : ℤ)))) *
          ((∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
            if ((d + (r : ℤ) * ((W : ℤ) + 1)) % (r : ℤ)).toNat = m.val then
              sincGaussian alpha ((d : ℝ) - fractionalShift j1)
            else 0 : ℝ) : ℂ)) =
      ∑ m : Fin r,
        ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          (if intModFin r hr d = m then
            x (strideFin j1 (intModFin r hr ((k2.val : ℤ) - d))) *
              (sincGaussian alpha ((d : ℝ) - fractionalShift j1) : ℂ)
          else 0) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [periodicFilterTap_cond_iff hr W d m]
    split_ifs with hdm
    · subst hdm
      rw [hmod_sub d]
    · simp
  rw [hrhs, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.sum_ite_eq Finset.univ (intModFin r hr d)
    (fun _ => x (strideFin j1 (intModFin r hr ((k2.val : ℤ) - d))) *
      (sincGaussian alpha ((d : ℝ) - fractionalShift j1) : ℂ))]
  simp only [Finset.mem_univ, ↓reduceIte]
  have habs : |d| ≤ (W : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hd)
  rw [filterTap_of_abs_le habs]

/-- Discrete Fourier response $\hat{f}_{j_1}(u_2) = \sum_{d = -W}^{W} f_{j_1}(d) e^{2\pi i u_2 d / r}$ along the second axis (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def filterDiscreteResponse {t1 r : ℕ} (W : ℕ)
    (f : Fin t1 → ℤ → ℂ) (j1 : Fin t1) (u2 : Fin r) : ℂ :=
  ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
    f j1 d * expTwoPiI (((d : ℝ) * (u2.val : ℝ)) / (r : ℝ))

/-- Exact algebraic 2D-to-1D DFT factorization identity (the algebraic core of Theorem 4.2 (`thm:poisson`), Section 4.2 (`sec:poisson`)). -/
theorem normDFT2D_spreadArray_eq {t1 r : ℕ} (hr : 0 < r) (W : ℕ)
    (x : Fin (t1 * r) → ℂ) (f : Fin t1 → ℤ → ℂ) (u1 : Fin t1) (u2 : Fin r) :
    normDFT2D (spreadArray hr W x f) u1 u2 =
      (((t1 * r : ℕ) : ℝ)⁻¹ : ℂ) *
        ∑ j1 : Fin t1,
          (∑ m : Fin r, x (strideFin j1 m) * expTwoPiI (((m.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
            filterDiscreteResponse W f j1 u2 *
            expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) := by
  unfold normDFT2D spreadArray filterDiscreteResponse
  congr 1
  refine Finset.sum_congr rfl (fun j1 _ => ?_)
  have hinner :
      (∑ k2 : Fin r,
        (∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          x (strideFin j1 (intModFin r hr ((k2.val : ℤ) - d))) * f j1 d) *
          expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) *
          expTwoPiI (((k2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) =
      (∑ m : Fin r, x (strideFin j1 m) * expTwoPiI (((m.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
        (∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          f j1 d * expTwoPiI (((d : ℝ) * (u2.val : ℝ)) / (r : ℝ))) *
        expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have hswap :
        (∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          ∑ k2 : Fin r,
            x (strideFin j1 (intModFin r hr ((k2.val : ℤ) - d))) * f j1 d *
              expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) *
              expTwoPiI (((k2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) =
        ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          (∑ m : Fin r, x (strideFin j1 m) * expTwoPiI (((m.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
            (f j1 d * expTwoPiI (((d : ℝ) * (u2.val : ℝ)) / (r : ℝ))) *
            expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) := by
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [← (cyclicShiftEquiv r hr d).symm.sum_comp]
      simp_rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      have hm : intModFin r hr ((((cyclicShiftEquiv r hr d).symm m).val : ℤ) - d) = m :=
        (cyclicShiftEquiv r hr d).apply_symm_apply m
      have hexp :
          expTwoPiI (((((cyclicShiftEquiv r hr d).symm m).val * u2.val : ℕ) : ℝ) / (r : ℝ)) =
            expTwoPiI (((m.val * u2.val : ℕ) : ℝ) / (r : ℝ)) *
              expTwoPiI (((d : ℝ) * (u2.val : ℝ)) / (r : ℝ)) := by
        have hsymm : (cyclicShiftEquiv r hr d).symm m = intModFin r hr ((m.val : ℤ) + d) := rfl
        rw [hsymm]
        have hcast :
            ((((intModFin r hr ((m.val : ℤ) + d)).val * u2.val : ℕ) : ℝ) / (r : ℝ)) =
              (((intModFin r hr ((m.val : ℤ) + d)).val : ℝ) * ((u2.val : ℤ) : ℝ)) / (r : ℝ) := by
          push_cast; ring
        rw [hcast, expTwoPiI_intModFin_mul_div]
        have hsplit : ((((m.val : ℤ) + d : ℤ) : ℝ) * ((u2.val : ℤ) : ℝ)) / (r : ℝ) =
            (((m.val * u2.val : ℕ) : ℝ) / (r : ℝ)) + (((d : ℝ) * (u2.val : ℝ)) / (r : ℝ)) := by
          push_cast; ring
        rw [hsplit, expTwoPiI_add]
      rw [hm, hexp]
      ring
    rw [hswap]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  exact hinner

/-- Single-mode Poisson phase collapse: for any mode $m \in \mathbb{Z}$, the $m$-th Poisson frequency
term collapses the 2D sum into the 1D DFT at frequency $u_2 + r ((u_1 - m) \bmod t_1)$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), equation (18) (`eq:poisson-bridge`)). -/
theorem single_mode_poisson_collapse {t1 r : ℕ} (ht1 : 0 < t1)
    (x : Fin (t1 * r) → ℂ) (u1 : Fin t1) (u2 : Fin r) (m : ℤ) :
    (((t1 * r : ℕ) : ℝ)⁻¹ : ℂ) *
      ∑ j1 : Fin t1,
        (∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
          expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ)) *
          expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) =
      normDFT1D x (freqFin (intModFin t1 ht1 ((u1.val : ℤ) - m)) u2) := by
  by_cases hr : r = 0
  · subst hr
    simp [normDFT1D]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have ht1R : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrpos.ne'
  unfold normDFT1D
  congr 1
  rw [← (strideFinEquiv t1 r).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j1 _ => ?_)
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j2 _ => ?_)
  dsimp [strideFinEquiv]
  set u1_tilde := intModFin t1 ht1 ((u1.val : ℤ) - m)
  have hphase :
      expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ)) *
        expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ)) *
        expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) =
      expTwoPiI ((((strideFin j1 j2).val * (freqFin u1_tilde u2).val : ℕ) : ℝ) / ((t1 * r : ℕ) : ℝ)) := by
    have hu1 :
        expTwoPiI (((u1_tilde.val : ℝ) * (j1.val : ℝ)) / (t1 : ℝ)) =
          expTwoPiI (((((u1.val : ℤ) - m : ℤ) : ℝ) * (j1.val : ℝ)) / (t1 : ℝ)) := by
      have := expTwoPiI_intModFin_mul_div t1 ht1 ((u1.val : ℤ) - m) (j1.val : ℤ)
      simpa using this
    rw [← expTwoPiI_add, ← expTwoPiI_add]
    have h1 :
        (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ) +
          (((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ) +
          ((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) =
        (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ) +
          ((j1.val : ℝ) * (u2.val : ℝ)) / ((t1 : ℝ) * (r : ℝ))) +
          (((((u1.val : ℤ) - m : ℤ) : ℝ) * (j1.val : ℝ)) / (t1 : ℝ)) := by
      push_cast
      field_simp [ht1R, hrR]
      ring
    rw [h1, expTwoPiI_add, ← hu1, ← expTwoPiI_add]
    have h2 :
        ((((strideFin j1 j2).val * (freqFin u1_tilde u2).val : ℕ) : ℝ) / ((t1 * r : ℕ) : ℝ)) =
        ((((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ) +
          ((j1.val : ℝ) * (u2.val : ℝ)) / ((t1 : ℝ) * (r : ℝ))) +
          (((u1_tilde.val : ℝ) * (j1.val : ℝ)) / (t1 : ℝ))) +
          (((j2.val * u1_tilde.val : ℕ) : ℤ) : ℝ) := by
      dsimp [strideFin, freqFin]
      push_cast
      field_simp [ht1R, hrR]
      ring
    rw [h2, expTwoPiI_add_int]
  rw [← hphase]
  ring

/-! ### Vector and Matrix $\ell_\infty$-Norm Lemmas -/

private theorem vecInfNorm_nonneg {R : ℕ} (x : Fin R → ℂ) : 0 ≤ vecInfNorm x := by
  unfold vecInfNorm
  exact NNReal.coe_nonneg _

private theorem norm_le_vecInfNorm {R : ℕ} (x : Fin R → ℂ) (u : Fin R) :
    ‖x u‖ ≤ vecInfNorm x := by
  unfold vecInfNorm
  exact_mod_cast Finset.le_sup (f := fun v : Fin R => ‖x v‖₊) (Finset.mem_univ u)

private theorem matInfNorm_nonneg {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) : 0 ≤ matInfNorm U := by
  unfold matInfNorm
  exact NNReal.coe_nonneg _

private theorem norm_le_matInfNorm {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) (j1 : Fin t1) (k2 : Fin r) :
    ‖U j1 k2‖ ≤ matInfNorm U := by
  unfold matInfNorm
  exact_mod_cast Finset.le_sup (f := fun p : Fin t1 × Fin r => ‖U p.1 p.2‖₊) (Finset.mem_univ (j1, k2))

theorem matInfNorm_le_of_forall {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j1 k2, ‖U j1 k2‖ ≤ B) : matInfNorm U ≤ B := by
  unfold matInfNorm
  rw [← NNReal.coe_mk B hB, NNReal.coe_le_coe]
  refine Finset.sup_le (fun p _ => ?_)
  exact_mod_cast h p.1 p.2

/-- Matrix $\ell_\infty$-norm bound for the spread array: $\|\tilde{x}\|_\infty \le \|f\|_1 \|x\|_\infty$ (Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`)). -/
theorem matInfNorm_spreadArray_le {t1 r : ℕ} (hr : 0 < r) (W : ℕ)
    (x : Fin (t1 * r) → ℂ) (f : Fin t1 → ℤ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ j1 : Fin t1, ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), ‖f j1 d‖ ≤ L) :
    matInfNorm (spreadArray hr W x f) ≤ L * vecInfNorm x := by
  refine matInfNorm_le_of_forall _ (mul_nonneg hL (vecInfNorm_nonneg x)) (fun j1 k2 => ?_)
  unfold spreadArray
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
        ‖x (strideFin j1 (intModFin r hr ((k2.val : ℤ) - d))) * f j1 d‖
      ≤ ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), vecInfNorm x * ‖f j1 d‖ := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_le_vecInfNorm x _) (norm_nonneg _)
    _ = vecInfNorm x * ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), ‖f j1 d‖ := by
        rw [← Finset.mul_sum]
    _ ≤ L * vecInfNorm x := by
        nlinarith [hf j1, vecInfNorm_nonneg x]

/-- Spatial residual induced on $(F_{t_1, r} \tilde{x})_{u_1, u_2}$ by a filter response tail $E_{\text{tail}}(j_1, u_2)$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def poissonSpatialResidual {t1 r : ℕ}
    (x : Fin (t1 * r) → ℂ) (E_tail : Fin t1 → Fin r → ℂ) (u1 : Fin t1) (u2 : Fin r) : ℂ :=
  (((t1 * r : ℕ) : ℝ)⁻¹ : ℂ) *
    ∑ j1 : Fin t1,
      (∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
        E_tail j1 u2 *
        expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ))

/-- Bound on `poissonSpatialResidual` in terms of the row-wise tail bound $\varepsilon_{\text{tail}}$ and $\|x\|_\infty$. -/
theorem norm_poissonSpatialResidual_le {t1 r : ℕ} (ht1 : 0 < t1) (hr : 0 < r)
    (x : Fin (t1 * r) → ℂ) (E_tail : Fin t1 → Fin r → ℂ) (u1 : Fin t1) (u2 : Fin r)
    {eps : ℝ} (_heps : 0 ≤ eps) (hE : ∀ j1 : Fin t1, ‖E_tail j1 u2‖ ≤ eps) :
    ‖poissonSpatialResidual x E_tail u1 u2‖ ≤ eps * vecInfNorm x := by
  unfold poissonSpatialResidual
  have htr : (0 : ℝ) < ((t1 * r : ℕ) : ℝ) := by positivity
  have hnorm_inv : ‖(((t1 * r : ℕ) : ℝ)⁻¹ : ℂ)‖ = ((t1 * r : ℕ) : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg htr.le]
  rw [norm_mul, hnorm_inv]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr htr.le)).trans ?_
  have hrow : ∀ j1 : Fin t1,
      ‖(∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
        E_tail j1 u2 * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ))‖ ≤
        (r : ℝ) * vecInfNorm x * eps := by
    intro j1
    rw [norm_mul, norm_mul, norm_expTwoPiI, mul_one]
    have hsum :
        ‖∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))‖ ≤
          (r : ℝ) * vecInfNorm x := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ j2 : Fin r,
          ‖x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))‖ ≤ vecInfNorm x := by
        intro j2
        rw [norm_mul, norm_expTwoPiI, mul_one]
        exact norm_le_vecInfNorm x (strideFin j1 j2)
      calc ∑ j2 : Fin r, ‖x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))‖
          ≤ ∑ _j2 : Fin r, vecInfNorm x := Finset.sum_le_sum (fun j2 _ => hterm j2)
        _ = (r : ℝ) * vecInfNorm x := by simp
    exact mul_le_mul hsum (hE j1) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg r) (vecInfNorm_nonneg x))
  calc (((t1 * r : ℕ) : ℝ)⁻¹) * ∑ j1 : Fin t1,
        ‖(∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
          E_tail j1 u2 * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ))‖
      ≤ (((t1 * r : ℕ) : ℝ)⁻¹) * ∑ _j1 : Fin t1, ((r : ℝ) * vecInfNorm x * eps) := by
        gcongr
        exact hrow _
    _ = eps * vecInfNorm x := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
        have ht1R : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
        have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
        field_simp [ht1R, hrR]

/-- **Conditional Fractional-Shift Poisson Identity (`poisson_fractional_shift_identity_of_hresp`, Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`))**:
Given the explicit hypothesis `hresp` that for every `j1 : Fin t1`, the discrete Fourier response
`filterDiscreteResponse W f j1 u2` decomposes into the finite sum of Poisson modes `m ∈ S` plus
`E_tail j1 u2`:
`filterDiscreteResponse W f j1 u2 = (∑ m ∈ S, (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) * expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))) + E_tail j1 u2`,
the 2D DFT `normDFT2D (spreadArray hr W x f) u1 u2` equals the linear combination of shifted 1D DFT
values `normDFT1D x (freqFin (intModFin t1 ht1 ((u1.val : ℤ) - m)) u2)` plus
`poissonSpatialResidual x E_tail u1 u2`. -/
theorem poisson_fractional_shift_identity_of_hresp {t1 r : ℕ} (ht1 : 0 < t1) (hr : 0 < r) (W : ℕ)
    (alpha : ℝ) (x : Fin (t1 * r) → ℂ) (f : Fin t1 → ℤ → ℂ)
    (S : Finset ℤ) (E_tail : Fin t1 → Fin r → ℂ) (u1 : Fin t1) (u2 : Fin r)
    (hresp : ∀ j1 : Fin t1,
      filterDiscreteResponse W f j1 u2 =
        (∑ m ∈ S,
          (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
            expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))) +
          E_tail j1 u2) :
    normDFT2D (spreadArray hr W x f) u1 u2 =
      (∑ m ∈ S,
        (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
          normDFT1D x (freqFin (intModFin t1 ht1 ((u1.val : ℤ) - m)) u2)) +
        poissonSpatialResidual x E_tail u1 u2 := by
  rw [normDFT2D_spreadArray_eq hr W x f u1 u2]
  simp_rw [hresp]
  unfold poissonSpatialResidual
  have hdistrib :
      (∑ j1 : Fin t1,
        (∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
          ((∑ m ∈ S,
            (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
              expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))) +
            E_tail j1 u2) *
          expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ))) =
      (∑ m ∈ S,
        (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
          ∑ j1 : Fin t1,
            (∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
              expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ)) *
              expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ))) +
      ∑ j1 : Fin t1,
        (∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
          E_tail j1 u2 *
          expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) := by
    trans ∑ j1 : Fin t1,
      ((∑ m ∈ S,
        (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
          ((∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
            expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ)) *
            expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)))) +
      (∑ j2 : Fin r, x (strideFin j1 j2) * expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))) *
        E_tail j1 u2 *
        expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)))
    · refine Finset.sum_congr rfl (fun j1 _ => ?_)
      rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun m _ => by ring)
    · rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← Finset.mul_sum]
  rw [hdistrib, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← single_mode_poisson_collapse ht1 x u1 u2 m]
  ring

/-- Concrete frequency-domain residual for the truncated Sinc-Gaussian filter `filterTap alpha W t1`
relative to a finite Poisson mode set `S : Finset ℤ` (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def concretePoissonResidual (alpha : ℝ) (W : ℕ) {t1 r : ℕ}
    (S : Finset ℤ) (j1 : Fin t1) (u2 : Fin r) : ℂ :=
  filterDiscreteResponse W (fun j d => (filterTap alpha W t1 j d : ℂ)) j1 u2 -
    ∑ m ∈ S,
      (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
        expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))

/-- **Theorem 4.2 (`thm:poisson`) (Fractional-Shift Poisson Identity for `filterTap`, Section 4.2 (`sec:poisson`), equation (18) (`eq:poisson-bridge`))**:
For any positive radices `0 < t1`, `0 < r`, window half-width `W : ℕ`, kernel parameter `alpha : ℝ`,
input vector `x : Fin (t1 * r) → ℂ`, and finite mode set `S : Finset ℤ`, the 2D DFT of the
`filterTap`-spread array equals the linear combination of shifted 1D DFT values over `m ∈ S`
plus `poissonSpatialResidual x (concretePoissonResidual alpha W S) u1 u2`. -/
theorem poisson_fractional_shift_identity {t1 r : ℕ} (ht1 : 0 < t1) (hr : 0 < r) (W : ℕ)
    (alpha : ℝ) (x : Fin (t1 * r) → ℂ)
    (S : Finset ℤ) (u1 : Fin t1) (u2 : Fin r) :
    normDFT2D (spreadArray hr W x (fun j1 d => (filterTap alpha W t1 j1 d : ℂ))) u1 u2 =
      (∑ m ∈ S,
        (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
          normDFT1D x (freqFin (intModFin t1 ht1 ((u1.val : ℤ) - m)) u2)) +
        poissonSpatialResidual x (concretePoissonResidual alpha W S) u1 u2 := by
  refine poisson_fractional_shift_identity_of_hresp ht1 hr W alpha x
    (fun j1 d => (filterTap alpha W t1 j1 d : ℂ)) S (concretePoissonResidual alpha W S) u1 u2 ?_
  intro j1
  unfold concretePoissonResidual
  exact (add_sub_cancel _ _).symm

/-! ## 4. Passband/Stopband Estimates (Theorem 5.1 (`thm:deconv`)) & Filter Norm / Spatial Tail Bounds (Lemma 6.1 (`lem:filter-norms`)) -/

/-- Square of the Sinc-Gaussian shape parameter: $\alpha^2 = 4 p_{\text{work}} \ln 2 / \pi$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`)). -/
theorem alphaFromPWork_sq (pWork : ℕ) :
    (alphaFromPWork pWork) ^ 2 = 4 * (pWork : ℝ) * Real.log 2 / Real.pi := by
  unfold alphaFromPWork
  have hnonneg : 0 ≤ ((pWork : ℝ) * Real.log 2) / Real.pi := by
    positivity [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2), Real.pi_pos.le]
  rw [mul_pow, Real.sq_sqrt hnonneg]
  ring

theorem alphaFromPWork_pos {pWork : ℕ} (hp : 1 ≤ pWork) : 0 < alphaFromPWork pWork := by
  unfold alphaFromPWork
  have hpR : (0 : ℝ) < (pWork : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  positivity [Real.pi_pos]

theorem sqrt_p_log_two_div_pi_ge_five_fourths {p : ℕ} (hp : 8 ≤ p) :
    (5 / 4 : ℝ) ≤ Real.sqrt (((p : ℝ) * Real.log 2) / Real.pi) := by
  refine Real.le_sqrt_of_sq_le ?_
  have hpR : (8 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
  have hlog : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  rw [le_div_iff₀ hpi_pos]
  nlinarith

theorem two_le_alphaFromPWork {pWork : ℕ} (hp : 8 ≤ pWork) : 2 ≤ alphaFromPWork pWork := by
  unfold alphaFromPWork
  have h := sqrt_p_log_two_div_pi_ge_five_fourths hp
  linarith

/-- Square of $\sqrt{\pi} \alpha$: $(\sqrt{\pi} \alpha)^2 = 4 p_{\text{work}} \ln 2$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`)). -/
theorem sqrt_pi_mul_alphaFromPWork_sq (pWork : ℕ) :
    (Real.sqrt Real.pi * alphaFromPWork pWork) ^ 2 = 4 * (pWork : ℝ) * Real.log 2 := by
  rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, alphaFromPWork_sq]
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi_ne]

/-- Nyquist passband lower bound: for $p_{\text{work}} \ge 8$,
$\hat{g}_{\alpha(p_{\text{work}})}(1/2) \ge 49999999 / 100000000$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1(1) (`thm:deconv`), equation (20) (`eq:passband`)). -/
theorem gHat_alphaFromPWork_half_ge {pWork : ℕ} (hp : 8 ≤ pWork) :
    (49999999 / 100000000 : ℝ) ≤ gHat (alphaFromPWork pWork) (1 / 2) := by
  set z : ℝ := Real.sqrt Real.pi * alphaFromPWork pWork
  have halpha_ge : 2 ≤ alphaFromPWork pWork := two_le_alphaFromPWork hp
  have hsqrt_pi : 1 ≤ Real.sqrt Real.pi := by
    refine Real.le_sqrt_of_sq_le ?_
    linarith [Real.pi_gt_three]
  have hz_ge : 2 ≤ z := by
    dsimp [z]
    nlinarith
  have hz_pos : 0 < z := by linarith
  have hz_sq : z ^ 2 = 4 * (pWork : ℝ) * Real.log 2 := sqrt_pi_mul_alphaFromPWork_sq pWork
  have hlog : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpR : (8 : ℝ) ≤ (pWork : ℝ) := Nat.cast_le.mpr hp
  have hz_sq_ge : 32 * Real.log 2 ≤ z ^ 2 := by
    rw [hz_sq]
    nlinarith
  have hexp_le : Real.exp (-(z ^ 2)) ≤ (1 / 4294967296 : ℝ) := by
    have h32 : Real.exp (-(32 * Real.log 2)) = (1 / 4294967296 : ℝ) := by
      have hcast : -(32 * Real.log 2) = -(((32 : ℕ) : ℝ) * Real.log 2) := by push_cast; ring
      rw [hcast, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [← h32, Real.exp_le_exp]
    linarith
  have hinv_le : 1 / (Real.sqrt Real.pi * z) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have herfc : erfc z ≤ (1 / 4294967296 : ℝ) := by
    calc erfc z
        ≤ (1 / (Real.sqrt Real.pi * z)) * Real.exp (-(z ^ 2)) :=
          erfc_le_inv_sqrt_pi_mul_exp hz_pos
      _ ≤ 1 * (1 / 4294967296 : ℝ) :=
          mul_le_mul hinv_le hexp_le (Real.exp_pos _).le zero_le_one
      _ = (1 / 4294967296 : ℝ) := one_mul _
  have hg_eq : gHat (alphaFromPWork pWork) (1 / 2) = (1 / 2 : ℝ) * (1 - erfc z) := by
    unfold gHat erfc
    have h0 : Real.sqrt Real.pi * alphaFromPWork pWork * (1 / 2 - (1 / 2 : ℝ)) = 0 := by ring
    have h1 : Real.sqrt Real.pi * alphaFromPWork pWork * (1 / 2 + (1 / 2 : ℝ)) = z := by
      dsimp [z]; ring
    rw [h0, h1, erf_zero, zero_add]
    ring
  rw [hg_eq]
  linarith

/-- **Theorem 5.1(1) (`thm:deconv`) Uniform $\Omega(1)$ Passband Lower Bound (`gHat_passband_max_ge`, Section 5.1 (`sec:deconv-thm`), equation (20) (`eq:passband`))**:
For $p_{\text{work}} \ge 8$ and $y \in [0, 1]$,
$\max(\hat{g}_\alpha(y), \hat{g}_\alpha(y - 1)) \ge \frac{49999999}{100000000}$. -/
theorem gHat_passband_max_ge (pWork : ℕ) (hp : 8 ≤ pWork) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (49999999 / 100000000 : ℝ) ≤
      max (gHat (alphaFromPWork pWork) y) (gHat (alphaFromPWork pWork) (y - 1)) := by
  have halpha0 : 0 ≤ alphaFromPWork pWork := (alphaFromPWork_pos (by omega)).le
  have hhalf := gHat_alphaFromPWork_half_ge hp
  rcases le_or_gt y (1 / 2 : ℝ) with hle | hgt
  · exact hhalf.trans ((gHat_half_le_of_le_half halpha0 hy0 hle).trans (le_max_left _ _))
  · rw [gHat_symm_one]
    exact hhalf.trans ((gHat_half_le_of_le_half halpha0 (by linarith) (by linarith)).trans (le_max_right _ _))

/-- **Theorem 5.1(1) (`thm:deconv`) Stopband Alias Tail Bound (`gHat_stopband_alias_lt`, Section 5.1 (`sec:deconv-thm`), equation (21) (`eq:stopband`), Table 3 (`tab:lean-map`))**:
For $p_{\text{work}} \ge 8$ and $y \in [0, 1]$,
$1 - \hat{g}_\alpha(y) - \hat{g}_\alpha(y - 1) < 0.15 \cdot 2^{-p_{\text{work}}}$. -/
theorem gHat_stopband_alias_lt (pWork : ℕ) (hp : 8 ≤ pWork) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - gHat (alphaFromPWork pWork) y - gHat (alphaFromPWork pWork) (y - 1) <
      (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)) := by
  rw [gHat_symm_one, one_sub_gHat_sub_gHat_one_sub]
  set c : ℝ := Real.sqrt Real.pi * alphaFromPWork pWork
  have hc_sq : c ^ 2 = 4 * (pWork : ℝ) * Real.log 2 := sqrt_pi_mul_alphaFromPWork_sq pWork
  have hpR : (8 : ℝ) ≤ (pWork : ℝ) := Nat.cast_le.mpr hp
  have hlog : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hc_pos : 0 < c := mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (alphaFromPWork_pos (by omega))
  have hsqrt_pi_c_half : 4 ≤ Real.sqrt Real.pi * (c * (1 / 2)) := by
    set X := Real.sqrt Real.pi * (c * (1 / 2))
    have hX_pos : 0 < X := by positivity
    have hX_sq : 16 ≤ X ^ 2 := by
      dsimp [X]
      rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, hc_sq]
      nlinarith
    have hprod : 0 ≤ (X + 4) * (X - 4) := by linarith
    nlinarith
  have hexp_pWork : Real.exp (-((pWork : ℝ) * Real.log 2)) = (2 : ℝ) ^ (-(pWork : ℤ)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      zpow_neg, zpow_natCast]
  have hbound_half : ∀ u : ℝ, 1 / 2 ≤ u →
      (1 / 2 : ℝ) * erfc (c * u) ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)) := by
    intro u hu
    have hcu_pos : 0 < c * u := by positivity
    have hcu_ge : c * (1 / 2) ≤ c * u := mul_le_mul_of_nonneg_left hu hc_pos.le
    have hdenom : 4 ≤ Real.sqrt Real.pi * (c * u) :=
      hsqrt_pi_c_half.trans (mul_le_mul_of_nonneg_left hcu_ge (Real.sqrt_nonneg _))
    have hinv : 1 / (Real.sqrt Real.pi * (c * u)) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hdenom
    have hsq_ge : (pWork : ℝ) * Real.log 2 ≤ (c * u) ^ 2 := by
      have h1 : (c * (1 / 2)) ^ 2 ≤ (c * u) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcu_ge 2
      have h2 : (c * (1 / 2)) ^ 2 = (pWork : ℝ) * Real.log 2 := by
        rw [mul_pow, hc_sq]; ring
      linarith
    have hexp : Real.exp (-((c * u) ^ 2)) ≤ (2 : ℝ) ^ (-(pWork : ℤ)) := by
      rw [← hexp_pWork, Real.exp_le_exp]
      linarith
    have herfc := erfc_le_inv_sqrt_pi_mul_exp hcu_pos
    have hmul := mul_le_mul hinv hexp (Real.exp_pos _).le (by norm_num)
    linarith
  have hbound_one : ∀ u : ℝ, 1 ≤ u →
      (1 / 2 : ℝ) * erfc (c * u) ≤ (1 / 128 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)) := by
    intro u hu
    have hcu_pos : 0 < c * u := by positivity
    have hcu_ge : c ≤ c * u := le_mul_of_one_le_right hc_pos.le hu
    have hcu_ge_half : c * (1 / 2) ≤ c * u := by linarith
    have hdenom : 4 ≤ Real.sqrt Real.pi * (c * u) :=
      hsqrt_pi_c_half.trans (mul_le_mul_of_nonneg_left hcu_ge_half (Real.sqrt_nonneg _))
    have hinv : 1 / (Real.sqrt Real.pi * (c * u)) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hdenom
    have hsq_ge : (pWork : ℝ) * Real.log 2 + 15 ≤ (c * u) ^ 2 := by
      have h1 : c ^ 2 ≤ (c * u) ^ 2 := pow_le_pow_left₀ hc_pos.le hcu_ge 2
      nlinarith
    have hexp15 : Real.exp (-15) ≤ 1 / 16 := by
      rw [Real.exp_neg, inv_eq_one_div]
      refine one_div_le_one_div_of_le (by norm_num) ?_
      linarith [Real.add_one_le_exp (15 : ℝ)]
    have hexp : Real.exp (-((c * u) ^ 2)) ≤ (1 / 16 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)) := by
      calc Real.exp (-((c * u) ^ 2))
          ≤ Real.exp (-((pWork : ℝ) * Real.log 2) + (-15 : ℝ)) := by
            rw [Real.exp_le_exp]; linarith
        _ = (2 : ℝ) ^ (-(pWork : ℤ)) * Real.exp (-15) := by
            rw [Real.exp_add, hexp_pWork]
        _ ≤ (1 / 16 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)) := by
            nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (-(pWork : ℤ))]
    have herfc := erfc_le_inv_sqrt_pi_mul_exp hcu_pos
    have hmul := mul_le_mul hinv hexp (Real.exp_pos _).le (by norm_num)
    linarith
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(pWork : ℤ)) := zpow_pos (by norm_num) _
  rcases le_or_gt y (1 / 2 : ℝ) with hle | hgt
  · have h1 := hbound_half (y + 1 / 2) (by linarith)
    have h2 := hbound_one (3 / 2 - y) (by linarith)
    linarith
  · have h1 := hbound_one (y + 1 / 2) (by linarith)
    have h2 := hbound_half (3 / 2 - y) (by linarith)
    linarith

/-- Cubic lower bound on `erf x` for $x \in [0, 1]$: $\operatorname{erf}(x) \ge \frac{74}{100} x$. -/
theorem erf_ge_of_nonneg_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (74 / 100 : ℝ) * x ≤ erf x := by
  unfold erf
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun u : ℝ => u - u ^ 3 / 3) (1 - t ^ 2) t := by
    intro t _
    exact ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)).congr_deriv (by dsimp; ring)
  have hcont1 : Continuous (fun t : ℝ => 1 - t ^ 2) := by fun_prop
  have hcont2 : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by fun_prop
  have hint_poly : (∫ t in (0 : ℝ)..x, (1 - t ^ 2)) = x - x ^ 3 / 3 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont1.intervalIntegrable _ _)]
    ring
  have hmono : (∫ t in (0 : ℝ)..x, (1 - t ^ 2)) ≤ ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
    refine intervalIntegral.integral_mono_on hx0
      (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _) (fun t _ => ?_)
    linarith [Real.add_one_le_exp (-(t ^ 2))]
  have hx3 : x ^ 3 ≤ x := by nlinarith [sq_nonneg x]
  have hint_ge : (2 / 3 : ℝ) * x ≤ ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
    linarith
  have hsqrt_pi_le : Real.sqrt Real.pi ≤ 178 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith [Real.pi_lt_d4]
  have hcoeff : (100 / 89 : ℝ) ≤ 2 / Real.sqrt Real.pi := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
    linarith
  have hmul : (100 / 89 : ℝ) * ((2 / 3 : ℝ) * x) ≤
      (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) :=
    mul_le_mul hcoeff hint_ge (by positivity) (by positivity)
  linarith

/-- Upper bound on $\frac{1}{2}(\operatorname{erf}(c + x) - \operatorname{erf}(c - x))$ when $c \ge 33/5$ and $x \in [0, 1]$. -/
theorem half_mul_erf_add_sub_erf_sub_le {c x : ℝ} (hc : (33 / 5 : ℝ) ≤ c)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 / 2 : ℝ) * (erf (c + x) - erf (c - x)) ≤ (1 / 16 : ℝ) * x := by
  unfold erf
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by fun_prop
  have hsub := intervalIntegral.integral_interval_sub_left
    (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := c + x) (c := c - x)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hlen : c - x ≤ c + x := by linarith
  have hexp31 : Real.exp (-31) ≤ 1 / 32 := by
    rw [Real.exp_neg, inv_eq_one_div]
    refine one_div_le_one_div_of_le (by norm_num) ?_
    linarith [Real.add_one_le_exp (31 : ℝ)]
  have hmono : (∫ t in (c - x)..(c + x), Real.exp (-(t ^ 2))) ≤
      ∫ _t in (c - x)..(c + x), (1 / 32 : ℝ) := by
    refine intervalIntegral.integral_mono_on hlen
      (hcont.intervalIntegrable _ _) intervalIntegrable_const (fun t ht => ?_)
    have ht_ge : (28 / 5 : ℝ) ≤ t := by linarith [ht.1]
    have htsq : (31 : ℝ) ≤ t ^ 2 := by nlinarith
    have hexp_le : Real.exp (-(t ^ 2)) ≤ Real.exp (-31) := by
      rw [Real.exp_le_exp]; linarith
    exact hexp_le.trans hexp31
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hsqrt_ge : 1 ≤ Real.sqrt Real.pi := by
    refine Real.le_sqrt_of_sq_le ?_
    linarith [Real.pi_gt_three]
  have hinv_sqrt : 1 / Real.sqrt Real.pi ≤ 1 := div_le_one_of_le₀ hsqrt_ge (by positivity)
  have hcomb : (1 / 2 : ℝ) *
      ((2 / Real.sqrt Real.pi) * (∫ t in (0 : ℝ)..(c + x), Real.exp (-(t ^ 2))) -
        (2 / Real.sqrt Real.pi) * (∫ t in (0 : ℝ)..(c - x), Real.exp (-(t ^ 2)))) =
      (1 / Real.sqrt Real.pi) * ∫ t in (c - x)..(c + x), Real.exp (-(t ^ 2)) := by
    rw [← mul_sub, ← hsub]
    ring
  rw [hcomb]
  have hbound : (1 / Real.sqrt Real.pi) * ∫ t in (c - x)..(c + x), Real.exp (-(t ^ 2)) ≤
      1 * ((c + x - (c - x)) * (1 / 32 : ℝ)) := by
    refine mul_le_mul hinv_sqrt hmono ?_ zero_le_one
    exact intervalIntegral.integral_nonneg hlen (fun _ _ => (Real.exp_pos _).le)
  linarith

/-- Near-Nyquist ratio bound when $x = \sqrt{\pi} \alpha \varepsilon \le 1$. -/
theorem gHat_half_add_div_gHat_half_sub_le_exp_of_le_one {alpha ε : ℝ}
    (halpha_pos : 0 < alpha) (hε_nonneg : 0 ≤ ε)
    (hc_ge : (33 / 5 : ℝ) ≤ Real.sqrt Real.pi * alpha)
    (hx1 : Real.sqrt Real.pi * alpha * ε ≤ 1) :
    gHat alpha (1 / 2 + ε) / gHat alpha (1 / 2 - ε) ≤
      Real.exp (-((20 / 33 : ℝ) * (Real.sqrt Real.pi * alpha * ε))) := by
  generalize hc_def : Real.sqrt Real.pi * alpha = c
  rw [hc_def] at hc_ge hx1
  generalize hx_def : c * ε = x
  rw [hx_def] at hx1
  have hx0 : 0 ≤ x := by rw [← hx_def]; positivity
  have hg_sub_pos : 0 < gHat alpha (1 / 2 - ε) := gHat_pos alpha halpha_pos (1 / 2 - ε)
  have hg_sub_le_one : gHat alpha (1 / 2 - ε) ≤ 1 := gHat_le_one alpha (1 / 2 - ε)
  have herf_x := erf_ge_of_nonneg_of_le_one hx0 hx1
  have htail_x := half_mul_erf_add_sub_erf_sub_le hc_ge hx0 hx1
  have hdiff_eq : gHat alpha (1 / 2 - ε) - gHat alpha (1 / 2 + ε) =
      erf x - (1 / 2 : ℝ) * (erf (c + x) - erf (c - x)) := by
    unfold gHat
    have h1 : Real.sqrt Real.pi * alpha * (1 / 2 - (1 / 2 - ε)) = x := by
      rw [← hx_def, ← hc_def]; ring
    have h2 : Real.sqrt Real.pi * alpha * (1 / 2 + (1 / 2 - ε)) = c - x := by
      rw [← hx_def, ← hc_def]; ring
    have h3 : Real.sqrt Real.pi * alpha * (1 / 2 - (1 / 2 + ε)) = -x := by
      rw [← hx_def, ← hc_def]; ring
    have h4 : Real.sqrt Real.pi * alpha * (1 / 2 + (1 / 2 + ε)) = c + x := by
      rw [← hx_def, ← hc_def]; ring
    rw [h1, h2, h3, h4, erf_odd]
    ring
  have hdiff_ge : (20 / 33 : ℝ) * x ≤ gHat alpha (1 / 2 - ε) - gHat alpha (1 / 2 + ε) := by
    rw [hdiff_eq]
    linarith only [herf_x, htail_x, hx0]
  have hdiv_diff : (20 / 33 : ℝ) * x ≤
      (gHat alpha (1 / 2 - ε) - gHat alpha (1 / 2 + ε)) / gHat alpha (1 / 2 - ε) := by
    rw [le_div_iff₀ hg_sub_pos]
    nlinarith only [hdiff_ge, hg_sub_le_one, hx0]
  have h1 : gHat alpha (1 / 2 + ε) / gHat alpha (1 / 2 - ε) =
      1 - (gHat alpha (1 / 2 - ε) - gHat alpha (1 / 2 + ε)) / gHat alpha (1 / 2 - ε) := by
    rw [sub_div, div_self hg_sub_pos.ne']
    ring
  have h2 := Real.add_one_le_exp (-((20 / 33 : ℝ) * x))
  linarith only [hdiv_diff, h1, h2]

/-- Far-from-Nyquist ratio bound when $x = \sqrt{\pi} \alpha \varepsilon > 1$. -/
theorem gHat_half_add_div_gHat_half_sub_le_of_gt_one {alpha ε : ℝ}
    (halpha_pos : 0 < alpha) (hε_nonneg : 0 ≤ ε) (hε_hi : ε ≤ 1 / 2)
    (hhalf : (9 / 20 : ℝ) ≤ gHat alpha (1 / 2))
    (hx1 : 1 < Real.sqrt Real.pi * alpha * ε) :
    gHat alpha (1 / 2 + ε) / gHat alpha (1 / 2 - ε) ≤ 10 / 27 := by
  generalize hc_def : Real.sqrt Real.pi * alpha = c
  rw [hc_def] at hx1
  generalize hx_def : c * ε = x
  rw [hx_def] at hx1
  have hx_pos : 0 < x := by linarith only [hx1]
  have hg_sub_pos : 0 < gHat alpha (1 / 2 - ε) := gHat_pos alpha halpha_pos (1 / 2 - ε)
  have hg_add_eq : gHat alpha (1 / 2 + ε) = (1 / 2 : ℝ) * (erf (c + x) - erf x) := by
    unfold gHat
    have h3 : Real.sqrt Real.pi * alpha * (1 / 2 - (1 / 2 + ε)) = -x := by
      rw [← hx_def, ← hc_def]; ring
    have h4 : Real.sqrt Real.pi * alpha * (1 / 2 + (1 / 2 + ε)) = c + x := by
      rw [← hx_def, ← hc_def]; ring
    rw [h3, h4, erf_odd]
    ring
  have hsqrt_pi_ge : (3 / 2 : ℝ) ≤ Real.sqrt Real.pi := by
    refine Real.le_sqrt_of_sq_le ?_
    linarith [Real.pi_gt_three]
  have hinv_le : 1 / (Real.sqrt Real.pi * x) ≤ 2 / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hsqrt_pi_ge, hx1]
  have hexp_x : Real.exp (-(x ^ 2)) ≤ 1 / 2 := by
    have hx2 : 1 ≤ x ^ 2 := by nlinarith only [hx1]
    have hle : Real.exp (-(x ^ 2)) ≤ Real.exp (-1) := by
      rw [Real.exp_le_exp]; linarith only [hx2]
    exact hle.trans Real.exp_neg_one_lt_half.le
  have herfc_x : erfc x ≤ 1 / 3 := by
    calc erfc x
        ≤ (1 / (Real.sqrt Real.pi * x)) * Real.exp (-(x ^ 2)) :=
          erfc_le_inv_sqrt_pi_mul_exp hx_pos
      _ ≤ (2 / 3 : ℝ) * (1 / 2 : ℝ) :=
          mul_le_mul hinv_le hexp_x (Real.exp_pos _).le (by norm_num)
      _ = 1 / 3 := by norm_num
  have hg_add_le : gHat alpha (1 / 2 + ε) ≤ 1 / 6 := by
    rw [hg_add_eq]
    have h1 := erf_le_one (c + x)
    unfold erfc at herfc_x
    linarith only [h1, herfc_x]
  have hg_sub_ge : (9 / 20 : ℝ) ≤ gHat alpha (1 / 2 - ε) := by
    have hmono := gHat_half_le_of_le_half (y := 1 / 2 - ε) halpha_pos.le
      (by linarith only [hε_hi]) (by linarith only [hε_nonneg])
    linarith only [hhalf, hmono]
  rw [div_le_iff₀ hg_sub_pos]
  linarith only [hg_add_le, hg_sub_ge]

/-- Secant ratio power bound on $[1/(2 t_1), 1/2]$ when $p_{\text{work}} \ge 16$ and $t_1 \ge 2$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1(2) (`thm:deconv`)). -/
theorem gHat_half_add_div_gHat_half_sub_pow_le {pWork t1 : ℕ}
    (hp : 16 ≤ pWork) (ht1 : 2 ≤ t1) {ε : ℝ}
    (hε_lo : 1 / (2 * (t1 : ℝ)) ≤ ε) (hε_hi : ε ≤ 1 / 2) :
    (gHat (alphaFromPWork pWork) (1 / 2 + ε) /
      gHat (alphaFromPWork pWork) (1 / 2 - ε)) ^ t1 ≤ (15 / 100 : ℝ) := by
  have hp8 : 8 ≤ pWork := by omega
  have halpha_pos : 0 < alphaFromPWork pWork := alphaFromPWork_pos (by omega)
  have hc_sq : (Real.sqrt Real.pi * alphaFromPWork pWork) ^ 2 = 4 * (pWork : ℝ) * Real.log 2 :=
    sqrt_pi_mul_alphaFromPWork_sq pWork
  have hpR : (16 : ℝ) ≤ (pWork : ℝ) := Nat.cast_le.mpr hp
  have hlog : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc_ge : (33 / 5 : ℝ) ≤ Real.sqrt Real.pi * alphaFromPWork pWork := by
    set c := Real.sqrt Real.pi * alphaFromPWork pWork
    have hc_pos : 0 < c := mul_pos (Real.sqrt_pos.mpr Real.pi_pos) halpha_pos
    have hsq : (33 / 5 : ℝ) ^ 2 ≤ c ^ 2 := by rw [hc_sq]; nlinarith only [hpR, hlog]
    have hprod : 0 ≤ (c + 33 / 5) * (c - 33 / 5) := by linarith only [hsq]
    nlinarith only [hc_pos, hprod]
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hε_pos : 0 < ε := lt_of_lt_of_le (by positivity) hε_lo
  have hg_sub_pos : 0 < gHat (alphaFromPWork pWork) (1 / 2 - ε) :=
    gHat_pos (alphaFromPWork pWork) halpha_pos (1 / 2 - ε)
  have hg_add_nonneg : 0 ≤ gHat (alphaFromPWork pWork) (1 / 2 + ε) :=
    gHat_nonneg (alphaFromPWork pWork) halpha_pos.le (1 / 2 + ε)
  have hq_nonneg : 0 ≤ gHat (alphaFromPWork pWork) (1 / 2 + ε) / gHat (alphaFromPWork pWork) (1 / 2 - ε) :=
    div_nonneg hg_add_nonneg hg_sub_pos.le
  rcases le_or_gt (Real.sqrt Real.pi * alphaFromPWork pWork * ε) 1 with hx1 | hx1
  · have hq_le_exp := gHat_half_add_div_gHat_half_sub_le_exp_of_le_one halpha_pos hε_pos.le hc_ge hx1
    have ht1_eps : (1 / 2 : ℝ) ≤ (t1 : ℝ) * ε := by
      have := mul_le_mul_of_nonneg_left hε_lo ht1_pos.le
      have hcancel : (t1 : ℝ) * (1 / (2 * (t1 : ℝ))) = 1 / 2 := by field_simp [ht1_pos.ne']
      linarith
    have hexp_arg : (t1 : ℝ) * (-((20 / 33 : ℝ) * (Real.sqrt Real.pi * alphaFromPWork pWork * ε))) ≤ -2 := by
      set c := Real.sqrt Real.pi * alphaFromPWork pWork
      have hce : (33 / 10 : ℝ) ≤ c * ((t1 : ℝ) * ε) := by nlinarith only [hc_ge, ht1_eps]
      linarith only [hce]
    have hexp_neg2 : Real.exp (-2) ≤ (15 / 100 : ℝ) := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have he1 : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [he2]
      nlinarith only [he1]
    calc (gHat (alphaFromPWork pWork) (1 / 2 + ε) / gHat (alphaFromPWork pWork) (1 / 2 - ε)) ^ t1
        ≤ (Real.exp (-((20 / 33 : ℝ) * (Real.sqrt Real.pi * alphaFromPWork pWork * ε)))) ^ t1 :=
          pow_le_pow_left₀ hq_nonneg hq_le_exp t1
      _ = Real.exp ((t1 : ℝ) * (-((20 / 33 : ℝ) * (Real.sqrt Real.pi * alphaFromPWork pWork * ε)))) :=
          (Real.exp_nat_mul _ t1).symm
      _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr hexp_arg
      _ ≤ (15 / 100 : ℝ) := hexp_neg2
  · have hhalf9 : (9 / 20 : ℝ) ≤ gHat (alphaFromPWork pWork) (1 / 2) :=
      (by norm_num : (9 / 20 : ℝ) ≤ 49999999 / 100000000).trans (gHat_alphaFromPWork_half_ge hp8)
    have hq_le := gHat_half_add_div_gHat_half_sub_le_of_gt_one halpha_pos hε_pos.le hε_hi hhalf9 hx1
    calc (gHat (alphaFromPWork pWork) (1 / 2 + ε) / gHat (alphaFromPWork pWork) (1 / 2 - ε)) ^ t1
        ≤ (10 / 27 : ℝ) ^ t1 := pow_le_pow_left₀ hq_nonneg hq_le t1
      _ ≤ (10 / 27 : ℝ) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) ht1
      _ ≤ (15 / 100 : ℝ) := by norm_num

/-- **Theorem 5.1(2) (`thm:deconv`) Non-Nyquist Secant Wrap-Around Ratio Bound (`gHat_ratio_pow_t1_le_015`, Section 5.1 (`sec:deconv-thm`), equation (22) (`eq:wrap-bound`), Table 3 (`tab:lean-map`))**:
For $K \ge 2$, $p \ge 8$, and any column $u_2 \in \operatorname{Fin}(r_\ell)$ with $u_2 \ne r_\ell / 2$,
$\left(\frac{\min(\hat{g}_\alpha(u_2/r_\ell), \hat{g}_\alpha(u_2/r_\ell - 1))}{\max(\hat{g}_\alpha(u_2/r_\ell), \hat{g}_\alpha(u_2/r_\ell - 1))}\right)^{t_{1,\ell}} \le 0.15$. -/
theorem gHat_ratio_pow_t1_le_015 (K p : ℕ) (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2) :
    (min (gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ)))
         (gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1)) /
     max (gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ)))
         (gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1))) ^ (t1Ell K) ≤
      (15 / 100 : ℝ) := by
  unfold alphaEll
  have hpWork : 16 ≤ pWorkEll K p := by unfold pWorkEll; omega
  have hk1 : 1 ≤ k1Ell K := by unfold k1Ell; omega
  have ht1 : 2 ≤ t1Ell K := by
    unfold t1Ell
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k1Ell K := Nat.pow_le_pow_right (by norm_num) hk1
  have hk2 : 1 ≤ k2Ell K := by unfold k2Ell; omega
  have hr_even : 2 * (rEll K / 2) = rEll K := by
    unfold rEll
    have hpow : 2 ∣ 2 ^ k2Ell K := dvd_pow_self 2 (by omega)
    exact Nat.mul_div_cancel' hpow
  have hr_pos : (0 : ℝ) < (rEll K : ℝ) := Nat.cast_pos.mpr (rEll_pos K)
  have ht1_pos : (0 : ℝ) < (t1Ell K : ℝ) := Nat.cast_pos.mpr (t1Ell_pos K)
  set y : ℝ := (u2.val : ℝ) / (rEll K : ℝ)
  set ε : ℝ := |1 / 2 - y|
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) hr_pos.le
  have hy1 : y ≤ 1 := div_le_one_of_le₀ (Nat.cast_le.mpr u2.isLt.le) hr_pos.le
  have hε_hi : ε ≤ 1 / 2 := by
    dsimp [ε]
    rw [abs_le]
    constructor <;> linarith
  have hε_r : 1 / (rEll K : ℝ) ≤ ε := by
    have hdiff_int : (1 : ℝ) ≤ |((rEll K / 2 : ℕ) : ℝ) - (u2.val : ℝ)| := by
      have hne : ((rEll K / 2 : ℕ) : ℤ) ≠ (u2.val : ℤ) := by exact_mod_cast hu2.symm
      have habs_int : (1 : ℤ) ≤ |((rEll K / 2 : ℕ) : ℤ) - (u2.val : ℤ)| :=
        Int.one_le_abs (sub_ne_zero.mpr hne)
      exact_mod_cast habs_int
    have hhalf_r : (1 / 2 : ℝ) - y = (((rEll K / 2 : ℕ) : ℝ) - (u2.val : ℝ)) / (rEll K : ℝ) := by
      dsimp [y]
      have hr2 : (rEll K : ℝ) = 2 * ((rEll K / 2 : ℕ) : ℝ) := by exact_mod_cast hr_even.symm
      field_simp [hr_pos.ne']
      linarith
    dsimp [ε]
    rw [hhalf_r, abs_div, abs_of_pos hr_pos]
    exact div_le_div_of_nonneg_right hdiff_int hr_pos.le
  have hε_lo : 1 / (2 * (t1Ell K : ℝ)) ≤ ε := by
    refine (one_div_le_one_div_of_le hr_pos ?_).trans hε_r
    exact_mod_cast rEll_le_two_mul_t1Ell K
  set alpha := alphaFromPWork (pWorkEll K p)
  have halpha_pos : 0 < alpha := alphaFromPWork_pos (by omega)
  have hg_pos : ∀ z, 0 < gHat alpha z := gHat_pos alpha halpha_pos
  have hmax_pos : 0 < max (gHat alpha y) (gHat alpha (y - 1)) :=
    lt_max_of_lt_left (hg_pos y)
  have hmin_nonneg : 0 ≤ min (gHat alpha y) (gHat alpha (y - 1)) :=
    le_min (hg_pos y).le (hg_pos (y - 1)).le
  have hratio_le :
      min (gHat alpha y) (gHat alpha (y - 1)) / max (gHat alpha y) (gHat alpha (y - 1)) ≤
        gHat alpha (1 / 2 + ε) / gHat alpha (1 / 2 - ε) := by
    rw [gHat_symm_one]
    rcases le_or_gt y (1 / 2 : ℝ) with hle | hgt
    · have hε_eq : ε = 1 / 2 - y := abs_of_nonneg (by linarith)
      have hy_eq : y = 1 / 2 - ε := by linarith
      have h1y_eq : 1 - y = 1 / 2 + ε := by linarith
      have hnum : min (gHat alpha y) (gHat alpha (1 - y)) ≤ gHat alpha (1 / 2 + ε) := by
        rw [← h1y_eq]; exact min_le_right _ _
      have hden : gHat alpha (1 / 2 - ε) ≤ max (gHat alpha y) (gHat alpha (1 - y)) := by
        rw [← hy_eq]; exact le_max_left _ _
      exact div_le_div₀ (hg_pos _).le hnum (hg_pos _) hden
    · have hε_eq : ε = y - 1 / 2 := by
        dsimp [ε]
        rw [← abs_neg (1 / 2 - y), neg_sub]
        exact abs_of_pos (by linarith)
      have hy_eq : y = 1 / 2 + ε := by linarith
      have h1y_eq : 1 - y = 1 / 2 - ε := by linarith
      have hnum : min (gHat alpha y) (gHat alpha (1 - y)) ≤ gHat alpha (1 / 2 + ε) := by
        rw [← hy_eq]; exact min_le_left _ _
      have hden : gHat alpha (1 / 2 - ε) ≤ max (gHat alpha y) (gHat alpha (1 - y)) := by
        rw [← h1y_eq]; exact le_max_right _ _
      exact div_le_div₀ (hg_pos _).le hnum (hg_pos _) hden
  calc (min (gHat alpha y) (gHat alpha (y - 1)) / max (gHat alpha y) (gHat alpha (y - 1))) ^ (t1Ell K)
      ≤ (gHat alpha (1 / 2 + ε) / gHat alpha (1 / 2 - ε)) ^ (t1Ell K) :=
        pow_le_pow_left₀ (div_nonneg hmin_nonneg hmax_pos.le) hratio_le (t1Ell K)
    _ ≤ (15 / 100 : ℝ) := gHat_half_add_div_gHat_half_sub_pow_le hpWork ht1 hε_lo hε_hi

theorem four_le_m1FromPWorkPChild {pWork pChild : ℕ} (hpW : 8 ≤ pWork) (hpC : 8 ≤ pChild) :
    4 ≤ m1FromPWorkPChild pWork pChild := by
  unfold m1FromPWorkPChild
  have h1 := sqrt_p_log_two_div_pi_ge_five_fourths hpW
  have h2 := sqrt_p_log_two_div_pi_ge_five_fourths hpC
  have hprod : (3 : ℝ) < alphaFromPWork pWork * Real.sqrt (((pChild : ℝ) * Real.log 2) / Real.pi) := by
    unfold alphaFromPWork
    nlinarith
  have hceil : 3 < Nat.ceil (alphaFromPWork pWork * Real.sqrt (((pChild : ℝ) * Real.log 2) / Real.pi)) :=
    Nat.lt_ceil.mpr hprod
  omega

theorem pi_mul_m1_sq_div_alpha_sq_ge {pWork pChild : ℕ} (hpW : 1 ≤ pWork) :
    (pChild : ℝ) * Real.log 2 ≤
      Real.pi * (m1FromPWorkPChild pWork pChild : ℝ) ^ 2 / (alphaFromPWork pWork) ^ 2 := by
  have halpha : 0 < alphaFromPWork pWork := alphaFromPWork_pos hpW
  have halpha2 : 0 < (alphaFromPWork pWork) ^ 2 := sq_pos_of_pos halpha
  have hceil : alphaFromPWork pWork * Real.sqrt (((pChild : ℝ) * Real.log 2) / Real.pi) ≤
      (m1FromPWorkPChild pWork pChild : ℝ) :=
    Nat.le_ceil _
  have hnonneg : 0 ≤ alphaFromPWork pWork * Real.sqrt (((pChild : ℝ) * Real.log 2) / Real.pi) := by
    positivity
  have hsq : (alphaFromPWork pWork) ^ 2 * (((pChild : ℝ) * Real.log 2) / Real.pi) ≤
      (m1FromPWorkPChild pWork pChild : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ hnonneg hceil 2
    have hlog : 0 ≤ ((pChild : ℝ) * Real.log 2) / Real.pi := by
      positivity [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2), Real.pi_pos.le]
    rwa [mul_pow, Real.sq_sqrt hlog] at h
  rw [le_div_iff₀ halpha2]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq' : (alphaFromPWork pWork) ^ 2 * ((pChild : ℝ) * Real.log 2) ≤
      Real.pi * (m1FromPWorkPChild pWork pChild : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hpi.le
    have hpi_ne : Real.pi ≠ 0 := hpi.ne'
    calc (alphaFromPWork pWork) ^ 2 * ((pChild : ℝ) * Real.log 2)
        = Real.pi * ((alphaFromPWork pWork) ^ 2 * (((pChild : ℝ) * Real.log 2) / Real.pi)) := by
          field_simp [hpi_ne]
      _ ≤ Real.pi * (m1FromPWorkPChild pWork pChild : ℝ) ^ 2 := this
  linarith

theorem one_le_pi_mul_m1_div_alpha_sq {pWork pChild : ℕ} (hpW : 1 ≤ pWork) (hpC : pWork ≤ pChild) :
    1 ≤ Real.pi * (m1FromPWorkPChild pWork pChild : ℝ) / (alphaFromPWork pWork) ^ 2 := by
  have halpha : 0 < alphaFromPWork pWork := alphaFromPWork_pos hpW
  have halpha2 : 0 < (alphaFromPWork pWork) ^ 2 := sq_pos_of_pos halpha
  have hceil : alphaFromPWork pWork * Real.sqrt (((pChild : ℝ) * Real.log 2) / Real.pi) ≤
      (m1FromPWorkPChild pWork pChild : ℝ) :=
    Nat.le_ceil _
  have hmono : Real.sqrt (((pWork : ℝ) * Real.log 2) / Real.pi) ≤
      Real.sqrt (((pChild : ℝ) * Real.log 2) / Real.pi) := by
    refine Real.sqrt_le_sqrt ?_
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hpC) hlog) Real.pi_pos.le
  have hm1_ge : (alphaFromPWork pWork) ^ 2 / 2 ≤ (m1FromPWorkPChild pWork pChild : ℝ) := by
    have hhalf : alphaFromPWork pWork * Real.sqrt (((pWork : ℝ) * Real.log 2) / Real.pi) =
        (alphaFromPWork pWork) ^ 2 / 2 := by
      unfold alphaFromPWork
      ring
    linarith [mul_le_mul_of_nonneg_left hmono halpha.le]
  rw [le_div_iff₀ halpha2]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  nlinarith

/-- Two-sided spatial truncation tail sum $\sum_{|d| > M} |g_\alpha(d - \delta)|$ indexed by $n = |d| - (M + 1) \in \mathbb{N}$ (Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`), equation (28) (`eq:spatial-tail`)). -/
noncomputable def spatialTailSum (alpha : ℝ) (M : ℕ) (delta : ℝ) : ℝ :=
  ∑' n : ℕ, (|sincGaussian alpha (((M + 1 + n : ℕ) : ℝ) - delta)| +
    |sincGaussian alpha (-((M + 1 + n : ℕ) : ℝ) - delta)|)

/-- Conditional triangle-inequality bound connecting `concretePoissonResidual` to `spatialTailSum`
and the frequency-domain alias tail `eps_alias`: given any untruncated series sum `untruncatedResp`
whose distance from `filterDiscreteResponse W (filterTap ...)` is at most
`spatialTailSum alpha W (fractionalShift j1)` and whose distance from the finite mode sum over `S`
is at most `eps_alias`, we have
`‖concretePoissonResidual alpha W S j1 u2‖ ≤ spatialTailSum alpha W (fractionalShift j1) + eps_alias`
(Theorem 4.2 (`thm:poisson`), Lemma 6.1 (`lem:filter-norms`)). -/
theorem norm_concretePoissonResidual_le_of_spatial_and_alias (alpha : ℝ) (W : ℕ) {t1 r : ℕ}
    (S : Finset ℤ) (j1 : Fin t1) (u2 : Fin r)
    (untruncatedResp : ℂ) {eps_alias : ℝ}
    (hspatial :
      ‖filterDiscreteResponse W (fun j d => (filterTap alpha W t1 j d : ℂ)) j1 u2 -
        untruncatedResp‖ ≤ spatialTailSum alpha W (fractionalShift j1))
    (halias :
      ‖untruncatedResp -
        ∑ m ∈ S,
          (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
            expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))‖ ≤
        eps_alias) :
    ‖concretePoissonResidual alpha W S j1 u2‖ ≤
      spatialTailSum alpha W (fractionalShift j1) + eps_alias := by
  unfold concretePoissonResidual
  calc ‖filterDiscreteResponse W (fun j d => (filterTap alpha W t1 j d : ℂ)) j1 u2 -
          ∑ m ∈ S,
            (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
              expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))‖
      = ‖(filterDiscreteResponse W (fun j d => (filterTap alpha W t1 j d : ℂ)) j1 u2 -
            untruncatedResp) +
          (untruncatedResp -
            ∑ m ∈ S,
              (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
                expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ)))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖filterDiscreteResponse W (fun j d => (filterTap alpha W t1 j d : ℂ)) j1 u2 -
          untruncatedResp‖ +
        ‖untruncatedResp -
          ∑ m ∈ S,
            (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
              expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))‖ :=
        norm_add_le _ _
    _ ≤ spatialTailSum alpha W (fractionalShift j1) + eps_alias :=
        add_le_add hspatial halias

/-- Per-index bound on the two-sided spatial truncation tail term at $n \in \mathbb{N}$. -/
theorem spatialTailTerm_le {alpha : ℝ} {M p : ℕ} {delta : ℝ}
    (halpha : 0 < alpha) (hM : 1 ≤ M) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hpM : (p : ℝ) * Real.log 2 ≤ Real.pi * (M : ℝ) ^ 2 / alpha ^ 2)
    (hstep : 1 ≤ Real.pi * (M : ℝ) / alpha ^ 2) (n : ℕ) :
    |sincGaussian alpha (((M + 1 + n : ℕ) : ℝ) - delta)| +
      |sincGaussian alpha (-((M + 1 + n : ℕ) : ℝ) - delta)| ≤
      (2 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n := by
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have halpha2 : 0 < alpha ^ 2 := sq_pos_of_pos halpha
  have hbound : ∀ t : ℝ, (M : ℝ) + (n : ℝ) ≤ |t| →
      |sincGaussian alpha t| ≤
        (1 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n := by
    intro t ht
    have htM : (M : ℝ) ≤ |t| := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have ht_pos : 0 < |t| := lt_of_lt_of_le hMpos htM
    have ht_ne : t ≠ 0 := abs_pos.mp ht_pos
    have hinv : 1 / (Real.pi * |t|) ≤ 1 / (Real.pi * (M : ℝ)) :=
      one_div_le_one_div_of_le (mul_pos Real.pi_pos hMpos)
        (mul_le_mul_of_nonneg_left htM Real.pi_pos.le)
    have htsq : (M : ℝ) ^ 2 + (M : ℝ) * (n : ℝ) ≤ t ^ 2 := by
      have h1 : ((M : ℝ) + (n : ℝ)) ^ 2 ≤ |t| ^ 2 :=
        pow_le_pow_left₀ (by positivity) ht 2
      rw [sq_abs] at h1
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hexp_arg : -Real.pi * t ^ 2 / alpha ^ 2 ≤ -(p : ℝ) * Real.log 2 - (n : ℝ) := by
      have hdiv : Real.pi * (M : ℝ) ^ 2 / alpha ^ 2 +
          (Real.pi * (M : ℝ) / alpha ^ 2) * (n : ℝ) ≤ Real.pi * t ^ 2 / alpha ^ 2 := by
        calc Real.pi * (M : ℝ) ^ 2 / alpha ^ 2 + (Real.pi * (M : ℝ) / alpha ^ 2) * (n : ℝ)
            = Real.pi * ((M : ℝ) ^ 2 + (M : ℝ) * (n : ℝ)) / alpha ^ 2 := by ring
          _ ≤ Real.pi * t ^ 2 / alpha ^ 2 := by
            gcongr
      have hn : (n : ℝ) ≤ (Real.pi * (M : ℝ) / alpha ^ 2) * (n : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      linarith [show -Real.pi * t ^ 2 / alpha ^ 2 = -(Real.pi * t ^ 2 / alpha ^ 2) by ring]
    have hexp_le : Real.exp (-Real.pi * t ^ 2 / alpha ^ 2) ≤
        (2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n := by
      calc Real.exp (-Real.pi * t ^ 2 / alpha ^ 2)
          ≤ Real.exp (-(p : ℝ) * Real.log 2 - (n : ℝ)) := Real.exp_le_exp.mpr hexp_arg
        _ = Real.exp (-(p : ℝ) * Real.log 2) * Real.exp (-(n : ℝ)) := by
            rw [sub_eq_add_neg, Real.exp_add]
        _ ≤ (2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n := by
            have hp2 : Real.exp (-(p : ℝ) * Real.log 2) = (2 : ℝ) ^ (-(p : ℤ)) := by
              rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
                zpow_neg, zpow_natCast]
            have hn2 : Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
              have hneg : -(n : ℝ) = (n : ℝ) * (-1 : ℝ) := by ring
              rw [hneg, Real.exp_nat_mul]
              exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le n
            rw [hp2]
            exact mul_le_mul_of_nonneg_left hn2 (by positivity)
    calc |sincGaussian alpha t|
        ≤ (1 / (Real.pi * |t|)) * Real.exp (-Real.pi * t ^ 2 / alpha ^ 2) :=
          abs_sincGaussian_le_inv_pi_mul_exp ht_ne
      _ ≤ (1 / (Real.pi * (M : ℝ))) * ((2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n) :=
          mul_le_mul hinv hexp_le (Real.exp_pos _).le (by positivity)
      _ = (1 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n := by ring
  have hpos_t : (M : ℝ) + (n : ℝ) ≤ |((M + 1 + n : ℕ) : ℝ) - delta| := by
    have h1 : (M : ℝ) + (n : ℝ) ≤ ((M + 1 + n : ℕ) : ℝ) - delta := by
      push_cast; linarith
    exact h1.trans (le_abs_self _)
  have hneg_t : (M : ℝ) + (n : ℝ) ≤ |-((M + 1 + n : ℕ) : ℝ) - delta| := by
    have h1 : (M : ℝ) + (n : ℝ) ≤ ((M + 1 + n : ℕ) : ℝ) + delta := by
      push_cast; linarith
    have h2 : ((M + 1 + n : ℕ) : ℝ) + delta = -(-((M + 1 + n : ℕ) : ℝ) - delta) := by ring
    exact h1.trans (by rw [h2]; exact neg_le_abs _)
  have hb1 := hbound _ hpos_t
  have hb2 := hbound _ hneg_t
  calc |sincGaussian alpha (((M + 1 + n : ℕ) : ℝ) - delta)| +
        |sincGaussian alpha (-((M + 1 + n : ℕ) : ℝ) - delta)|
      ≤ (1 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n +
        (1 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n := add_le_add hb1 hb2
    _ = (2 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 2 : ℝ) ^ n := by ring

/-- Spatial truncation tail bound under general parameter conditions:
$\operatorname{spatialTailSum} \alpha \, M \, \delta < 0.4 \cdot 2^{-p}$ (Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`)). -/
theorem spatialTailSum_lt_of_bounds {alpha : ℝ} {M p : ℕ} {delta : ℝ}
    (halpha : 0 < alpha) (hM : 4 ≤ M) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hpM : (p : ℝ) * Real.log 2 ≤ Real.pi * (M : ℝ) ^ 2 / alpha ^ 2)
    (hstep : 1 ≤ Real.pi * (M : ℝ) / alpha ^ 2) :
    spatialTailSum alpha M delta < (0.4 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  unfold spatialTailSum
  set C := (2 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ))
  have hM1 : 1 ≤ M := by omega
  have hterm : ∀ n : ℕ,
      |sincGaussian alpha (((M + 1 + n : ℕ) : ℝ) - delta)| +
        |sincGaussian alpha (-((M + 1 + n : ℕ) : ℝ) - delta)| ≤
        C * (1 / 2 : ℝ) ^ n :=
    spatialTailTerm_le halpha hM1 hdelta0 hdelta1 hpM hstep
  have hgeom : Summable (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_two).mul_left C
  have hsummable : Summable (fun n : ℕ =>
      |sincGaussian alpha (((M + 1 + n : ℕ) : ℝ) - delta)| +
        |sincGaussian alpha (-((M + 1 + n : ℕ) : ℝ) - delta)|) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hterm hgeom
  have htsum_le :
      (∑' n : ℕ, (|sincGaussian alpha (((M + 1 + n : ℕ) : ℝ) - delta)| +
        |sincGaussian alpha (-((M + 1 + n : ℕ) : ℝ) - delta)|)) ≤
      (4 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc (∑' n : ℕ, (|sincGaussian alpha (((M + 1 + n : ℕ) : ℝ) - delta)| +
            |sincGaussian alpha (-((M + 1 + n : ℕ) : ℝ) - delta)|))
        ≤ ∑' n : ℕ, C * (1 / 2 : ℝ) ^ n :=
          Summable.tsum_le_tsum hterm hsummable hgeom
      _ = C * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := tsum_mul_left
      _ = (4 / (Real.pi * (M : ℝ))) * (2 : ℝ) ^ (-(p : ℤ)) := by
          rw [tsum_geometric_two]
          dsimp [C]
          ring
  refine htsum_le.trans_lt ?_
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hMR : (4 : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hM
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpiM : (12 : ℝ) < Real.pi * (M : ℝ) := by nlinarith
  have hfrac : 4 / (Real.pi * (M : ℝ)) < (0.4 : ℝ) := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  exact mul_lt_mul_of_pos_right hfrac h2pow_pos

/-- **Lemma 6.1(2) (`lem:filter-norms`) Spatial Truncation Tail Bound (`spatial_truncation_tail_le`, Section 6.1 (`sec:filter-norms`), equation (28) (`eq:spatial-tail`), Table 3 (`tab:lean-map`))**:
For $8 \le p_{\text{work}} \le p_{\text{child}}$ and $\delta \in [0, 1]$, the spatial truncation tail beyond
$m_1 = \operatorname{m1FromPWorkPChild} p_{\text{work}} \, p_{\text{child}}$ satisfies
$\sum_{|d| > m_1} |g_\alpha(d - \delta)| < 0.4 \cdot 2^{-p_{\text{child}}}$. -/
theorem spatial_truncation_tail_le {pWork pChild : ℕ} {delta : ℝ}
    (hpW : 8 ≤ pWork) (hpC : pWork ≤ pChild) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    spatialTailSum (alphaFromPWork pWork) (m1FromPWorkPChild pWork pChild) delta <
      (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
  have hpW1 : 1 ≤ pWork := by omega
  have hpC8 : 8 ≤ pChild := le_trans hpW hpC
  exact spatialTailSum_lt_of_bounds
    (alphaFromPWork_pos hpW1)
    (four_le_m1FromPWorkPChild hpW hpC8)
    hdelta0 hdelta1
    (pi_mul_m1_sq_div_alpha_sq_ge hpW1)
    (one_le_pi_mul_m1_div_alpha_sq hpW1 hpC)

/-- Monotone spatial truncation tail bound for any window half-width $M \ge \operatorname{m1FromPWorkPChild} p_{\text{work}} \, p_{\text{child}}$. -/
theorem spatial_truncation_tail_le_of_ge {pWork pChild M : ℕ} {delta : ℝ}
    (hpW : 8 ≤ pWork) (hpC : pWork ≤ pChild)
    (hM : m1FromPWorkPChild pWork pChild ≤ M)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    spatialTailSum (alphaFromPWork pWork) M delta <
      (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
  have hpW1 : 1 ≤ pWork := by omega
  have hpC8 : 8 ≤ pChild := le_trans hpW hpC
  have hM_cast : (m1FromPWorkPChild pWork pChild : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hM
  have hM_sq : (m1FromPWorkPChild pWork pChild : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hM_cast 2
  have halpha_sq : 0 ≤ (alphaFromPWork pWork) ^ 2 := sq_nonneg _
  exact spatialTailSum_lt_of_bounds
    (alphaFromPWork_pos hpW1)
    (le_trans (four_le_m1FromPWorkPChild hpW hpC8) hM)
    hdelta0 hdelta1
    ((pi_mul_m1_sq_div_alpha_sq_ge hpW1).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM_sq Real.pi_pos.le) halpha_sq))
    ((one_le_pi_mul_m1_div_alpha_sq hpW1 hpC).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM_cast Real.pi_pos.le) halpha_sq))

/-- Two-mode ($m \in \{0, 1\}$) Poisson frequency approximation to the discrete filter response
$\hat{f}_{j_1}(u_2)$ (Theorem 4.2 (`thm:poisson`), Theorem 5.1 (`thm:deconv`)):
$\hat{g}_\alpha(u_2/r) e^{2\pi i (u_2/r) j_1 / t_1} + \hat{g}_\alpha(u_2/r - 1) e^{2\pi i (u_2/r - 1) j_1 / t_1}$. -/
noncomputable def twoModeFrequencyApproximation (alpha : ℝ) {t1 r : ℕ}
    (j1 : Fin t1) (u2 : Fin r) : ℂ :=
  ∑ m ∈ ({0, 1} : Finset ℤ),
    (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
      expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))

/-- Explicit two-term expansion of `twoModeFrequencyApproximation`. -/
theorem twoModeFrequencyApproximation_eq (alpha : ℝ) {t1 r : ℕ}
    (j1 : Fin t1) (u2 : Fin r) :
    twoModeFrequencyApproximation alpha j1 u2 =
      (gHat alpha ((u2.val : ℝ) / (r : ℝ)) : ℂ) *
        expTwoPiI ((((u2.val : ℝ) / (r : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ)) +
      (gHat alpha ((u2.val : ℝ) / (r : ℝ) - 1) : ℂ) *
        expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - 1) * (j1.val : ℝ)) / (t1 : ℝ)) := by
  unfold twoModeFrequencyApproximation
  simp

/-- Combined spatial truncation tail and two-mode stopband alias error bound at working precision
`pWork` and child precision `pChild` (Theorem 4.2 (`thm:poisson`), Theorem 5.1(1) (`thm:deconv`), Lemma 6.1 (`lem:filter-norms`)). -/
noncomputable def twoModePoissonResidualBounds (pWork pChild : ℕ) {t1 r : ℕ}
    (j1 : Fin t1) (u2 : Fin r) : ℝ :=
  spatialTailSum (alphaFromPWork pWork) (m1FromPWorkPChild pWork pChild) (fractionalShift j1) +
    (1 - gHat (alphaFromPWork pWork) ((u2.val : ℝ) / (r : ℝ)) -
      gHat (alphaFromPWork pWork) ((u2.val : ℝ) / (r : ℝ) - 1))

/-- **Two-Mode Spatial + Stopband Error Bound (`twoMode_spatial_and_stopband_error_lt`, Theorem 5.1(1) (`thm:deconv`), Lemma 6.1 (`lem:filter-norms`))**:
For all $8 \le p_{\text{work}} \le p_{\text{child}}$, $0 < t_1$, $0 < r$, $j_1 \in \operatorname{Fin} t_1$,
and $u_2 \in \operatorname{Fin} r$, the sum of the spatial truncation tail
`spatialTailSum (alphaFromPWork pWork) (m1FromPWorkPChild pWork pChild) (fractionalShift j1)`
and the stopband alias tail
`1 - gHat (alphaFromPWork pWork) ((u2.val : ℝ) / (r : ℝ)) - gHat (alphaFromPWork pWork) ((u2.val : ℝ) / (r : ℝ) - 1)`
is strictly bounded by $0.4 \cdot 2^{-p_{\text{child}}} + 0.15 \cdot 2^{-p_{\text{work}}}$. -/
theorem twoMode_spatial_and_stopband_error_lt (pWork pChild : ℕ)
    (hpW : 8 ≤ pWork) (hpC : pWork ≤ pChild)
    {t1 r : ℕ} (_ht1 : 0 < t1) (hr : 0 < r) (j1 : Fin t1) (u2 : Fin r) :
    spatialTailSum (alphaFromPWork pWork) (m1FromPWorkPChild pWork pChild) (fractionalShift j1) +
      (1 - gHat (alphaFromPWork pWork) ((u2.val : ℝ) / (r : ℝ)) -
        gHat (alphaFromPWork pWork) ((u2.val : ℝ) / (r : ℝ) - 1)) <
      (4 / 10 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) + (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)) := by
  have hspatial := spatial_truncation_tail_le hpW hpC
    (fractionalShift_nonneg j1) (fractionalShift_le_one j1)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy0 : 0 ≤ (u2.val : ℝ) / (r : ℝ) := div_nonneg (Nat.cast_nonneg _) hr_pos.le
  have hy1 : (u2.val : ℝ) / (r : ℝ) ≤ 1 :=
    div_le_one_of_le₀ (Nat.cast_le.mpr u2.isLt.le) hr_pos.le
  have halias := gHat_stopband_alias_lt pWork hpW ((u2.val : ℝ) / (r : ℝ)) hy0 hy1
  linarith

/-- `twoModePoissonResidualBounds` is strictly bounded by $0.4 \cdot 2^{-p_{\text{child}}} + 0.15 \cdot 2^{-p_{\text{work}}}$. -/
theorem twoModePoissonResidualBounds_lt (pWork pChild : ℕ)
    (hpW : 8 ≤ pWork) (hpC : pWork ≤ pChild)
    {t1 r : ℕ} (ht1 : 0 < t1) (hr : 0 < r) (j1 : Fin t1) (u2 : Fin r) :
    twoModePoissonResidualBounds pWork pChild j1 u2 <
      (4 / 10 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) + (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)) :=
  twoMode_spatial_and_stopband_error_lt pWork pChild hpW hpC ht1 hr j1 u2

/-! ### Harmonic Sum and Filter $\ell_1$-Norm Bounds (Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`), Appendix C.2 (`app:filter-norms-proof`)) -/

/-- Logarithmic step bound $\frac{1}{m} \le \ln m - \ln(m - 1)$ for $m \ge 2$. -/
theorem inv_nat_le_log_sub_log {m : ℕ} (hm : 2 ≤ m) :
    1 / (m : ℝ) ≤ Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) := by
  have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hdiv : ((m - 1 : ℕ) : ℝ) / (m : ℝ) = 1 - 1 / (m : ℝ) := by
    rw [hcast, sub_div, div_self hm_pos.ne']
  have hlog := Real.log_le_sub_one_of_pos (div_pos hm1_pos hm_pos)
  rw [Real.log_div hm1_pos.ne' hm_pos.ne', hdiv] at hlog
  linarith

/-- Harmonic sum bound $\sum_{m=2}^W \frac{1}{m} \le \ln W$ for $W \ge 1$. -/
theorem harmonic_sum_Icc_two_le_log {W : ℕ} (hW : 1 ≤ W) :
    ∑ m ∈ Finset.Icc 2 W, (1 / (m : ℝ)) ≤ Real.log (W : ℝ) := by
  induction W, hW using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1)]
    have hstep := inv_nat_le_log_sub_log (by omega : 2 ≤ k + 1)
    simp only [Nat.add_sub_cancel] at hstep
    linarith

/-- Harmonic sum bound $\sum_{m=1}^W \frac{1}{m} \le 1 + \ln W$ for $W \ge 1$. -/
theorem harmonic_sum_Icc_one_le_one_add_log {W : ℕ} (hW : 1 ≤ W) :
    ∑ m ∈ Finset.Icc 1 W, (1 / (m : ℝ)) ≤ 1 + Real.log (W : ℝ) := by
  have hsplit : Finset.Icc 1 W = insert 1 (Finset.Icc 2 W) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h2 := harmonic_sum_Icc_two_le_log hW
  norm_num at *
  linarith

/-- Exact pairing identity for integer intervals `Finset.Icc (-(W : ℤ)) ((W : ℤ) + 1)`. -/
theorem sum_Icc_neg_to_pos_succ (W : ℕ) (F : ℤ → ℝ) :
    ∑ d ∈ Finset.Icc (-(W : ℤ)) ((W : ℤ) + 1), F d =
      (F 0 + F 1) + ∑ m ∈ Finset.Icc 1 W, (F (-(m : ℤ)) + F ((m : ℤ) + 1)) := by
  induction W with
  | zero =>
    have hIcc : Finset.Icc (0 : ℤ) 1 = insert 0 {1} := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    simp [hIcc]
  | succ k ih =>
    have hIcc : Finset.Icc (-((k + 1 : ℕ) : ℤ)) (((k + 1 : ℕ) : ℤ) + 1) =
        insert (-((k + 1 : ℕ) : ℤ))
          (insert (((k + 1 : ℕ) : ℤ) + 1) (Finset.Icc (-(k : ℤ)) ((k : ℤ) + 1))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot1 : (-((k + 1 : ℕ) : ℤ)) ∉
        insert (((k + 1 : ℕ) : ℤ) + 1) (Finset.Icc (-(k : ℤ)) ((k : ℤ) + 1)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot2 : (((k + 1 : ℕ) : ℤ) + 1) ∉ Finset.Icc (-(k : ℤ)) ((k : ℤ) + 1) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnot1, Finset.sum_insert hnot2, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    ring

/-- Pairing upper bound on `Finset.Icc (-(W : ℤ)) (W : ℤ)` for non-negative `F : ℤ → ℝ`. -/
theorem sum_Icc_neg_to_pos_le_pair (W : ℕ) (F : ℤ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), F d ≤
      (F 0 + F 1) + ∑ m ∈ Finset.Icc 1 W, (F (-(m : ℤ)) + F ((m : ℤ) + 1)) := by
  rw [← sum_Icc_neg_to_pos_succ W F]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hF d)
  intro d hd
  simp only [Finset.mem_Icc] at hd ⊢
  omega

/-- Central pair bound: for $\delta \in [0, 1]$, $|\operatorname{sinc}(\delta)| + |\operatorname{sinc}(1 - \delta)| \le \frac{3}{2}$. -/
theorem abs_sinc_add_abs_sinc_one_sub_le {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    |sinc delta| + |sinc (1 - delta)| ≤ 3 / 2 := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  rcases le_or_gt delta (1 / 3 : ℝ) with hleft | hmid
  · have hs1 : |sinc delta| ≤ 1 := abs_sinc_le_one delta
    have h1d_pos : 0 < 1 - delta := by linarith
    have h1d_abs : |1 - delta| = 1 - delta := abs_of_pos h1d_pos
    have hs2 : |sinc (1 - delta)| ≤ 1 / 2 := by
      rw [sinc_of_ne_zero h1d_pos.ne', abs_div, abs_mul, abs_of_pos Real.pi_pos, h1d_abs]
      have hsin_eq : Real.sin (Real.pi * (1 - delta)) = Real.sin (Real.pi * delta) := by
        have : Real.pi * (1 - delta) = Real.pi - Real.pi * delta := by ring
        rw [this, Real.sin_pi_sub]
      rw [hsin_eq]
      have hsin_le : |Real.sin (Real.pi * delta)| ≤ Real.pi * delta := by
        refine Real.abs_sin_le_abs.trans ?_
        rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · rcases le_or_gt (2 / 3 : ℝ) delta with hright | hmid2
    · have hs2 : |sinc (1 - delta)| ≤ 1 := abs_sinc_le_one (1 - delta)
      have hd_pos : 0 < delta := by linarith
      have hd_abs : |delta| = delta := abs_of_pos hd_pos
      have hs1 : |sinc delta| ≤ 1 / 2 := by
        rw [sinc_of_ne_zero hd_pos.ne', abs_div, abs_mul, abs_of_pos Real.pi_pos, hd_abs]
        have hsin_eq : Real.sin (Real.pi * delta) = Real.sin (Real.pi * (1 - delta)) := by
          have : Real.pi * delta = Real.pi - Real.pi * (1 - delta) := by ring
          rw [this, Real.sin_pi_sub]
        rw [hsin_eq]
        have h1d_nonneg : 0 ≤ Real.pi * (1 - delta) := by nlinarith
        have hsin_le : |Real.sin (Real.pi * (1 - delta))| ≤ Real.pi * (1 - delta) := by
          refine Real.abs_sin_le_abs.trans ?_
          rw [abs_of_nonneg h1d_nonneg]
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · have hd_pos : 0 < delta := by linarith
      have h1d_pos : 0 < 1 - delta := by linarith
      have hd_abs : |delta| = delta := abs_of_pos hd_pos
      have h1d_abs : |1 - delta| = 1 - delta := abs_of_pos h1d_pos
      have hs1 := abs_sinc_le_inv_pi_mul_abs hd_pos.ne'
      have hs2 := abs_sinc_le_inv_pi_mul_abs h1d_pos.ne'
      rw [hd_abs] at hs1
      rw [h1d_abs] at hs2
      have hsum : 1 / (Real.pi * delta) + 1 / (Real.pi * (1 - delta)) ≤ 3 / 2 := by
        have hprod : (2 / 9 : ℝ) ≤ delta * (1 - delta) := by nlinarith
        have hcomb : 1 / (Real.pi * delta) + 1 / (Real.pi * (1 - delta)) =
            1 / (Real.pi * (delta * (1 - delta))) := by
          have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
          field_simp [hpi_ne, hd_pos.ne', h1d_pos.ne']
          ring
        rw [hcomb, div_le_iff₀ (by positivity)]
        nlinarith
      linarith

/-- Pairwise decay bound for $d = -m$ and $d = m + 1$ ($m \ge 1$, $\delta \in [0, 1]$). -/
theorem abs_sincGaussian_pair_le (alpha : ℝ) {m : ℕ} (hm : 1 ≤ m)
    {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    |sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
      |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)| ≤
      (1 / Real.pi) * (1 / (m : ℝ) + 1 / ((m : ℝ) + 1)) *
        Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd1 : 0 < (m : ℝ) + delta := by linarith
  have hd2 : 0 < (m : ℝ) + 1 - delta := by linarith
  have hd3 : 0 < (m : ℝ) + 1 := by linarith
  have ht1_abs : |((-(m : ℤ) : ℤ) : ℝ) - delta| = (m : ℝ) + delta := by
    have : ((-(m : ℤ) : ℤ) : ℝ) - delta = -((m : ℝ) + delta) := by push_cast; ring
    rw [this, abs_neg, abs_of_pos hd1]
  have ht2_abs : |(((m : ℤ) + 1 : ℤ) : ℝ) - delta| = (m : ℝ) + 1 - delta := by
    have : (((m : ℤ) + 1 : ℤ) : ℝ) - delta = (m : ℝ) + 1 - delta := by push_cast; ring
    rw [this, abs_of_pos hd2]
  have ht1_ne : ((-(m : ℤ) : ℤ) : ℝ) - delta ≠ 0 := by
    intro h; rw [h, abs_zero] at ht1_abs; linarith
  have ht2_ne : (((m : ℤ) + 1 : ℤ) : ℝ) - delta ≠ 0 := by
    intro h; rw [h, abs_zero] at ht2_abs; linarith
  have hb1 := abs_sincGaussian_le_inv_pi_mul_exp (alpha := alpha) ht1_ne
  have hb2 := abs_sincGaussian_le_inv_pi_mul_exp (alpha := alpha) ht2_ne
  rw [ht1_abs] at hb1
  rw [ht2_abs] at hb2
  have hexp1 : Real.exp (-Real.pi * (((-(m : ℤ) : ℤ) : ℝ) - delta) ^ 2 / alpha ^ 2) ≤
      Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) := by
    rw [Real.exp_le_exp]
    have hsq : (m : ℝ) ^ 2 ≤ (((-(m : ℤ) : ℤ) : ℝ) - delta) ^ 2 := by
      rw [← sq_abs (((-(m : ℤ) : ℤ) : ℝ) - delta), ht1_abs]
      nlinarith
    have hnum : -Real.pi * (((-(m : ℤ) : ℤ) : ℝ) - delta) ^ 2 ≤ -Real.pi * (m : ℝ) ^ 2 := by
      nlinarith [Real.pi_pos]
    exact div_le_div_of_nonneg_right hnum (sq_nonneg alpha)
  have hexp2 : Real.exp (-Real.pi * ((((m : ℤ) + 1 : ℤ) : ℝ) - delta) ^ 2 / alpha ^ 2) ≤
      Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) := by
    rw [Real.exp_le_exp]
    have hsq : (m : ℝ) ^ 2 ≤ ((((m : ℤ) + 1 : ℤ) : ℝ) - delta) ^ 2 := by
      rw [← sq_abs ((((m : ℤ) + 1 : ℤ) : ℝ) - delta), ht2_abs]
      nlinarith
    have hnum : -Real.pi * ((((m : ℤ) + 1 : ℤ) : ℝ) - delta) ^ 2 ≤ -Real.pi * (m : ℝ) ^ 2 := by
      nlinarith [Real.pi_pos]
    exact div_le_div_of_nonneg_right hnum (sq_nonneg alpha)
  have h1' : |sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| ≤
      (1 / (Real.pi * ((m : ℝ) + delta))) * Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) :=
    hb1.trans (mul_le_mul_of_nonneg_left hexp1 (by positivity))
  have h2' : |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)| ≤
      (1 / (Real.pi * ((m : ℝ) + 1 - delta))) * Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) :=
    hb2.trans (mul_le_mul_of_nonneg_left hexp2 (by positivity))
  have hfrac : 1 / (Real.pi * ((m : ℝ) + delta)) + 1 / (Real.pi * ((m : ℝ) + 1 - delta)) ≤
      (1 / Real.pi) * (1 / (m : ℝ) + 1 / ((m : ℝ) + 1)) := by
    have hdenom : (m : ℝ) * ((m : ℝ) + 1) ≤ ((m : ℝ) + delta) * ((m : ℝ) + 1 - delta) := by
      nlinarith
    have hsum_eq1 : 1 / ((m : ℝ) + delta) + 1 / ((m : ℝ) + 1 - delta) =
        (2 * (m : ℝ) + 1) / (((m : ℝ) + delta) * ((m : ℝ) + 1 - delta)) := by
      field_simp [hd1.ne', hd2.ne']; ring
    have hsum_eq2 : 1 / (m : ℝ) + 1 / ((m : ℝ) + 1) =
        (2 * (m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 1)) := by
      field_simp [hm_pos.ne', hd3.ne']; ring
    have hdiv_le : (2 * (m : ℝ) + 1) / (((m : ℝ) + delta) * ((m : ℝ) + 1 - delta)) ≤
        (2 * (m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
    have hfactor : 1 / (Real.pi * ((m : ℝ) + delta)) + 1 / (Real.pi * ((m : ℝ) + 1 - delta)) =
        (1 / Real.pi) * (1 / ((m : ℝ) + delta) + 1 / ((m : ℝ) + 1 - delta)) := by
      simp only [one_div, mul_inv_rev]
      ring
    rw [hfactor, hsum_eq1, hsum_eq2]
    exact mul_le_mul_of_nonneg_left hdiv_le (by positivity)
  calc |sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|
      ≤ (1 / (Real.pi * ((m : ℝ) + delta)) + 1 / (Real.pi * ((m : ℝ) + 1 - delta))) *
          Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) := by linarith
    _ ≤ (1 / Real.pi) * (1 / (m : ℝ) + 1 / ((m : ℝ) + 1)) *
          Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) :=
        mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le

/-- Filter $\ell_1$-norm harmonic upper bound:
$\sum_{d = -W}^{W} |g_\alpha(d - \delta)| \le \frac{3}{2} + \frac{2}{\pi} \sum_{m=1}^{W} \frac{1}{m} \le 2 + \frac{2}{\pi} \sum_{m=1}^{W} \frac{1}{m}$ (Lemma 6.1 (`lem:filter-norms`), Appendix C.2 (`app:filter-norms-proof`)). -/
theorem filter_l1_norm_le_harmonic (alpha : ℝ) (W : ℕ) {delta : ℝ}
    (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), |sincGaussian alpha ((d : ℝ) - delta)| ≤
      (3 / 2 : ℝ) + (2 / Real.pi) * ∑ m ∈ Finset.Icc 1 W, (1 / (m : ℝ)) := by
  refine (sum_Icc_neg_to_pos_le_pair W (fun d => |sincGaussian alpha ((d : ℝ) - delta)|)
    (fun _ => abs_nonneg _)).trans ?_
  have hc0 : |sincGaussian alpha (((0 : ℤ) : ℝ) - delta)| ≤ |sinc delta| := by
    have : ((0 : ℤ) : ℝ) - delta = -delta := by push_cast; ring
    rw [this, sincGaussian_even]
    exact abs_sincGaussian_le_abs_sinc alpha delta
  have hc1 : |sincGaussian alpha (((1 : ℤ) : ℝ) - delta)| ≤ |sinc (1 - delta)| := by
    have : ((1 : ℤ) : ℝ) - delta = 1 - delta := by push_cast; ring
    rw [this]
    exact abs_sincGaussian_le_abs_sinc alpha (1 - delta)
  have hcentral : |sincGaussian alpha (((0 : ℤ) : ℝ) - delta)| +
      |sincGaussian alpha (((1 : ℤ) : ℝ) - delta)| ≤ 3 / 2 :=
    (add_le_add hc0 hc1).trans (abs_sinc_add_abs_sinc_one_sub_le h0 h1)
  have hsum : ∑ m ∈ Finset.Icc 1 W,
      (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) ≤
      ∑ m ∈ Finset.Icc 1 W, (2 / Real.pi) * (1 / (m : ℝ)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hpair := abs_sincGaussian_pair_le alpha hm1 h0 h1
    have hexp : Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg
        (by nlinarith [Real.pi_pos, sq_nonneg (m : ℝ)]) (sq_nonneg alpha)
    have h1m : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) :=
      one_div_le_one_div_of_le hm_pos (by linarith)
    have hcoeff : (1 / Real.pi) * (1 / (m : ℝ) + 1 / ((m : ℝ) + 1)) ≤
        (2 / Real.pi) * (1 / (m : ℝ)) := by
      have : (2 / Real.pi) * (1 / (m : ℝ)) =
          (1 / Real.pi) * (1 / (m : ℝ) + 1 / (m : ℝ)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact hpair.trans ((mul_le_of_le_one_right (by positivity) hexp).trans hcoeff)
  rw [← Finset.mul_sum] at hsum
  linarith

/-- Filter $\ell_1$-norm logarithmic upper bound in terms of $W \ge 1$:
$\sum_{d = -W}^{W} |g_\alpha(d - \delta)| \le \frac{2}{\pi} \ln W + 2.4$ (Lemma 6.1 (`lem:filter-norms`)). -/
theorem filter_l1_norm_le_log_W (alpha : ℝ) {W : ℕ} (hW : 1 ≤ W) {delta : ℝ}
    (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), |sincGaussian alpha ((d : ℝ) - delta)| ≤
      (2 / Real.pi) * Real.log (W : ℝ) + 12 / 5 := by
  have hharm := filter_l1_norm_le_harmonic alpha W h0 h1
  have hlog := harmonic_sum_Icc_one_le_one_add_log hW
  have hmul : (2 / Real.pi) * ∑ m ∈ Finset.Icc 1 W, (1 / (m : ℝ)) ≤
      (2 / Real.pi) * (1 + Real.log (W : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have htwo_pi : 2 / Real.pi ≤ 2 / 3 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith
  linarith

/-- Quadratic upper bound $\sin(\pi \delta) \le \frac{1}{2} + 2\delta(1 - \delta)$ for $\delta \in [0, 1]$. -/
theorem sin_pi_mul_le_half_add_two_mul {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    Real.sin (Real.pi * delta) ≤ 1 / 2 + 2 * delta * (1 - delta) := by
  have hcos : Real.sin (Real.pi * delta) = Real.cos (Real.pi * (1 / 2 - delta)) := by
    have : Real.pi * (1 / 2 - delta) = Real.pi / 2 - Real.pi * delta := by ring
    rw [this, Real.cos_pi_div_two_sub]
  have habs : |Real.pi * (1 / 2 - delta)| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have : |1 / 2 - delta| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [Real.pi_pos]
  have hbound := Real.cos_le_one_sub_mul_cos_sq habs
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hrhs : 1 - 2 / Real.pi ^ 2 * (Real.pi * (1 / 2 - delta)) ^ 2 =
      1 / 2 + 2 * delta * (1 - delta) := by
    field_simp [hpi_ne]
    ring
  linarith

/-- Absolute value of $\sin(\pi(1 + \delta))$ equals $|\sin(\pi\delta)|$. -/
theorem abs_sin_pi_one_add (delta : ℝ) :
    |Real.sin (Real.pi * (1 + delta))| = |Real.sin (Real.pi * delta)| := by
  have h : Real.pi * (1 + delta) = Real.pi - (-Real.pi * delta) := by ring
  rw [h, Real.sin_pi_sub, neg_mul, Real.sin_neg, abs_neg]

/-- Absolute value of $\sin(\pi(2 - \delta))$ equals $|\sin(\pi\delta)|$. -/
theorem abs_sin_pi_two_sub (delta : ℝ) :
    |Real.sin (Real.pi * (2 - delta))| = |Real.sin (Real.pi * delta)| := by
  have h1 : Real.pi * (2 - delta) = Real.pi - (-Real.pi * (1 - delta)) := by ring
  have h2 : Real.pi * (1 - delta) = Real.pi - Real.pi * delta := by ring
  rw [h1, Real.sin_pi_sub, neg_mul, Real.sin_neg, abs_neg, h2, Real.sin_pi_sub]

/-- Four-tap central sinc sum bound on $[0, 2/7]$. -/
theorem abs_sinc_four_central_le_of_le_two_sevenths {delta : ℝ}
    (h0 : 0 ≤ delta) (h27 : delta ≤ 2 / 7) :
    |sinc delta| + |sinc (1 - delta)| + |sinc (1 + delta)| + |sinc (2 - delta)| ≤ 161 / 90 := by
  have hs0 : |sinc delta| ≤ 1 := abs_sinc_le_one delta
  have hsin_le : |Real.sin (Real.pi * delta)| ≤ Real.pi * delta := by
    refine Real.abs_sin_le_abs.trans ?_
    rw [abs_of_nonneg (by positivity)]
  have hs1 : |sinc (1 - delta)| ≤ 2 / 5 := by
    have hd_pos : 0 < 1 - delta := by linarith
    have hd_abs : |1 - delta| = 1 - delta := abs_of_pos hd_pos
    rw [sinc_of_ne_zero hd_pos.ne', abs_div, abs_mul, abs_of_pos Real.pi_pos, hd_abs]
    have hsin_eq : Real.sin (Real.pi * (1 - delta)) = Real.sin (Real.pi * delta) := by
      have : Real.pi * (1 - delta) = Real.pi - Real.pi * delta := by ring
      rw [this, Real.sin_pi_sub]
    rw [hsin_eq, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hs2 : |sinc (1 + delta)| ≤ 2 / 9 := by
    have hd_pos : 0 < 1 + delta := by linarith
    have hd_abs : |1 + delta| = 1 + delta := abs_of_pos hd_pos
    rw [sinc_of_ne_zero hd_pos.ne', abs_div, abs_mul, abs_of_pos Real.pi_pos, hd_abs,
      abs_sin_pi_one_add, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hs3 : |sinc (2 - delta)| ≤ 1 / 6 := by
    have hd_pos : 0 < 2 - delta := by linarith
    have hd_abs : |2 - delta| = 2 - delta := abs_of_pos hd_pos
    rw [sinc_of_ne_zero hd_pos.ne', abs_div, abs_mul, abs_of_pos Real.pi_pos, hd_abs,
      abs_sin_pi_two_sub, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  linarith

/-- Four-tap central sinc sum bound on $[0, 1]$:
$|\operatorname{sinc}(\delta)| + |\operatorname{sinc}(1 - \delta)| + |\operatorname{sinc}(1 + \delta)| + |\operatorname{sinc}(2 - \delta)| \le \frac{453}{250} = 1.812$. -/
theorem abs_sinc_four_central_le {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    |sinc delta| + |sinc (1 - delta)| + |sinc (1 + delta)| + |sinc (2 - delta)| ≤ 453 / 250 := by
  rcases le_or_gt delta (2 / 7 : ℝ) with hleft | hmid
  · linarith [abs_sinc_four_central_le_of_le_two_sevenths h0 hleft]
  · rcases le_or_gt (5 / 7 : ℝ) delta with hright | hmid2
    · have hsym := abs_sinc_four_central_le_of_le_two_sevenths (delta := 1 - delta)
        (by linarith) (by linarith)
      have he1 : 1 - (1 - delta) = delta := by ring
      have he2 : 1 + (1 - delta) = 2 - delta := by ring
      have he3 : 2 - (1 - delta) = 1 + delta := by ring
      rw [he1, he2, he3] at hsym
      linarith
    · have hd0 : 0 < delta := by linarith
      have hd1 : 0 < 1 - delta := by linarith
      have hd2 : 0 < 1 + delta := by linarith
      have hd3 : 0 < 2 - delta := by linarith
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
      rw [sinc_of_ne_zero hd0.ne', sinc_of_ne_zero hd1.ne',
        sinc_of_ne_zero hd2.ne', sinc_of_ne_zero hd3.ne']
      simp only [abs_div, abs_mul, abs_of_pos hpi_pos, abs_of_pos hd0,
        abs_of_pos hd1, abs_of_pos hd2, abs_of_pos hd3,
        abs_sin_pi_one_add, abs_sin_pi_two_sub]
      have hsin1 : |Real.sin (Real.pi * (1 - delta))| = |Real.sin (Real.pi * delta)| := by
        have : Real.pi * (1 - delta) = Real.pi - Real.pi * delta := by ring
        rw [this, Real.sin_pi_sub]
      rw [hsin1]
      have hsin_nonneg : 0 ≤ Real.sin (Real.pi * delta) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
      rw [abs_of_nonneg hsin_nonneg]
      let w : ℝ := delta * (1 - delta)
      have hw_lo : 10 / 49 ≤ w := by dsimp [w]; nlinarith
      have hw_hi : w ≤ 1 / 4 := by dsimp [w]; nlinarith [sq_nonneg (delta - 1 / 2)]
      have hw_pos : 0 < w := by linarith
      have h2w_pos : 0 < 2 + w := by linarith
      have hsin_bound : Real.sin (Real.pi * delta) ≤ 1 / 2 + 2 * w := by
        dsimp [w]
        linarith [sin_pi_mul_le_half_add_two_mul h0 h1]
      have hsum_eq :
          Real.sin (Real.pi * delta) / (Real.pi * delta) +
          Real.sin (Real.pi * delta) / (Real.pi * (1 - delta)) +
          Real.sin (Real.pi * delta) / (Real.pi * (1 + delta)) +
          Real.sin (Real.pi * delta) / (Real.pi * (2 - delta)) =
          Real.sin (Real.pi * delta) * ((2 + 4 * w) / (Real.pi * w * (2 + w))) := by
        dsimp [w]
        field_simp [hpi_ne, hd0.ne', hd1.ne', hd2.ne', hd3.ne']
        ring
      rw [hsum_eq]
      have hprod_le :
          Real.sin (Real.pi * delta) * ((2 + 4 * w) / (Real.pi * w * (2 + w))) ≤
          ((1 / 2 + 2 * w) * (2 + 4 * w)) / (Real.pi * w * (2 + w)) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsin_bound (by positivity)) (by positivity)
      refine hprod_le.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have hquad : (1 / 2 + 2 * w) * (2 + 4 * w) ≤ (683 / 120 : ℝ) * (w * (2 + w)) := by
        nlinarith
      have hvw_pos : 0 < w * (2 + w) := mul_pos hw_pos h2w_pos
      have hpi_w : (683 / 120 : ℝ) * (w * (2 + w)) ≤ (453 / 250 : ℝ) * (Real.pi * w * (2 + w)) := by
        have h1 : (683 / 120 : ℝ) ≤ (453 / 250 : ℝ) * Real.pi := by
          nlinarith [Real.pi_gt_d4]
        calc (683 / 120 : ℝ) * (w * (2 + w))
            ≤ ((453 / 250 : ℝ) * Real.pi) * (w * (2 + w)) :=
              mul_le_mul_of_nonneg_right h1 hvw_pos.le
          _ = (453 / 250 : ℝ) * (Real.pi * w * (2 + w)) := by ring
      linarith

/-- Exact telescoping identity for $\sum_{m=2}^{N-1} (\frac{1}{m} + \frac{1}{m+1}) + \frac{1}{N}$. -/
theorem sum_Icc_two_pred_pair_add_inv {N : ℕ} (hN : 2 ≤ N) :
    (∑ m ∈ Finset.Icc 2 (N - 1), (1 / (m : ℝ) + 1 / ((m : ℝ) + 1))) + 1 / (N : ℝ) =
      (1 / 2 : ℝ) + 2 * ∑ m ∈ Finset.Icc 3 N, (1 / (m : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    simp only [Nat.add_sub_cancel]
    have hIcc : Finset.Icc 2 k = insert k (Finset.Icc 2 (k - 1)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k ∉ Finset.Icc 2 (k - 1) := by
      simp only [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert hnot, Finset.sum_Icc_succ_top (by omega : 3 ≤ k + 1)]
    push_cast
    linarith

/-- Harmonic sum bound $\sum_{m=3}^N \frac{1}{m} \le \ln N - \ln 2$ for $N \ge 2$. -/
theorem harmonic_sum_Icc_three_le_log_sub_log_two {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ Finset.Icc 3 N, (1 / (m : ℝ)) ≤ Real.log (N : ℝ) - Real.log 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ k + 1)]
    have hstep := inv_nat_le_log_sub_log (by omega : 2 ≤ k + 1)
    simp only [Nat.add_sub_cancel] at hstep
    linarith

/-- Telescoping bound $\sum_{m=N+1}^W (\frac{1}{m-1} - \frac{1}{m}) \le \frac{1}{N}$ for $N \ge 1$. -/
theorem sum_Icc_inv_sub_inv_le {N : ℕ} (hN : 1 ≤ N) (W : ℕ) :
    ∑ m ∈ Finset.Icc (N + 1) W, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) ≤ 1 / (N : ℝ) := by
  rcases lt_or_ge W N with hlt | hge
  · have hemp : Finset.Icc (N + 1) W = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    positivity
  · suffices h_eq : ∑ m ∈ Finset.Icc (N + 1) W, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) =
        1 / (N : ℝ) - 1 / (W : ℝ) by
      rw [h_eq]
      have : (0 : ℝ) ≤ 1 / (W : ℝ) := by positivity
      linarith
    induction W, hge using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (by omega : N + 1 ≤ k + 1), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- Linear lower bound $4x \le e^x$ for $x \ge 3$. -/
theorem four_mul_le_exp_of_three_le {x : ℝ} (hx : 3 ≤ x) :
    4 * x ≤ Real.exp x := by
  have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he2 : (7.38 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
  have hx2 : x - 1 ≤ Real.exp (x - 2) := by
    have h := Real.add_one_le_exp (x - 2)
    linarith
  have hexp : Real.exp x = (Real.exp 1 * Real.exp 1) * Real.exp (x - 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith

/-- Middle-range pair sum bound for $2 \le m \le N$ where $2 \le N \le \alpha < N + 1$. -/
theorem filter_l1_middle_sum_le {alpha : ℝ} {N : ℕ} (hN2 : 2 ≤ N)
    (hN_le_alpha : (N : ℝ) ≤ alpha) (halpha_lt_N1 : alpha < (N : ℝ) + 1)
    {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    ∑ m ∈ Finset.Icc 2 N,
      (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) ≤
      (2 / Real.pi) * Real.log alpha + (1 / 2 - 2 * Real.log 2) / Real.pi := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have halpha_pos : 0 < alpha := lt_of_lt_of_le hN_pos hN_le_alpha
  have hIcc_N : Finset.Icc 2 N = insert N (Finset.Icc 2 (N - 1)) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot_mem : N ∉ Finset.Icc 2 (N - 1) := by
    simp only [Finset.mem_Icc]; omega
  rw [hIcc_N, Finset.sum_insert hnot_mem]
  have hPN : |sincGaussian alpha (((-(N : ℤ) : ℤ) : ℝ) - delta)| +
      |sincGaussian alpha ((((N : ℤ) + 1 : ℤ) : ℝ) - delta)| ≤
      (1 / Real.pi) * (1 / (N : ℝ)) := by
    have hp := abs_sincGaussian_pair_le alpha (by omega : 1 ≤ N) h0 h1
    have hexpN : Real.exp (-Real.pi * (N : ℝ) ^ 2 / alpha ^ 2) ≤ 1 / 2 := by
      have hratio : 1 ≤ Real.pi * (N : ℝ) ^ 2 / alpha ^ 2 := by
        rw [one_le_div (by positivity)]
        have h32 : alpha ≤ (3 / 2 : ℝ) * (N : ℝ) := by
          have : (2 : ℝ) ≤ (N : ℝ) := Nat.ofNat_le_cast.mpr hN2
          linarith
        have hsq : alpha ^ 2 ≤ (9 / 4 : ℝ) * (N : ℝ) ^ 2 := by nlinarith
        have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
        nlinarith
      have hexp_le : Real.exp (-Real.pi * (N : ℝ) ^ 2 / alpha ^ 2) ≤ Real.exp (-1) := by
        rw [Real.exp_le_exp]
        linarith [show -Real.pi * (N : ℝ) ^ 2 / alpha ^ 2 = -(Real.pi * (N : ℝ) ^ 2 / alpha ^ 2) by ring]
      exact hexp_le.trans Real.exp_neg_one_lt_half.le
    have h1N : 1 / ((N : ℝ) + 1) ≤ 1 / (N : ℝ) :=
      one_div_le_one_div_of_le hN_pos (by linarith)
    have hcomb : (1 / Real.pi) * (1 / (N : ℝ) + 1 / ((N : ℝ) + 1)) * (1 / 2) ≤
        (1 / Real.pi) * (1 / (N : ℝ)) := by
      have : (1 / Real.pi) * (1 / (N : ℝ)) =
          (1 / Real.pi) * (1 / (N : ℝ) + 1 / (N : ℝ)) * (1 / 2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by norm_num)
    exact hp.trans ((mul_le_mul_of_nonneg_left hexpN (by positivity)).trans hcomb)
  have hP_prev : ∑ m ∈ Finset.Icc 2 (N - 1),
      (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) ≤
      (1 / Real.pi) * ∑ m ∈ Finset.Icc 2 (N - 1), (1 / (m : ℝ) + 1 / ((m : ℝ) + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
    have hp := abs_sincGaussian_pair_le alpha hm1 h0 h1
    have hexp : Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg
        (by nlinarith [Real.pi_pos, sq_nonneg (m : ℝ)]) (sq_nonneg alpha)
    exact hp.trans (mul_le_of_le_one_right (by positivity) hexp)
  have htel := sum_Icc_two_pred_pair_add_inv hN2
  have hharm3 := harmonic_sum_Icc_three_le_log_sub_log_two hN2
  have hlog_mono : Real.log (N : ℝ) ≤ Real.log alpha :=
    Real.log_le_log hN_pos hN_le_alpha
  have hsum_mid : (∑ m ∈ Finset.Icc 2 (N - 1), (1 / (m : ℝ) + 1 / ((m : ℝ) + 1))) + 1 / (N : ℝ) ≤
      1 / 2 + 2 * (Real.log alpha - Real.log 2) := by
    linarith
  have hmul_mid : (1 / Real.pi) *
      ((∑ m ∈ Finset.Icc 2 (N - 1), (1 / (m : ℝ) + 1 / ((m : ℝ) + 1))) + 1 / (N : ℝ)) ≤
      (1 / Real.pi) * (1 / 2 + 2 * (Real.log alpha - Real.log 2)) :=
    mul_le_mul_of_nonneg_left hsum_mid (by positivity)
  linarith [show (1 / Real.pi) * (1 / (N : ℝ)) +
      (1 / Real.pi) * ∑ m ∈ Finset.Icc 2 (N - 1), (1 / (m : ℝ) + 1 / ((m : ℝ) + 1)) =
      (1 / Real.pi) * ((∑ m ∈ Finset.Icc 2 (N - 1), (1 / (m : ℝ) + 1 / ((m : ℝ) + 1))) + 1 / (N : ℝ)) by ring,
    show (1 / Real.pi) * (1 / 2 + 2 * (Real.log alpha - Real.log 2)) =
      (2 / Real.pi) * Real.log alpha + (1 / 2 - 2 * Real.log 2) / Real.pi by ring]

/-- Tail pair sum bound for $N + 1 \le m \le W$ where $2 \le N \le \alpha < N + 1$. -/
theorem filter_l1_tail_sum_le {alpha : ℝ} {N : ℕ} (hN2 : 2 ≤ N)
    (hN_le_alpha : (N : ℝ) ≤ alpha) (halpha_lt_N1 : alpha < (N : ℝ) + 1) (W : ℕ)
    {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    ∑ m ∈ Finset.Icc (N + 1) W,
      (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) ≤
      3 / (4 * Real.pi ^ 2) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have halpha_pos : 0 < alpha := lt_of_lt_of_le hN_pos hN_le_alpha
  have hterm : ∀ m ∈ Finset.Icc (N + 1) W,
      |sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)| ≤
      (alpha ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1))) *
        (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) := by
    intro m hm
    have hm_ge : N + 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hcast_m1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hp := abs_sincGaussian_pair_le alpha (by omega : 1 ≤ m) h0 h1
    have h1m : 1 / (m : ℝ) + 1 / ((m : ℝ) + 1) ≤ 2 / (m : ℝ) := by
      have hle : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) :=
        one_div_le_one_div_of_le hm_pos (by linarith)
      have htwo : 2 / (m : ℝ) = 1 / (m : ℝ) + 1 / (m : ℝ) := by ring
      linarith
    have hx_ge : 3 ≤ Real.pi * (m : ℝ) ^ 2 / alpha ^ 2 := by
      have hm_gt_alpha : alpha ≤ (m : ℝ) := by
        have : (N : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm_ge
        linarith
      have hsq : alpha ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    have hexp_inv := four_mul_le_exp_of_three_le hx_ge
    have hexp_le : Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) ≤
        alpha ^ 2 / (4 * Real.pi * (m : ℝ) ^ 2) := by
      have hneg : -Real.pi * (m : ℝ) ^ 2 / alpha ^ 2 = -(Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) := by ring
      rw [hneg, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
      have hdiv : (alpha ^ 2 / (4 * Real.pi * (m : ℝ) ^ 2)) *
          (4 * (Real.pi * (m : ℝ) ^ 2 / alpha ^ 2)) = 1 := by
        have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp [hpi_ne, halpha_pos.ne', hm_pos.ne']
      calc 1 = (alpha ^ 2 / (4 * Real.pi * (m : ℝ) ^ 2)) *
            (4 * (Real.pi * (m : ℝ) ^ 2 / alpha ^ 2)) := hdiv.symm
        _ ≤ (alpha ^ 2 / (4 * Real.pi * (m : ℝ) ^ 2)) *
            Real.exp (Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) :=
          mul_le_mul_of_nonneg_left hexp_inv (by positivity)
    have hPm_le1 : |sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)| ≤
        (2 / (Real.pi * (m : ℝ))) * (alpha ^ 2 / (4 * Real.pi * (m : ℝ) ^ 2)) := by
      calc |sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
            |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|
          ≤ (1 / Real.pi) * (1 / (m : ℝ) + 1 / ((m : ℝ) + 1)) *
            Real.exp (-Real.pi * (m : ℝ) ^ 2 / alpha ^ 2) := hp
        _ ≤ (1 / Real.pi) * (2 / (m : ℝ)) * (alpha ^ 2 / (4 * Real.pi * (m : ℝ) ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1m (by positivity)) hexp_le
            (Real.exp_pos _).le (by positivity)
        _ = (2 / (Real.pi * (m : ℝ))) * (alpha ^ 2 / (4 * Real.pi * (m : ℝ) ^ 2)) := by ring
    refine hPm_le1.trans ?_
    have hdiff : 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) = 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := by
      rw [div_sub_div _ _ hm1_pos.ne' hm_pos.ne', hcast_m1]
      ring
    rw [hdiff]
    have hN1_le_m : (N : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm_ge
    have hm1_le_m : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by rw [hcast_m1]; linarith
    have hdenom : 2 * Real.pi ^ 2 * ((N : ℝ) + 1) * (((m - 1 : ℕ) : ℝ) * (m : ℝ)) ≤
        2 * Real.pi ^ 2 * (m : ℝ) ^ 3 := by
      have hcube : ((N : ℝ) + 1) * (((m - 1 : ℕ) : ℝ) * (m : ℝ)) ≤ (m : ℝ) ^ 3 := by
        calc ((N : ℝ) + 1) * (((m - 1 : ℕ) : ℝ) * (m : ℝ))
            ≤ (m : ℝ) * ((m : ℝ) * (m : ℝ)) :=
              mul_le_mul hN1_le_m (mul_le_mul_of_nonneg_right hm1_le_m hm_pos.le)
                (by positivity) hm_pos.le
          _ = (m : ℝ) ^ 3 := by ring
      nlinarith [sq_nonneg Real.pi]
    have hlhs : (2 / (Real.pi * (m : ℝ))) * (alpha ^ 2 / (4 * Real.pi * (m : ℝ) ^ 2)) =
        alpha ^ 2 / (2 * Real.pi ^ 2 * (m : ℝ) ^ 3) := by
      have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp [hpi_ne, hm_pos.ne']
      ring
    have hrhs : (alpha ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1))) *
        (1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ))) =
        alpha ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1) * (((m - 1 : ℕ) : ℝ) * (m : ℝ))) := by
      rw [div_mul_div_comm, mul_one]
    rw [hlhs, hrhs]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
  have hsum_tail : ∑ m ∈ Finset.Icc (N + 1) W,
      (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) ≤
      (alpha ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1))) * (1 / (N : ℝ)) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_Icc_inv_sub_inv_le (by omega) W) (by positivity)
  refine hsum_tail.trans ?_
  have halpha2_le : alpha ^ 2 ≤ (3 / 2 : ℝ) * ((N : ℝ) + 1) * (N : ℝ) := by
    have hN_real : (2 : ℝ) ≤ (N : ℝ) := Nat.ofNat_le_cast.mpr hN2
    nlinarith
  have hcomb : (alpha ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1))) * (1 / (N : ℝ)) =
      alpha ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1) * (N : ℝ)) := by
    rw [div_mul_div_comm, mul_one]
  rw [hcomb, div_le_iff₀ (by positivity)]
  have hprod_eq : (3 / (4 * Real.pi ^ 2)) * (2 * Real.pi ^ 2 * ((N : ℝ) + 1) * (N : ℝ)) =
      (3 / 2 : ℝ) * ((N : ℝ) + 1) * (N : ℝ) := by
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hpi_ne]
    ring
  linarith

/-- **Lemma 6.1(1) (`lem:filter-norms`) Filter $\ell_1$-Norm Logarithmic Upper Bound (`filter_l1_norm_le`, Section 6.1 (`sec:filter-norms`), equation (27) (`eq:unfolded-l1`), Table 3 (`tab:lean-map`))**:
For $\alpha \ge 2$, any window half-width $W \in \mathbb{N}$, and shift $\delta \in [0, 1]$,
$\sum_{d = -W}^{W} |g_\alpha(d - \delta)| \le \frac{2}{\pi} \ln \alpha + 1.62$. -/
theorem filter_l1_norm_le {alpha : ℝ} (halpha : 2 ≤ alpha) (W : ℕ)
    {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), |sincGaussian alpha ((d : ℝ) - delta)| ≤
      (2 / Real.pi) * Real.log alpha + 81 / 50 := by
  refine (sum_Icc_neg_to_pos_le_pair W (fun d => |sincGaussian alpha ((d : ℝ) - delta)|)
    (fun _ => abs_nonneg _)).trans ?_
  have hsplit_one : ∑ m ∈ Finset.Icc 1 W,
      (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) ≤
      (|sincGaussian alpha (((-((1 : ℕ) : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha (((((1 : ℕ) : ℤ) + 1 : ℤ) : ℝ) - delta)|) +
      ∑ m ∈ Finset.Icc 2 W,
        (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
          |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) := by
    have hsub : Finset.Icc 1 W ⊆ insert 1 (Finset.Icc 2 W) := by
      intro m hm; simp only [Finset.mem_Icc, Finset.mem_insert] at hm ⊢; omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))).trans ?_
    rw [Finset.sum_insert (by simp)]
  -- 1. Central 4 terms (d = 0, 1, -1, 2)
  have hcentral4 :
      (|sincGaussian alpha (((0 : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha (((1 : ℤ) : ℝ) - delta)|) +
      (|sincGaussian alpha (((-((1 : ℕ) : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha (((((1 : ℕ) : ℤ) + 1 : ℤ) : ℝ) - delta)|) ≤ 453 / 250 := by
    have hc0 : |sincGaussian alpha (((0 : ℤ) : ℝ) - delta)| ≤ |sinc delta| := by
      have : ((0 : ℤ) : ℝ) - delta = -delta := by push_cast; ring
      rw [this, sincGaussian_even]
      exact abs_sincGaussian_le_abs_sinc alpha delta
    have hc1 : |sincGaussian alpha (((1 : ℤ) : ℝ) - delta)| ≤ |sinc (1 - delta)| := by
      have : ((1 : ℤ) : ℝ) - delta = 1 - delta := by push_cast; ring
      rw [this]
      exact abs_sincGaussian_le_abs_sinc alpha (1 - delta)
    have hc_1 : |sincGaussian alpha (((-((1 : ℕ) : ℤ) : ℤ) : ℝ) - delta)| ≤ |sinc (1 + delta)| := by
      have : ((-((1 : ℕ) : ℤ) : ℤ) : ℝ) - delta = -(1 + delta) := by push_cast; ring
      rw [this, sincGaussian_even]
      exact abs_sincGaussian_le_abs_sinc alpha (1 + delta)
    have hc2 : |sincGaussian alpha (((((1 : ℕ) : ℤ) + 1 : ℤ) : ℝ) - delta)| ≤ |sinc (2 - delta)| := by
      have : ((((1 : ℕ) : ℤ) + 1 : ℤ) : ℝ) - delta = 2 - delta := by push_cast; ring
      rw [this]
      exact abs_sincGaussian_le_abs_sinc alpha (2 - delta)
    refine (add_le_add (add_le_add hc0 hc1) (add_le_add hc_1 hc2)).trans ?_
    linarith [abs_sinc_four_central_le h0 h1]
  -- 2. Split m ≥ 2 at N = ⌊alpha⌋₊ ≥ 2
  have hN2 : 2 ≤ Nat.floor alpha := Nat.le_floor halpha
  have hN_le_alpha : (Nat.floor alpha : ℝ) ≤ alpha := Nat.floor_le (by linarith)
  have halpha_lt_N1 : alpha < (Nat.floor alpha : ℝ) + 1 := Nat.lt_floor_add_one alpha
  have hsplit_N : ∑ m ∈ Finset.Icc 2 W,
      (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
        |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) ≤
      ∑ m ∈ Finset.Icc 2 (Nat.floor alpha),
        (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
          |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) +
      ∑ m ∈ Finset.Icc (Nat.floor alpha + 1) W,
        (|sincGaussian alpha (((-(m : ℤ) : ℤ) : ℝ) - delta)| +
          |sincGaussian alpha ((((m : ℤ) + 1 : ℤ) : ℝ) - delta)|) := by
    have hsub : Finset.Icc 2 W ⊆
        Finset.Icc 2 (Nat.floor alpha) ∪ Finset.Icc (Nat.floor alpha + 1) W := by
      intro m hm; simp only [Finset.mem_Icc, Finset.mem_union] at hm ⊢; omega
    have hdisj : Disjoint (Finset.Icc 2 (Nat.floor alpha))
        (Finset.Icc (Nat.floor alpha + 1) W) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      simp only [Finset.mem_Icc] at hm1 hm2
      omega
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  -- 3. Combine middle, tail, and numerical bounds
  have hmid := filter_l1_middle_sum_le hN2 hN_le_alpha halpha_lt_N1 h0 h1
  have htail := filter_l1_tail_sum_le hN2 hN_le_alpha halpha_lt_N1 W h0 h1
  have hpi_lo : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_hi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hlog2 : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hconst_mid : (1 / 2 - 2 * Real.log 2) / Real.pi ≤ -282 / 1000 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  have hconst_tail : 3 / (4 * Real.pi ^ 2) ≤ 76 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hstep1 := add_le_add
    (le_refl (|sincGaussian alpha (((0 : ℤ) : ℝ) - delta)| +
      |sincGaussian alpha (((1 : ℤ) : ℝ) - delta)|))
    hsplit_one
  rw [← add_assoc] at hstep1
  have hstep2 := add_le_add hcentral4 (hsplit_N.trans (add_le_add hmid htail))
  refine (hstep1.trans hstep2).trans ?_
  linarith

/-- Filter $\ell_1$-norm bound for the truncated filter `filterTap alpha m1 t1 j1` on `[-m1, m1]`
when $\alpha \ge 2$ (Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`)). -/
theorem filterTap_l1_norm_le {alpha : ℝ} (halpha : 2 ≤ alpha) (m1 t1 : ℕ)
    (j1 : Fin t1) :
    ∑ u ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
      |filterTap alpha m1 t1 j1 u| ≤
      (2 / Real.pi) * Real.log alpha + 81 / 50 := by
  have hle : ∑ u ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), |filterTap alpha m1 t1 j1 u| ≤
      ∑ u ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
        |sincGaussian alpha ((u : ℝ) - fractionalShift j1)| := by
    refine Finset.sum_le_sum fun u hu => ?_
    have habs : |u| ≤ (m1 : ℤ) := by
      have hmem := Finset.mem_Icc.mp hu
      exact abs_le.mpr hmem
    rw [filterTap_of_abs_le habs]
  exact hle.trans (filter_l1_norm_le halpha m1
    (fractionalShift_nonneg j1) (fractionalShift_le_one j1))

/-- Filter $\ell_1$-norm bound for the folded $r$-periodic filter `periodicFilterTap alpha m1 t1 r j1`
on `Fin r` when $\alpha \ge 2$, $0 < t_1$, and $0 < r$ (Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`)). -/
theorem periodicFilter_l1_norm_le {alpha : ℝ} (halpha : 2 ≤ alpha)
    (m1 : ℕ) {t1 r : ℕ} (_ht1 : 0 < t1) (hr : 0 < r) (j1 : Fin t1) :
    (∑ m : Fin r, |periodicFilterTap alpha m1 t1 r j1 m|) ≤
      (2 / Real.pi) * Real.log alpha + 81 / 50 := by
  have hle :
      (∑ m : Fin r, |periodicFilterTap alpha m1 t1 r j1 m|) ≤
        ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), |filterTap alpha m1 t1 j1 d| := by
    calc (∑ m : Fin r, |periodicFilterTap alpha m1 t1 r j1 m|)
        ≤ ∑ m : Fin r,
            ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
              (if intModFin r hr d = m then
                |sincGaussian alpha ((d : ℝ) - fractionalShift j1)|
              else 0) := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          unfold periodicFilterTap
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum (fun d _ => ?_)
          simp only [periodicFilterTap_cond_iff hr m1 d m]
          split_ifs <;> simp
      _ = ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
            ∑ m : Fin r,
              (if intModFin r hr d = m then
                |sincGaussian alpha ((d : ℝ) - fractionalShift j1)|
              else 0) := Finset.sum_comm
      _ = ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), |filterTap alpha m1 t1 j1 d| := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          rw [Finset.sum_ite_eq Finset.univ (intModFin r hr d)
            (fun _ => |sincGaussian alpha ((d : ℝ) - fractionalShift j1)|)]
          simp only [Finset.mem_univ, ↓reduceIte]
          have habs : |d| ≤ (m1 : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hd)
          rw [filterTap_of_abs_le habs]
  exact hle.trans (filterTap_l1_norm_le halpha m1 t1 j1)

/-- Every finite partial sum of `|untruncatedFilterTap alpha t1 j1 d|` over `s : Finset ℤ` is
bounded by `(2 / Real.pi) * Real.log alpha + 81 / 50` when $\alpha \ge 2$ (Lemma 6.1 (`lem:filter-norms`)). -/
theorem sum_abs_untruncatedFilterTap_le {alpha : ℝ} (halpha : 2 ≤ alpha)
    {t1 : ℕ} (j1 : Fin t1) (s : Finset ℤ) :
    (∑ d ∈ s, |untruncatedFilterTap alpha t1 j1 d|) ≤
      (2 / Real.pi) * Real.log alpha + 81 / 50 := by
  let W : ℕ := s.sup Int.natAbs
  have hsub : s ⊆ Finset.Icc (-(W : ℤ)) (W : ℤ) := by
    intro d hd
    have hle : d.natAbs ≤ W := Finset.le_sup (f := Int.natAbs) hd
    have habs : |d| ≤ (W : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact Nat.cast_le.mpr hle
    exact Finset.mem_Icc.mpr (abs_le.mp habs)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans ?_
  unfold untruncatedFilterTap
  exact filter_l1_norm_le halpha W (fractionalShift_nonneg j1) (fractionalShift_le_one j1)

/-- Summability of `|untruncatedFilterTap alpha t1 j1 d|` over `d : ℤ` when $\alpha \ge 2$ (Lemma 6.1 (`lem:filter-norms`)). -/
theorem summable_abs_untruncatedFilterTap {alpha : ℝ} (halpha : 2 ≤ alpha)
    {t1 : ℕ} (j1 : Fin t1) :
    Summable (fun d : ℤ => |untruncatedFilterTap alpha t1 j1 d|) :=
  summable_of_sum_le (fun _ => abs_nonneg _) (sum_abs_untruncatedFilterTap_le halpha j1)

/-- **Lemma 6.1(1) (`lem:filter-norms`) Untruncated Filter $\ell_1$-Norm Bound (`tsum_untruncatedFilterTap_le`, Section 6.1 (`sec:filter-norms`), equation (27) (`eq:unfolded-l1`))**:
For $\alpha \ge 2$ and $0 < t_1$, the untruncated Sinc-Gaussian filter $h^{\infty,(j_1)}$ satisfies
$\sum_{d \in \mathbb{Z}} |h^{\infty,(j_1)}_d| \le \frac{2}{\pi} \ln \alpha + 1.62$. -/
theorem tsum_untruncatedFilterTap_le {alpha : ℝ} (halpha : 2 ≤ alpha)
    {t1 : ℕ} (_ht1 : 0 < t1) (j1 : Fin t1) :
    (∑' d : ℤ, |untruncatedFilterTap alpha t1 j1 d|) ≤
      (2 / Real.pi) * Real.log alpha + 81 / 50 :=
  (summable_abs_untruncatedFilterTap halpha j1).tsum_le_of_sum_le
    (sum_abs_untruncatedFilterTap_le halpha j1)

/-! ## 5. 1D Poisson Summation & Concrete Residual Bounds (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)) -/

/-- Untruncated infinite discrete Fourier response
$\hat{f}^{\infty}_{j_1}(u_2) = \sum_{d \in \mathbb{Z}} h^{\infty,(j_1)}_d e^{2\pi i u_2 d / r}$
along the second axis (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def untruncatedFilterResponse (alpha : ℝ) {t1 r : ℕ}
    (j1 : Fin t1) (u2 : Fin r) : ℂ :=
  ∑' d : ℤ, (untruncatedFilterTap alpha t1 j1 d : ℂ) *
    expTwoPiI (((d : ℝ) * (u2.val : ℝ)) / (r : ℝ))

/-- Untruncated infinite Poisson frequency mode sum
$\sum_{m \in \mathbb{Z}} \hat{g}_\alpha(u_2 / r - m) e^{2\pi i (u_2 / r - m) j_1 / t_1}$
(Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def untruncatedPoissonModeSum (alpha : ℝ) {t1 r : ℕ}
    (j1 : Fin t1) (u2 : Fin r) : ℂ :=
  ∑' m : ℤ,
    (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
      expTwoPiI ((((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))

/-- Oddness cancellation $\int_{-1/2}^{1/2} \sin(-2\pi \nu t) \, d\nu = 0$. -/
theorem intervalIntegral_sin_two_pi_mul_eq_zero (t : ℝ) :
    (∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.sin (-2 * Real.pi * nu * t)) = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (fun nu : ℝ => Real.sin (-2 * Real.pi * nu * t))
  have h1 : -(-1 / 2 : ℝ) = (1 / 2 : ℝ) := by ring
  have h2 : -(1 / 2 : ℝ) = (-1 / 2 : ℝ) := by ring
  rw [h1, h2] at hcomp
  have hodd :
      (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.sin (-2 * Real.pi * -x * t)) =
        -(∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.sin (-2 * Real.pi * x * t)) := by
    rw [← intervalIntegral.integral_neg]
    congr 1; ext x
    have : -2 * Real.pi * -x * t = -(-2 * Real.pi * x * t) := by ring
    rw [this, Real.sin_neg]
  linarith

/-- Complex exponential boxcar integral representation of `sinc t`:
$(\operatorname{sinc}(t) : \mathbb{C}) = \int_{-1/2}^{1/2} e^{-2\pi i \nu t} \, d\nu$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
theorem ofReal_sinc_eq_intervalIntegral_cexp (t : ℝ) :
    (sinc t : ℂ) =
      ∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Complex.exp (-2 * Real.pi * Complex.I * (nu : ℂ) * (t : ℂ)) := by
  have hfun :
      (fun nu : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (nu : ℂ) * (t : ℂ))) =
      (fun nu : ℝ => (Real.cos (2 * Real.pi * nu * t) : ℂ) +
        (Real.sin (-2 * Real.pi * nu * t) : ℂ) * Complex.I) := by
    ext nu
    have hexp : -2 * Real.pi * Complex.I * (nu : ℂ) * (t : ℂ) =
        ((-2 * Real.pi * nu * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hcos : Real.cos (-2 * Real.pi * nu * t) = Real.cos (2 * Real.pi * nu * t) := by
      have : -2 * Real.pi * nu * t = -(2 * Real.pi * nu * t) := by ring
      rw [this, Real.cos_neg]
    rw [hexp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos]
  have hcont1 : Continuous (fun nu : ℝ => (Real.cos (2 * Real.pi * nu * t) : ℂ)) := by fun_prop
  have hcont2 : Continuous (fun nu : ℝ => (Real.sin (-2 * Real.pi * nu * t) : ℂ) * Complex.I) := by
    fun_prop
  rw [hfun,
    intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, sinc_eq_intervalIntegral_cos,
    intervalIntegral_sin_two_pi_mul_eq_zero]
  simp

/-- Spatial integrand $e^{-\pi (d - \delta)^2 / \alpha^2 - 2\pi i \nu (d - \delta) + 2\pi i d \xi}$
for the frequency-boxcar decomposition of `sincGaussian` (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def poissonSpatialIntegrand (alpha delta xi : ℝ) (d : ℤ) (nu : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (((d : ℝ) - delta : ℝ) : ℂ) ^ 2 / (alpha : ℂ) ^ 2 -
    2 * Real.pi * Complex.I * (nu : ℂ) * (((d : ℝ) - delta : ℝ) : ℂ) +
    2 * Real.pi * Complex.I * (d : ℂ) * (xi : ℂ))

/-- Frequency-mode integrand $\alpha e^{-\pi \alpha^2 (\xi - m - \nu)^2} e^{2\pi i (\xi - m) \delta}$
obtained after applying 1D Gaussian Poisson summation at frequency $\nu$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
noncomputable def poissonModeIntegrand (alpha delta xi : ℝ) (m : ℤ) (nu : ℝ) : ℂ :=
  ((alpha * Real.exp (-Real.pi * alpha ^ 2 * (xi - (m : ℝ) - nu) ^ 2) : ℝ) : ℂ) *
    expTwoPiI ((xi - (m : ℝ)) * delta)

/-- Each spatial term $g_\alpha(d - \delta) e^{2\pi i d \xi}$ equals the interval integral of
`poissonSpatialIntegrand alpha delta xi d` over $\nu \in [-1/2, 1/2]$. -/
theorem sincGaussian_mul_expTwoPiI_eq_intervalIntegral (alpha delta xi : ℝ) (d : ℤ) :
    (sincGaussian alpha ((d : ℝ) - delta) : ℂ) * expTwoPiI ((d : ℝ) * xi) =
      ∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), poissonSpatialIntegrand alpha delta xi d nu := by
  unfold sincGaussian expTwoPiI
  rw [Complex.ofReal_mul, ofReal_sinc_eq_intervalIntegral_cexp ((d : ℝ) - delta),
    ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
  congr 1; ext nu
  unfold poissonSpatialIntegrand
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The norm of `poissonSpatialIntegrand alpha delta xi d nu` is independent of $\nu$ and equals
$e^{-(\pi / \alpha^2)(d - \delta)^2}$. -/
theorem norm_poissonSpatialIntegrand (alpha delta xi : ℝ) (d : ℤ) (nu : ℝ) :
    ‖poissonSpatialIntegrand alpha delta xi d nu‖ =
      Real.exp (-(Real.pi / alpha ^ 2) * ((d : ℝ) - delta) ^ 2) := by
  unfold poissonSpatialIntegrand
  have hsplit :
      -Real.pi * (((d : ℝ) - delta : ℝ) : ℂ) ^ 2 / (alpha : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * (nu : ℂ) * (((d : ℝ) - delta : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * (d : ℂ) * (xi : ℂ) =
      ((-(Real.pi / alpha ^ 2) * ((d : ℝ) - delta) ^ 2 : ℝ) : ℂ) +
        ((-2 * Real.pi * nu * ((d : ℝ) - delta) + 2 * Real.pi * (d : ℝ) * xi : ℝ) : ℂ) *
          Complex.I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    ← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- Summability of shifted real Gaussians $k \mapsto e^{-c (k - s)^2}$ over $k \in \mathbb{Z}$ for $c > 0$. -/
theorem summable_exp_neg_mul_sub_sq {c : ℝ} (hc : 0 < c) (s : ℝ) :
    Summable (fun k : ℤ => Real.exp (-c * ((k : ℝ) - s) ^ 2)) := by
  have ha : ((-c : ℝ) : ℂ).re < 0 := by simp [hc]
  have hbigO :=
    (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ha ((2 * c * s : ℝ) : ℂ) (-2)).isBigO
  have hsum_c : Summable (fun k : ℤ =>
      Complex.exp (((-c : ℝ) : ℂ) * (k : ℂ) ^ 2 + ((2 * c * s : ℝ) : ℂ) * (k : ℂ))) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hbigO.comp_tendsto Int.tendsto_coe_cofinite)
  have hsum_norm := (hsum_c.norm).mul_left (Real.exp (-c * s ^ 2))
  refine hsum_norm.congr (fun k => ?_)
  have hexp :
      (((-c : ℝ) : ℂ) * (k : ℂ) ^ 2 + ((2 * c * s : ℝ) : ℂ) * (k : ℂ)) =
        ((-c * (k : ℝ) ^ 2 + 2 * c * s * (k : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 1
  ring

/-- Pointwise 1D Gaussian Poisson summation identity at frequency $\nu \in \mathbb{R}$:
for $\alpha > 0$, $\sum'_{d : \mathbb{Z}} \text{poissonSpatialIntegrand } d \, \nu =
\sum'_{m : \mathbb{Z}} \text{poissonModeIntegrand } m \, \nu$ (Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`)). -/
theorem tsum_poissonSpatialIntegrand_eq (alpha delta xi : ℝ) (halpha : 0 < alpha) (nu : ℝ) :
    (∑' d : ℤ, poissonSpatialIntegrand alpha delta xi d nu) =
      ∑' m : ℤ, poissonModeIntegrand alpha delta xi m nu := by
  set a : ℂ := ((1 / alpha ^ 2 : ℝ) : ℂ)
  set b : ℂ := ((delta / alpha ^ 2 : ℝ) : ℂ) + Complex.I * ((xi - nu : ℝ) : ℂ)
  set c0 : ℂ := Complex.exp (-Real.pi * (delta : ℂ) ^ 2 / (alpha : ℂ) ^ 2 +
    2 * Real.pi * Complex.I * (nu : ℂ) * (delta : ℂ))
  have ha : 0 < a.re := by
    dsimp [a]
    positivity
  have hterm1 : ∀ d : ℤ,
      poissonSpatialIntegrand alpha delta xi d nu =
        c0 * Complex.exp (-Real.pi * a * (d : ℂ) ^ 2 + 2 * Real.pi * b * (d : ℂ)) := by
    intro d
    unfold poissonSpatialIntegrand
    dsimp [c0, a, b]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hterm1]
  rw [tsum_mul_left, Complex.tsum_exp_neg_quadratic ha b]
  have h1_div_a : 1 / a ^ (1 / 2 : ℂ) = (alpha : ℂ) := by
    have ha_eq : a = (((alpha ^ 2)⁻¹ : ℝ) : ℂ) := by dsimp [a]; push_cast; ring
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [ha_eq, hhalf, ← Complex.ofReal_cpow (inv_nonneg.mpr (sq_nonneg alpha)),
      ← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_sq halpha.le]
    push_cast
    simp
  rw [h1_div_a, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  unfold poissonModeIntegrand expTwoPiI
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  have hcomm :
      c0 * ((alpha : ℂ) * Complex.exp (-Real.pi / a * ((m : ℂ) + Complex.I * b) ^ 2)) =
        (alpha : ℂ) * (c0 * Complex.exp (-Real.pi / a * ((m : ℂ) + Complex.I * b) ^ 2)) := by
    ring
  rw [hcomm, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  have hb : (m : ℂ) + Complex.I * b =
      -((xi : ℂ) - (m : ℂ) - (nu : ℂ)) + Complex.I * ((delta : ℂ) / (alpha : ℂ) ^ 2) := by
    dsimp [b]
    push_cast
    linear_combination ((xi : ℂ) - (nu : ℂ)) * Complex.I_sq
  have hb2 : ((m : ℂ) + Complex.I * b) ^ 2 =
      ((xi : ℂ) - (m : ℂ) - (nu : ℂ)) ^ 2 -
        2 * Complex.I * ((xi : ℂ) - (m : ℂ) - (nu : ℂ)) * ((delta : ℂ) / (alpha : ℂ) ^ 2) -
        ((delta : ℂ) / (alpha : ℂ) ^ 2) ^ 2 := by
    rw [hb]
    linear_combination (((delta : ℂ) / (alpha : ℂ) ^ 2) ^ 2) * Complex.I_sq
  have halpha_ne : (alpha : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr halpha.ne'
  rw [hb2]
  dsimp [c0, a]
  push_cast
  field_simp [halpha_ne]
  ring

/-- Uniform Gaussian upper bound on `‖poissonModeIntegrand alpha delta xi m nu‖` for
$\nu \in \operatorname{uIoc}(-1/2, 1/2)$ and $\alpha > 0$. -/
theorem norm_poissonModeIntegrand_le_of_mem_uIoc {alpha : ℝ} (halpha : 0 < alpha)
    (delta xi : ℝ) (m : ℤ) {nu : ℝ} (hnu : nu ∈ Set.uIoc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    ‖poissonModeIntegrand alpha delta xi m nu‖ ≤
      alpha * Real.exp (Real.pi * alpha ^ 2 / 4) *
        Real.exp (-(Real.pi * alpha ^ 2 / 2) * ((m : ℝ) - xi) ^ 2) := by
  unfold poissonModeIntegrand
  rw [norm_mul, norm_expTwoPiI, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg halpha.le (Real.exp_pos _).le),
    mul_assoc alpha (Real.exp _) (Real.exp _), ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) halpha.le
  rw [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ (1 / 2 : ℝ))] at hnu
  have hnu1 : -1 / 2 < nu := hnu.1
  have hnu2 : nu ≤ 1 / 2 := hnu.2
  have hsq : (1 / 2 : ℝ) * ((m : ℝ) - xi) ^ 2 - 1 / 4 ≤ (xi - (m : ℝ) - nu) ^ 2 := by
    nlinarith [sq_nonneg (xi - (m : ℝ) - 2 * nu)]
  have hpi : 0 < Real.pi * alpha ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos halpha)
  nlinarith

/-- Mode-wise frequency-boxcar integral evaluation: for $\alpha > 0$,
$\int_{-1/2}^{1/2} \text{poissonModeIntegrand } m \, \nu \, d\nu = \hat{g}_\alpha(\xi - m) e^{2\pi i (\xi - m) \delta}$. -/
theorem intervalIntegral_poissonModeIntegrand_eq (alpha delta xi : ℝ) (halpha : 0 < alpha) (m : ℤ) :
    (∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), poissonModeIntegrand alpha delta xi m nu) =
      (gHat alpha (xi - (m : ℝ)) : ℂ) * expTwoPiI ((xi - (m : ℝ)) * delta) := by
  unfold poissonModeIntegrand
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    integral_boxcar_gaussian_eq_gHat alpha (xi - (m : ℝ)) halpha.ne']

/-- **General 1D Sinc-Gaussian Poisson Summation Formula (`tsum_sincGaussian_mul_expTwoPiI_eq`, Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`))**:
For any $\alpha > 0$ and $\delta, \xi \in \mathbb{R}$,
$\sum'_{d : \mathbb{Z}} g_\alpha(d - \delta) e^{2\pi i d \xi} = \sum'_{m : \mathbb{Z}} \hat{g}_\alpha(\xi - m) e^{2\pi i (\xi - m) \delta}$. -/
theorem tsum_sincGaussian_mul_expTwoPiI_eq (alpha delta xi : ℝ) (halpha : 0 < alpha) :
    (∑' d : ℤ, (sincGaussian alpha ((d : ℝ) - delta) : ℂ) * expTwoPiI ((d : ℝ) * xi)) =
      ∑' m : ℤ, (gHat alpha (xi - (m : ℝ)) : ℂ) * expTwoPiI ((xi - (m : ℝ)) * delta) := by
  simp_rw [sincGaussian_mul_expTwoPiI_eq_intervalIntegral alpha delta xi]
  let bound1 : ℤ → ℝ → ℝ := fun d _ =>
    Real.exp (-(Real.pi / alpha ^ 2) * ((d : ℝ) - delta) ^ 2)
  have hsum_bound1 : Summable (fun d : ℤ => bound1 d 0) :=
    summable_exp_neg_mul_sub_sq (div_pos Real.pi_pos (sq_pos_of_pos halpha)) delta
  have hswap1 :
      HasSum (fun d : ℤ => ∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), poissonSpatialIntegrand alpha delta xi d nu)
        (∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ∑' d : ℤ, poissonSpatialIntegrand alpha delta xi d nu) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound1
      (fun d => ?_) (fun d => ?_) ?_ ?_ ?_
    · have hcont : Continuous (poissonSpatialIntegrand alpha delta xi d) := by
        unfold poissonSpatialIntegrand; fun_prop
      exact hcont.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun nu _ => (norm_poissonSpatialIntegrand alpha delta xi d nu).le)
    · exact Filter.Eventually.of_forall (fun _ _ => hsum_bound1)
    · dsimp [bound1]
      exact continuous_const.intervalIntegrable _ _
    · refine Filter.Eventually.of_forall (fun nu _ => ?_)
      exact (Summable.of_norm_bounded hsum_bound1
        (fun d => (norm_poissonSpatialIntegrand alpha delta xi d nu).le)).hasSum
  rw [hswap1.tsum_eq]
  simp_rw [tsum_poissonSpatialIntegrand_eq alpha delta xi halpha]
  let bound2 : ℤ → ℝ → ℝ := fun m _ =>
    alpha * Real.exp (Real.pi * alpha ^ 2 / 4) *
      Real.exp (-(Real.pi * alpha ^ 2 / 2) * ((m : ℝ) - xi) ^ 2)
  have hsum_bound2 : Summable (fun m : ℤ => bound2 m 0) :=
    (summable_exp_neg_mul_sub_sq (by positivity : 0 < Real.pi * alpha ^ 2 / 2) xi).mul_left _
  have hswap2 :
      HasSum (fun m : ℤ => ∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), poissonModeIntegrand alpha delta xi m nu)
        (∫ nu in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ∑' m : ℤ, poissonModeIntegrand alpha delta xi m nu) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound2
      (fun m => ?_) (fun m => ?_) ?_ ?_ ?_
    · have hcont : Continuous (poissonModeIntegrand alpha delta xi m) := by
        unfold poissonModeIntegrand; fun_prop
      exact hcont.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun nu hnu =>
        norm_poissonModeIntegrand_le_of_mem_uIoc halpha delta xi m hnu)
    · exact Filter.Eventually.of_forall (fun _ _ => hsum_bound2)
    · dsimp [bound2]
      exact continuous_const.intervalIntegrable _ _
    · refine Filter.Eventually.of_forall (fun nu hnu => ?_)
      exact (Summable.of_norm_bounded hsum_bound2
        (fun m => norm_poissonModeIntegrand_le_of_mem_uIoc halpha delta xi m hnu)).hasSum
  rw [← hswap2.tsum_eq]
  simp_rw [intervalIntegral_poissonModeIntegrand_eq alpha delta xi halpha]

/-- **1D Sinc-Gaussian Poisson Summation (`untruncatedFilterResponse_eq_untruncatedPoissonModeSum`, Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`), Table 3 (`tab:lean-map`))**:
For $\alpha > 0$, $j_1 \in \operatorname{Fin} t_1$, and $u_2 \in \operatorname{Fin} r$, the untruncated
spatial filter response equals the untruncated Poisson frequency mode sum:
`untruncatedFilterResponse alpha j1 u2 = untruncatedPoissonModeSum alpha j1 u2`. -/
theorem untruncatedFilterResponse_eq_untruncatedPoissonModeSum
    {alpha : ℝ} (halpha : 0 < alpha) {t1 r : ℕ}
    (j1 : Fin t1) (u2 : Fin r) :
    untruncatedFilterResponse alpha j1 u2 = untruncatedPoissonModeSum alpha j1 u2 := by
  unfold untruncatedFilterResponse untruncatedPoissonModeSum untruncatedFilterTap fractionalShift
  have h1 :
      (∑' d : ℤ,
        (sincGaussian alpha ((d : ℝ) - (j1.val : ℝ) / (t1 : ℝ)) : ℂ) *
          expTwoPiI (((d : ℝ) * (u2.val : ℝ)) / (r : ℝ))) =
      ∑' d : ℤ,
        (sincGaussian alpha ((d : ℝ) - (j1.val : ℝ) / (t1 : ℝ)) : ℂ) *
          expTwoPiI ((d : ℝ) * ((u2.val : ℝ) / (r : ℝ))) := by
    refine tsum_congr (fun d => ?_)
    rw [mul_div_assoc]
  rw [h1, tsum_sincGaussian_mul_expTwoPiI_eq alpha ((j1.val : ℝ) / (t1 : ℝ))
    ((u2.val : ℝ) / (r : ℝ)) halpha]
  refine tsum_congr (fun m => ?_)
  rw [mul_div_assoc]

/-- Symmetric finite-sum pairing identity on `Finset.Icc (-(W : ℤ)) (W : ℤ)`:
$\left(\sum_{d = -W}^{W} f(d)\right) + f(0) = \sum_{n=0}^{W} (f(n) + f(-n))$. -/
theorem sum_Icc_neg_to_pos_add_zero {G : Type*} [AddCommMonoid G] (W : ℕ) (f : ℤ → G) :
    (∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), f d) + f 0 =
      ∑ n ∈ Finset.range (W + 1), (f (n : ℤ) + f (-(n : ℤ))) := by
  induction W with
  | zero =>
    simp
  | succ k ih =>
    have hIcc : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        insert (-((k + 1 : ℕ) : ℤ))
          (insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ))) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot1 : (-((k + 1 : ℕ) : ℤ)) ∉
        insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot2 : ((k + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(k : ℤ)) (k : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnot1, Finset.sum_insert hnot2,
      Finset.sum_range_succ (n := k + 1), ← ih]
    abel

/-- Two-sided infinite tail decomposition on $\mathbb{Z}$ outside `Finset.Icc (-(W : ℤ)) (W : ℤ)`:
for any summable $f : \mathbb{Z} \to \mathbb{C}$,
$\left(\sum'_{d : \mathbb{Z}} f(d)\right) - \sum_{d = -W}^{W} f(d) = \sum'_{n : \mathbb{N}} (f(W + 1 + n) + f(-(W + 1 + n)))$. -/
theorem tsum_int_sub_sum_Icc_eq_tsum_nat_pair (W : ℕ) {f : ℤ → ℂ} (hf : Summable f) :
    (∑' d : ℤ, f d) - ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), f d =
      ∑' n : ℕ, (f ((W + 1 + n : ℕ) : ℤ) + f (-((W + 1 + n : ℕ) : ℤ))) := by
  have hpair : Summable (fun n : ℕ => f (n : ℤ) + f (-(n : ℤ))) := hf.nat_add_neg
  have hsplit := hpair.sum_add_tsum_nat_add (W + 1)
  have htot := tsum_nat_add_neg hf
  have hfin := sum_Icc_neg_to_pos_add_zero W f
  have htail :
      (∑' n : ℕ, (f ((n + (W + 1) : ℕ) : ℤ) + f (-((n + (W + 1) : ℕ) : ℤ)))) =
        ∑' n : ℕ, (f ((W + 1 + n : ℕ) : ℤ) + f (-((W + 1 + n : ℕ) : ℤ))) := by
    refine tsum_congr (fun n => ?_)
    rw [Nat.add_comm n (W + 1)]
  rw [← htail]
  linear_combination -hsplit - htot - hfin

/-- **Spatial Truncation Tail Bound (`norm_filterDiscreteResponse_sub_untruncatedFilterResponse_le`, Section 6.1 (`sec:filter-norms`), Lemma 6.1 (`lem:filter-norms`))**:
For $\alpha \ge 2$, $W \in \mathbb{N}$, $j_1 \in \operatorname{Fin} t_1$, and $u_2 \in \operatorname{Fin} r$,
the norm difference between the truncated discrete filter response and `untruncatedFilterResponse`
is bounded by `spatialTailSum alpha W (fractionalShift j1)`. -/
theorem norm_filterDiscreteResponse_sub_untruncatedFilterResponse_le
    {alpha : ℝ} (halpha : 2 ≤ alpha) (W : ℕ) {t1 r : ℕ}
    (j1 : Fin t1) (u2 : Fin r) :
    ‖filterDiscreteResponse W (fun j d => (filterTap alpha W t1 j d : ℂ)) j1 u2 -
      untruncatedFilterResponse alpha j1 u2‖ ≤
      spatialTailSum alpha W (fractionalShift j1) := by
  let f : ℤ → ℂ := fun d =>
    (untruncatedFilterTap alpha t1 j1 d : ℂ) * expTwoPiI (((d : ℝ) * (u2.val : ℝ)) / (r : ℝ))
  have hnorm_f : ∀ d : ℤ, ‖f d‖ = |sincGaussian alpha ((d : ℝ) - fractionalShift j1)| := by
    intro d
    dsimp [f, untruncatedFilterTap]
    rw [norm_mul, norm_expTwoPiI, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hsum_abs : Summable (fun d : ℤ => ‖f d‖) := by
    simpa only [hnorm_f, untruncatedFilterTap] using summable_abs_untruncatedFilterTap halpha j1
  have hf : Summable f := hsum_abs.of_norm
  have hfin_eq :
      filterDiscreteResponse W (fun j d => (filterTap alpha W t1 j d : ℂ)) j1 u2 =
        ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), f d := by
    unfold filterDiscreteResponse
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have habs : |d| ≤ (W : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hd)
    dsimp [f, untruncatedFilterTap]
    rw [filterTap_of_abs_le habs]
  rw [norm_sub_rev, hfin_eq]
  change ‖(∑' d : ℤ, f d) - ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), f d‖ ≤
    spatialTailSum alpha W (fractionalShift j1)
  rw [tsum_int_sub_sum_Icc_eq_tsum_nat_pair W hf]
  have hsum_tail_norm :
      Summable (fun n : ℕ =>
        |sincGaussian alpha (((W + 1 + n : ℕ) : ℝ) - fractionalShift j1)| +
          |sincGaussian alpha (-((W + 1 + n : ℕ) : ℝ) - fractionalShift j1)|) := by
    have h1 := (summable_nat_add_iff (W + 1)).mpr hsum_abs.nat_add_neg
    refine h1.congr (fun n => ?_)
    rw [Nat.add_comm n (W + 1), hnorm_f, hnorm_f]
    push_cast
    rfl
  have hsum_pair_norm :
      Summable (fun n : ℕ => ‖f ((W + 1 + n : ℕ) : ℤ) + f (-((W + 1 + n : ℕ) : ℤ))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum_tail_norm
    refine (norm_add_le _ _).trans ?_
    rw [hnorm_f, hnorm_f]
    push_cast
    exact le_rfl
  refine (norm_tsum_le_tsum_norm hsum_pair_norm).trans ?_
  unfold spatialTailSum
  refine Summable.tsum_le_tsum (fun n => ?_) hsum_pair_norm hsum_tail_norm
  refine (norm_add_le _ _).trans ?_
  rw [hnorm_f, hnorm_f]
  push_cast
  exact le_rfl

/-- **Two-Mode Frequency Alias Bound (`norm_untruncatedPoissonModeSum_sub_twoMode_le`, Section 5.1 (`sec:deconv-thm`), Theorem 5.1(1) (`thm:deconv`))**:
For $\alpha > 0$, $j_1 \in \operatorname{Fin} t_1$, and $u_2 \in \operatorname{Fin} r$, the norm
difference between `untruncatedPoissonModeSum` and `twoModeFrequencyApproximation` is bounded by
$1 - \hat{g}_\alpha(u_2 / r) - \hat{g}_\alpha(u_2 / r - 1)$. -/
theorem norm_untruncatedPoissonModeSum_sub_twoMode_le
    {alpha : ℝ} (halpha : 0 < alpha) {t1 r : ℕ}
    (j1 : Fin t1) (u2 : Fin r) :
    ‖untruncatedPoissonModeSum alpha j1 u2 -
      twoModeFrequencyApproximation alpha j1 u2‖ ≤
      1 - gHat alpha ((u2.val : ℝ) / (r : ℝ)) -
        gHat alpha ((u2.val : ℝ) / (r : ℝ) - 1) := by
  let S : Finset ℤ := {0, 1}
  set xi : ℝ := (u2.val : ℝ) / (r : ℝ)
  let g : ℤ → ℝ := fun m => gHat alpha (xi - (m : ℝ))
  let f : ℤ → ℂ := fun m =>
    (g m : ℂ) * expTwoPiI (((xi - (m : ℝ)) * (j1.val : ℝ)) / (t1 : ℝ))
  have hg_hasSum : HasSum g 1 := hasSum_gHat_sub_int_eq_one alpha halpha xi
  have hnorm_f : ∀ m : ℤ, ‖f m‖ = g m := by
    intro m
    dsimp [f, g]
    rw [norm_mul, norm_expTwoPiI, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (gHat_pos alpha halpha _).le]
  have hf_sum : Summable f :=
    Summable.of_norm_bounded hg_hasSum.summable (fun m => (hnorm_f m).le)
  have hf_compl : HasSum (fun x : { x // x ∉ S } => f x)
      ((∑' m : ℤ, f m) - ∑ m ∈ S, f m) :=
    (S.hasSum_iff_compl).mp hf_sum.hasSum
  have hg_compl : HasSum (fun x : { x // x ∉ S } => g x)
      (1 - ∑ m ∈ S, g m) :=
    (S.hasSum_iff_compl).mp hg_hasSum
  have hsub_f :
      untruncatedPoissonModeSum alpha j1 u2 - twoModeFrequencyApproximation alpha j1 u2 =
        ∑' x : { x // x ∉ S }, f x := by
    unfold untruncatedPoissonModeSum twoModeFrequencyApproximation
    exact hf_compl.tsum_eq.symm
  have hsum_S : ∑ m ∈ S, g m = gHat alpha xi + gHat alpha (xi - 1) := by
    dsimp [S, g]
    simp
  have htsum_g : (∑' x : { x // x ∉ S }, g x) =
      1 - gHat alpha xi - gHat alpha (xi - 1) := by
    rw [hg_compl.tsum_eq, hsum_S]
    ring
  rw [hsub_f, ← htsum_g]
  have hnorm_compl : (fun x : { x // x ∉ S } => ‖f x‖) = (fun x : { x // x ∉ S } => g x) := by
    ext x
    exact hnorm_f x
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (by rw [hnorm_compl]))
  rw [hnorm_compl]
  exact hg_compl.summable

/-- **Two-Mode Concrete Poisson Residual Bound (`norm_concretePoissonResidual_twoMode_le`, Theorem 4.2 (`thm:poisson`), Theorem 5.1(1) (`thm:deconv`), Lemma 6.1 (`lem:filter-norms`))**:
For $\alpha \ge 2$, $W \in \mathbb{N}$, $0 < t_1$, $0 < r$, $j_1 \in \operatorname{Fin} t_1$, and
$u_2 \in \operatorname{Fin} r$, the two-mode frequency residual `concretePoissonResidual alpha W {0, 1} j1 u2`
is bounded by the sum of `spatialTailSum alpha W (fractionalShift j1)` and the stopband alias tail
`1 - gHat alpha (u2 / r) - gHat alpha (u2 / r - 1)`. -/
theorem norm_concretePoissonResidual_twoMode_le
    {alpha : ℝ} (halpha : 2 ≤ alpha) (W : ℕ) {t1 r : ℕ}
    (_ht1 : 0 < t1) (_hr : 0 < r) (j1 : Fin t1) (u2 : Fin r) :
    ‖concretePoissonResidual alpha W ({0, 1} : Finset ℤ) j1 u2‖ ≤
      spatialTailSum alpha W (fractionalShift j1) +
        (1 - gHat alpha ((u2.val : ℝ) / (r : ℝ)) -
          gHat alpha ((u2.val : ℝ) / (r : ℝ) - 1)) := by
  have halpha_pos : 0 < alpha := by linarith
  refine norm_concretePoissonResidual_le_of_spatial_and_alias alpha W ({0, 1} : Finset ℤ)
    j1 u2 (untruncatedFilterResponse alpha j1 u2)
    (norm_filterDiscreteResponse_sub_untruncatedFilterResponse_le halpha W j1 u2) ?_
  rw [untruncatedFilterResponse_eq_untruncatedPoissonModeSum halpha_pos j1 u2]
  exact norm_untruncatedPoissonModeSum_sub_twoMode_le halpha_pos j1 u2

/-- **Two-Mode Concrete Poisson Residual Strict Bound (`norm_concretePoissonResidual_twoMode_lt`, Theorem 4.2 (`thm:poisson`), Theorem 5.1(1) (`thm:deconv`), Lemma 6.1 (`lem:filter-norms`))**:
For $8 \le p_{\text{work}} \le p_{\text{child}}$, $0 < t_1$, $0 < r$, $j_1 \in \operatorname{Fin} t_1$,
and $u_2 \in \operatorname{Fin} r$, the two-mode concrete Poisson residual satisfies
`‖concretePoissonResidual (alphaFromPWork pWork) (m1FromPWorkPChild pWork pChild) {0, 1} j1 u2‖ < 0.4 * 2^(-pChild) + 0.15 * 2^(-pWork)`. -/
theorem norm_concretePoissonResidual_twoMode_lt (pWork pChild : ℕ)
    (hpW : 8 ≤ pWork) (hpC : pWork ≤ pChild)
    {t1 r : ℕ} (ht1 : 0 < t1) (hr : 0 < r) (j1 : Fin t1) (u2 : Fin r) :
    ‖concretePoissonResidual (alphaFromPWork pWork) (m1FromPWorkPChild pWork pChild)
      ({0, 1} : Finset ℤ) j1 u2‖ <
      (4 / 10 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) +
        (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)) :=
  (norm_concretePoissonResidual_twoMode_le (two_le_alphaFromPWork hpW)
    (m1FromPWorkPChild pWork pChild) ht1 hr j1 u2).trans_lt
    (twoMode_spatial_and_stopband_error_lt pWork pChild hpW hpC ht1 hr j1 u2)

/-- **Spatial Residual Bound for the Two-Mode Concrete Poisson Residual (`norm_poissonSpatialResidual_concretePoissonResidual_twoMode_le`, Section 4.2 (`sec:poisson`), Theorem 4.2 (`thm:poisson`))**:
For $8 \le p_{\text{work}} \le p_{\text{child}}$, $0 < t_1$, $0 < r$, input vector $x : \operatorname{Fin}(t_1 r) \to \mathbb{C}$,
and frequencies $u_1 \in \operatorname{Fin} t_1$, $u_2 \in \operatorname{Fin} r$, the 2D-to-1D Poisson
spatial residual satisfies
`‖poissonSpatialResidual x (concretePoissonResidual (alphaFromPWork pWork) (m1FromPWorkPChild pWork pChild) {0, 1}) u1 u2‖ ≤ (0.4 * 2^(-pChild) + 0.15 * 2^(-pWork)) * vecInfNorm x`. -/
theorem norm_poissonSpatialResidual_concretePoissonResidual_twoMode_le (pWork pChild : ℕ)
    (hpW : 8 ≤ pWork) (hpC : pWork ≤ pChild)
    {t1 r : ℕ} (ht1 : 0 < t1) (hr : 0 < r)
    (x : Fin (t1 * r) → ℂ) (u1 : Fin t1) (u2 : Fin r) :
    ‖poissonSpatialResidual x
      (concretePoissonResidual (alphaFromPWork pWork) (m1FromPWorkPChild pWork pChild)
        ({0, 1} : Finset ℤ)) u1 u2‖ ≤
      ((4 / 10 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) +
        (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) * vecInfNorm x := by
  refine norm_poissonSpatialResidual_le ht1 hr x _ u1 u2 (by positivity) (fun j1 => ?_)
  exact (norm_concretePoissonResidual_twoMode_lt pWork pChild hpW hpC ht1 hr j1 u2).le

/-- Monotone spatial residual bound for any window half-width $M \ge \operatorname{m1FromPWorkPChild} p_{\text{work}} \, p_{\text{child}}$. -/
theorem norm_poissonSpatialResidual_concretePoissonResidual_twoMode_le_of_ge (pWork pChild M : ℕ)
    (hpW : 8 ≤ pWork) (hpC : pWork ≤ pChild)
    (hM : m1FromPWorkPChild pWork pChild ≤ M)
    {t1 r : ℕ} (ht1 : 0 < t1) (hr : 0 < r)
    (x : Fin (t1 * r) → ℂ) (u1 : Fin t1) (u2 : Fin r) :
    ‖poissonSpatialResidual x
      (concretePoissonResidual (alphaFromPWork pWork) M
        ({0, 1} : Finset ℤ)) u1 u2‖ ≤
      ((4 / 10 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) +
        (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) * vecInfNorm x := by
  refine norm_poissonSpatialResidual_le ht1 hr x _ u1 u2 (by positivity) (fun j1 => ?_)
  have h1 := norm_concretePoissonResidual_twoMode_le (two_le_alphaFromPWork hpW) M ht1 hr j1 u2
  have hspatial := spatial_truncation_tail_le_of_ge hpW hpC hM
    (fractionalShift_nonneg j1) (fractionalShift_le_one j1)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy0 : 0 ≤ (u2.val : ℝ) / (r : ℝ) := div_nonneg (Nat.cast_nonneg _) hr_pos.le
  have hy1 : (u2.val : ℝ) / (r : ℝ) ≤ 1 :=
    div_le_one_of_le₀ (Nat.cast_le.mpr u2.isLt.le) hr_pos.le
  have halias := gHat_stopband_alias_lt pWork hpW ((u2.val : ℝ) / (r : ℝ)) hy0 hy1
  linarith

/-! ## 6. Axiom Verification Checks -/

#print axioms sinc_even
#print axioms sinc_pi_eq_intervalIntegral_cos
#print axioms fourier_gaussian_shift_integral
#print axioms integral_boxcar_fourier_gaussian_shift_eq_gHat
#print axioms abs_sincGaussian_le_exp_neg_pi_abs
#print axioms integral_boxcar_gaussian_eq_gHat
#print axioms one_sub_gHat_sub_gHat_one_sub
#print axioms gHat_pos
#print axioms gHat_nonneg
#print axioms gHat_symm_one
#print axioms tsum_gHat_sub_int_eq_one
#print axioms gHat_passband_max_ge
#print axioms gHat_stopband_alias_lt
#print axioms gHat_ratio_pow_t1_le_015
#print axioms fitsSignedWord_quantizeRealMantissa_filterTap
#print axioms mode_isolation_sum_sub
#print axioms spreadArray_filterTap_eq_periodicFilterTap_conv
#print axioms normDFT2D_spreadArray_eq
#print axioms single_mode_poisson_collapse
#print axioms matInfNorm_spreadArray_le
#print axioms poisson_fractional_shift_identity_of_hresp
#print axioms poisson_fractional_shift_identity
#print axioms norm_concretePoissonResidual_le_of_spatial_and_alias
#print axioms spatial_truncation_tail_le
#print axioms twoMode_spatial_and_stopband_error_lt
#print axioms filter_l1_norm_le_harmonic
#print axioms filter_l1_norm_le_log_W
#print axioms filter_l1_norm_le
#print axioms filterTap_l1_norm_le
#print axioms periodicFilter_l1_norm_le
#print axioms tsum_untruncatedFilterTap_le
#print axioms tsum_sincGaussian_mul_expTwoPiI_eq
#print axioms untruncatedFilterResponse_eq_untruncatedPoissonModeSum
#print axioms norm_filterDiscreteResponse_sub_untruncatedFilterResponse_le
#print axioms norm_untruncatedPoissonModeSum_sub_twoMode_le
#print axioms norm_concretePoissonResidual_twoMode_le
#print axioms norm_concretePoissonResidual_twoMode_lt
#print axioms norm_poissonSpatialResidual_concretePoissonResidual_twoMode_le

end IntMul
