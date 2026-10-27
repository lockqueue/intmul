import IntMul.Preliminaries
import IntMul.Theorem2PoissonIdentity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# `[MS]` Section 5 (Theorem 5.1 & Lemma 5.2) & Section 6 (Lemma 6.1 & Lemma 6.5) — 2-Term Bidiagonal Deconvolution & Additive Precision Schedule

This module is part of our independent formalization of `[MS]` Sections 5 and 6 (Theorem 5.1, Lemma 5.2, Lemma 6.1, and Lemma 6.5)
(companion manuscript `[MS]`, *Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*):

1. **`[MS]` Theorem 5.1 (Part 1, §5.1: Passband Lower Bound & Telescoping Stopband Alias, eqs. (19)–(21))**:
   - Box-Gaussian Fourier transform `gHatBox(ξ) = (1/2) (erfScaled(ξ + 1/2) - erfScaled(ξ - 1/2))`.
   - Exact Nyquist value `gHatBox(1/2) = (1/2) erfScaled(1)` (zero Nyquist attenuation).
   - Closed-form telescoping stopband alias (`m ∉ {0, 1}`):
     `1 - c_0(y) - c_1(y) = (1/2) erfcScaled(y + 1/2) + (1/2) erfcScaled(3/2 - y) < 0.15 * 2^{-p_work}`.
2. **`[MS]` Theorem 5.1 (Part 2, §5.1: Cyclic 2-Term Bidiagonal Solver & Uniform Conditioning `< 2.36 t_1`, eqs. (22)–(24))**:
   - Forward sweep decomposition `Z(u_1) = Z_part(u_1) + Z_0 * Z_hom(u_1)`.
   - Exact algebraic satisfaction of all interior equations `c_0 Z(u_1 + 1) + c_1 Z(u_1) = Y(u_1 + 1)`
     and the cyclic wrap-around equation `c_0 Z(0) + c_1 Z(t_1 - 1) = Y(0)`.
   - Uniform conditioning bound: for `M(u_2) ≥ 0.49999999` and wrap-around ratio `≤ 0.15`,
     `M(u_2) (1 - ratio^{t_1}) > 0.424` and `1 / (M(u_2) (1 - ratio^{t_1})) < 2.36`.
3. **`[MS]` Theorem 5.1 (Part 3, §5.1: Exact Nyquist Alternating-Sum Identity & Solver at `u_2 = r / 2`, eq. (25))**:
   - Exact Nyquist phase identity: `stdChar ((t_1/2 + t_1 j_2)(r/2) / (t_1 r)) = i (-1)^{j_2}`.
   - Exact satisfaction of both the bidiagonal equations `c_0 Z(u_1 + 1) + c_0 Z(u_1) = Y(u_1 + 1)`
     and the alternating sum constraint `∑_{u_1=0}^{t_1-1} (-1)^{u_1} Z(u_1) = alt_true`.
4. **`[MS]` Lemma 6.5 (§6.3: Purely Additive Precision Schedule & Four-Source Inductive Error Closure, eqs. (34)–(36))**:
   - Additive schedule `p_work = p + K + 6`, `p_child = p + 2 K + 12`.
   - Four-source error closure: `(0.003 + 0.037 + 0.354) * 2^{-p} * M = 0.394 * 2^{-p} * M < 2^{-p} * M`.
-/

namespace IntMul

open scoped BigOperators FourierTransform
open Complex Real MeasureTheory intervalIntegral

/-! ## 1. `[MS]` Theorem 5.1(1) (§5.1): Concrete Lebesgue Error Function, Passband Integral, and Gaussian Tail Bound -/

/-- Concrete Gaussian error function defined via Lebesgue interval integration:
`realErf(z) = (2 / √π) ∫_{0}^{z} exp(-t^2) dt`. -/
noncomputable def realErf (z : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))

/-- Scaled Gaussian error function `realErfScaled(α, z) = realErf(√π * α * z)`. -/
noncomputable def realErfScaled (α z : ℝ) : ℝ :=
  realErf (Real.sqrt Real.pi * α * z)

/-- At `z = 0`, `realErf 0 = 0` (`∫_0^0 = 0`). -/
@[simp]
theorem realErf_zero : realErf 0 = 0 := by
  simp [realErf]

/-- At `z = 0`, `realErfScaled α 0 = 0`. -/
@[simp]
theorem realErfScaled_zero (α : ℝ) : realErfScaled α 0 = 0 := by
  simp [realErfScaled]

/-- **First-Principles Proof of Oddness of `realErf`**:
By change of variables `t ↦ -t` (`intervalIntegral.integral_comp_neg`) and interval reversal
(`intervalIntegral.integral_symm`), `realErf (-z) = -realErf z`. -/
theorem realErf_neg (z : ℝ) : realErf (-z) = -realErf z := by
  unfold realErf
  have h1 : (∫ t in (0 : ℝ)..(-z), Real.exp (-(t ^ 2))) =
      ∫ t in (0 : ℝ)..(-z), Real.exp (-((-t) ^ 2)) := by
    simp_rw [neg_sq]
  have h2 : (∫ t in (0 : ℝ)..(-z), Real.exp (-((-t) ^ 2))) =
      ∫ t in -(-z)..-(0 : ℝ), Real.exp (-(t ^ 2)) :=
    intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -z) (f := fun t : ℝ => Real.exp (-(t ^ 2)))
  rw [h1, h2, neg_neg, neg_zero, intervalIntegral.integral_symm, mul_neg]

/-- **First-Principles Proof of Oddness of `realErfScaled`**:
For every scale parameter `α : ℝ` and `z : ℝ`, `realErfScaled α (-z) = -realErfScaled α z`. -/
theorem realErfScaled_neg (α z : ℝ) : realErfScaled α (-z) = -realErfScaled α z := by
  unfold realErfScaled
  rw [mul_neg, realErf_neg]

/-- **First-Principles Proof of the Mill's Ratio / Gaussian Tail Bound**:
For any `0 < a ≤ b`, integrating `exp(-t^2) ≤ (t / a) exp(-t^2) = d/dt (-exp(-t^2) / (2a))`
via the Fundamental Theorem of Calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) yields:
`∫_{a}^{b} exp(-t^2) dt ≤ (exp(-a^2) - exp(-b^2)) / (2a) ≤ exp(-a^2) / (2a)`. -/
theorem gaussian_tail_integral_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.exp (-(t ^ 2))) ≤ (Real.exp (-(a ^ 2)) - Real.exp (-(b ^ 2))) / (2 * a) ∧
    (Real.exp (-(a ^ 2)) - Real.exp (-(b ^ 2))) / (2 * a) ≤ Real.exp (-(a ^ 2)) / (2 * a) := by
  let F : ℝ → ℝ := fun t => -(1 / (2 * a)) * Real.exp (-(t ^ 2))
  let F' : ℝ → ℝ := fun t => (t / a) * Real.exp (-(t ^ 2))
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t := by
    intro t _
    have hd1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t ^ (2 - 1) * 1) t := (hasDerivAt_id t).pow 2
    have hd2 : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2)))
        (Real.exp (-(t ^ 2)) * -(2 * t ^ (2 - 1) * 1)) t := hd1.neg.exp
    have hd3 := hd2.const_mul (-(1 / (2 * a)))
    refine hd3.congr_deriv ?_
    dsimp [F']
    have ha_ne : a ≠ 0 := ha.ne'
    field_simp [ha_ne]
  have hcont_exp : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) :=
    Real.continuous_exp.comp (continuous_pow 2).neg
  have hcont_F' : Continuous F' :=
    (continuous_id.div_const a).mul hcont_exp
  have hint_exp : IntervalIntegrable (fun t : ℝ => Real.exp (-(t ^ 2))) volume a b :=
    hcont_exp.intervalIntegrable a b
  have hint_F' : IntervalIntegrable F' volume a b :=
    hcont_F'.intervalIntegrable a b
  have hftc : (∫ t in a..b, F' t) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_F'
  have hmono : (∫ t in a..b, Real.exp (-(t ^ 2))) ≤ ∫ t in a..b, F' t := by
    refine intervalIntegral.integral_mono_on hab hint_exp hint_F' fun t ht => ?_
    dsimp [F']
    have hta : 1 ≤ t / a := (le_div_iff₀ ha).mpr (by linarith [ht.1])
    have hexp_nonneg : 0 ≤ Real.exp (-(t ^ 2)) := (Real.exp_pos _).le
    nlinarith
  have hF_sub : F b - F a = (Real.exp (-(a ^ 2)) - Real.exp (-(b ^ 2))) / (2 * a) := by
    dsimp [F]
    ring
  rw [hftc, hF_sub] at hmono
  refine ⟨hmono, ?_⟩
  have hexp_b : 0 < Real.exp (-(b ^ 2)) := Real.exp_pos _
  have h2a : 0 < 2 * a := by linarith
  exact div_le_div_of_nonneg_right (by linarith) h2a.le

/-- **Corollary of `gaussian_tail_integral_le` (Complementary Error Function Tail Bound, `[MS]` §5.1)**:
For `α > 0`, `z > 0`, and any upper integration limit `B ≥ √π * α * z`, the complementary
Gaussian tail integral `(2 / √π) ∫_{√π α z}^B exp(-t^2) dt` is bounded above by
`exp(-π α^2 z^2) / (π α z)`. -/
theorem realErfcTrunc_le_gaussian_tail (α z B : ℝ) (hα : 0 < α) (hz : 0 < z)
    (hB : Real.sqrt Real.pi * α * z ≤ B) :
    (2 / Real.sqrt Real.pi) * (∫ t in (Real.sqrt Real.pi * α * z)..B, Real.exp (-(t ^ 2))) ≤
      Real.exp (-(Real.pi * α ^ 2 * z ^ 2)) / (Real.pi * α * z) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  set a := Real.sqrt Real.pi * α * z
  have ha : 0 < a := mul_pos (mul_pos hsqrt_pi hα) hz
  have htail := (gaussian_tail_integral_le a B ha hB).1.trans (gaussian_tail_integral_le a B ha hB).2
  have hmul := mul_le_mul_of_nonneg_left htail (div_nonneg zero_le_two hsqrt_pi.le)
  refine hmul.trans_eq ?_
  dsimp [a]
  have hsq : (Real.sqrt Real.pi * α * z) ^ 2 = Real.pi * α ^ 2 * z ^ 2 := by
    calc (Real.sqrt Real.pi * α * z) ^ 2
        = (Real.sqrt Real.pi) ^ 2 * α ^ 2 * z ^ 2 := by ring
      _ = Real.pi * α ^ 2 * z ^ 2 := by rw [Real.sq_sqrt hpi.le]
  have hmul_pi : Real.sqrt Real.pi * (2 * (Real.sqrt Real.pi * α * z)) =
      2 * (Real.pi * α * z) := by
    calc Real.sqrt Real.pi * (2 * (Real.sqrt Real.pi * α * z))
        = 2 * ((Real.sqrt Real.pi * Real.sqrt Real.pi) * α * z) := by ring
      _ = 2 * (Real.pi * α * z) := by rw [Real.mul_self_sqrt hpi.le]
  rw [hsq]
  have hα_ne : α ≠ 0 := hα.ne'
  have hz_ne : z ≠ 0 := hz.ne'
  have hpi_ne : Real.pi ≠ 0 := hpi.ne'
  calc 2 / Real.sqrt Real.pi * (Real.exp (-(Real.pi * α ^ 2 * z ^ 2)) / (2 * (Real.sqrt Real.pi * α * z)))
      = (2 * Real.exp (-(Real.pi * α ^ 2 * z ^ 2))) /
          (Real.sqrt Real.pi * (2 * (Real.sqrt Real.pi * α * z))) := by ring
    _ = (2 * Real.exp (-(Real.pi * α ^ 2 * z ^ 2))) / (2 * (Real.pi * α * z)) := by rw [hmul_pi]
    _ = Real.exp (-(Real.pi * α ^ 2 * z ^ 2)) / (Real.pi * α * z) := by
        field_simp [hpi_ne, hα_ne, hz_ne]

/-- The Box-Gaussian Fourier transform `ĝ(ξ) = (1/2) (E(ξ + 1/2) - E(ξ - 1/2))`,
parameterized by the scaled error function `E(z) = erf(√π α z)`. -/
noncomputable def gHatBox (erfScaled : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (erfScaled (ξ + 1 / 2) - erfScaled (ξ - 1 / 2))

/-- Primary passband coefficient `c_0(y) = ĝ(y)` (`m = 0`). -/
noncomputable def c0Coeff (erfScaled : ℝ → ℝ) (y : ℝ) : ℝ :=
  gHatBox erfScaled y

/-- Secondary passband coefficient `c_1(y) = ĝ(1 - y)` (`m = 1`). -/
noncomputable def c1Coeff (erfScaled : ℝ → ℝ) (y : ℝ) : ℝ :=
  gHatBox erfScaled (1 - y)

/-- Complementary scaled error function `erfcScaled(z) = 1 - erfScaled(z)`. -/
noncomputable def erfcScaled (erfScaled : ℝ → ℝ) (z : ℝ) : ℝ :=
  1 - erfScaled z

/-- **Improper Gaussian Tail Integral Representation of `erfcScaled (realErfScaled α)`**:
Since `∫_{0}^{∞} exp(-t^2) dt = √π / 2` (`integral_gaussian_Ioi`), splitting `(0, ∞)` at
`a = √π * α * z` shows that `erfcScaled (realErfScaled α) z = 1 - realErfScaled α z` equals
the improper Gaussian tail integral `(2 / √π) ∫_{t > √π α z} exp(-t^2) dt`. -/
theorem erfcScaled_realErfScaled_eq_integral_Ioi (α z : ℝ) :
    erfcScaled (realErfScaled α) z =
      (2 / Real.sqrt Real.pi) *
        ∫ t in Set.Ioi (Real.sqrt Real.pi * α * z), Real.exp (-(t ^ 2)) := by
  unfold erfcScaled realErfScaled realErf
  set a := Real.sqrt Real.pi * α * z
  have hint : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq one_pos
  have hgauss : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 := by
    simpa only [neg_one_mul, div_one] using integral_gaussian_Ioi 1
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) :=
    Real.continuous_exp.comp (continuous_pow 2).neg
  have ht0 := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hint.integrableOn Filter.tendsto_id
  have hta := intervalIntegral_tendsto_integral_Ioi a hint.integrableOn Filter.tendsto_id
  have hsub : ∀ B : ℝ,
      (∫ t in a..B, Real.exp (-(t ^ 2))) =
        (∫ t in (0 : ℝ)..B, Real.exp (-(t ^ 2))) - (∫ t in (0 : ℝ)..a, Real.exp (-(t ^ 2))) := by
    intro B
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 a)
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) a B)
    linarith
  have hta' : Filter.Tendsto (fun B : ℝ => ∫ t in a..B, Real.exp (-(t ^ 2))) Filter.atTop
      (nhds ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2))) -
        (∫ t in (0 : ℝ)..a, Real.exp (-(t ^ 2))))) := by
    simp_rw [hsub]
    exact ht0.sub_const _
  have heq : (∫ t in Set.Ioi a, Real.exp (-(t ^ 2))) =
      Real.sqrt Real.pi / 2 - ∫ t in (0 : ℝ)..a, Real.exp (-(t ^ 2)) := by
    rw [← hgauss]
    exact tendsto_nhds_unique hta hta'
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [heq, mul_sub]
  have h1 : 2 / Real.sqrt Real.pi * (Real.sqrt Real.pi / 2) = 1 := by
    field_simp [hsqrt_ne]
  rw [h1]

/-- **Upper Bound on `erfcScaled (realErfScaled α)` via the Improper Gaussian Tail Integral**:
For `α > 0` and `z > 0`, `erfcScaled (realErfScaled α) z ≤ exp(-π α^2 z^2) / (π α z)`. -/
theorem erfcScaled_realErfScaled_le_gaussian_tail (α z : ℝ) (hα : 0 < α) (hz : 0 < z) :
    erfcScaled (realErfScaled α) z ≤ Real.exp (-(Real.pi * α ^ 2 * z ^ 2)) / (Real.pi * α * z) := by
  rw [erfcScaled_realErfScaled_eq_integral_Ioi]
  set a := Real.sqrt Real.pi * α * z
  have hint : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq one_pos
  have hta := (intervalIntegral_tendsto_integral_Ioi a hint.integrableOn Filter.tendsto_id).const_mul
    (2 / Real.sqrt Real.pi)
  refine le_of_tendsto hta ?_
  filter_upwards [Filter.eventually_ge_atTop a] with B hB
  exact realErfcTrunc_le_gaussian_tail α z B hα hz hB

/-- If `erfScaled` is odd (`erfScaled (-z) = -erfScaled z`), then `gHatBox` is even. -/
theorem gHatBox_even (erfScaled : ℝ → ℝ) (hodd : ∀ z, erfScaled (-z) = -erfScaled z) (ξ : ℝ) :
    gHatBox erfScaled (-ξ) = gHatBox erfScaled ξ := by
  unfold gHatBox
  have h1 : -ξ + 1 / 2 = -(ξ - 1 / 2) := by ring
  have h2 : -ξ - 1 / 2 = -(ξ + 1 / 2) := by ring
  rw [h1, h2, hodd, hodd]
  ring

/-- At the Nyquist frequency `y = 1/2`, `c_0(1/2) = c_1(1/2) = (1/2) erfScaled 1` (zero Nyquist loss). -/
theorem theorem3_nyquist_passband_eq (erfScaled : ℝ → ℝ) (hzero : erfScaled 0 = 0) :
    c0Coeff erfScaled (1 / 2) = (1 / 2 : ℝ) * erfScaled 1 ∧
    c1Coeff erfScaled (1 / 2) = (1 / 2 : ℝ) * erfScaled 1 := by
  unfold c0Coeff c1Coeff gHatBox
  have h1 : (1 / 2 : ℝ) + 1 / 2 = 1 := by ring
  have h2 : (1 / 2 : ℝ) - 1 / 2 = 0 := by ring
  have h3 : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
  rw [h3, h1, h2, hzero]
  constructor <;> ring

/-- **`[MS]` Theorem 5.1 (Part 1: Closed-Form Telescoping Stopband Alias, `[MS]` §5.1, eq. (21))**:
Because `erfScaled` is odd, the interior boundary point `y - 1/2` cancels between `c_0(y)` and `c_1(y)`,
so the excluded stopband alias sum `1 - c_0(y) - c_1(y)` telescopes identically to:
`(1/2) erfcScaled(y + 1/2) + (1/2) erfcScaled(3/2 - y)`. -/
theorem theorem3_telescoping_stopband_alias
    (erfScaled : ℝ → ℝ) (hodd : ∀ z, erfScaled (-z) = -erfScaled z) (y : ℝ) :
    1 - c0Coeff erfScaled y - c1Coeff erfScaled y =
      (1 / 2 : ℝ) * erfcScaled erfScaled (y + 1 / 2) +
      (1 / 2 : ℝ) * erfcScaled erfScaled (3 / 2 - y) := by
  unfold c0Coeff c1Coeff gHatBox erfcScaled
  have h1 : (1 : ℝ) - y + 1 / 2 = 3 / 2 - y := by ring
  have h2 : (1 : ℝ) - y - 1 / 2 = -(y - 1 / 2) := by ring
  rw [h1, h2, hodd (y - 1 / 2)]
  ring

/-- Stopband alias bound: if both complementary error terms are `< 0.15 * 2^{-p_work}`, then
`1 - c_0(y) - c_1(y) < 0.15 * 2^{-p_work}`. -/
theorem theorem3_stopband_alias_bound
    (erfScaled : ℝ → ℝ) (hodd : ∀ z, erfScaled (-z) = -erfScaled z)
    (y : ℝ) (p_work : ℕ)
    (h_left : erfcScaled erfScaled (y + 1 / 2) < (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)))
    (h_right : erfcScaled erfScaled (3 / 2 - y) < (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ))) :
    1 - c0Coeff erfScaled y - c1Coeff erfScaled y <
      (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) := by
  rw [theorem3_telescoping_stopband_alias erfScaled hodd y]
  linarith

/-- **`[MS]` Theorem 5.1 (Concrete Box-Gaussian Convolution Integral Identity, `[MS]` §4.2, eq. (16) & §5.1)**:
For concrete `realErfScaled α`, the Box-Gaussian passband `gHatBox (realErfScaled α) ξ` equals
the exact Lebesgue interval integral `(1 / √π) ∫_{√π α (ξ - 1/2)}^{√π α (ξ + 1/2)} exp(-t^2) dt`,
and satisfies `1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y =
(1/2) erfcScaled (realErfScaled α) (y + 1/2) + (1/2) erfcScaled (realErfScaled α) (3/2 - y)`
unconditionally (without any oddness hypothesis). -/
theorem theorem3_concrete_box_gaussian_integral_and_telescoping (α ξ y : ℝ) :
    gHatBox (realErfScaled α) ξ =
      (1 / Real.sqrt Real.pi) *
        ∫ t in (Real.sqrt Real.pi * α * (ξ - 1 / 2))..(Real.sqrt Real.pi * α * (ξ + 1 / 2)),
          Real.exp (-(t ^ 2)) ∧
    1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y =
      (1 / 2 : ℝ) * erfcScaled (realErfScaled α) (y + 1 / 2) +
      (1 / 2 : ℝ) * erfcScaled (realErfScaled α) (3 / 2 - y) := by
  refine ⟨?_, theorem3_telescoping_stopband_alias (realErfScaled α) (realErfScaled_neg α) y⟩
  unfold gHatBox realErfScaled realErf
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) :=
    Real.continuous_exp.comp (continuous_pow 2).neg
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (Real.sqrt Real.pi * α * (ξ - 1 / 2)) 0)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (Real.sqrt Real.pi * α * (ξ + 1 / 2)))
  rw [← hadj, intervalIntegral.integral_symm (Real.sqrt Real.pi * α * (ξ - 1 / 2)) 0]
  ring

/-- **`[MS]` Theorem 5.1 (Unconditional Stopband Alias Gaussian-Tail Upper Bound, `[MS]` §5.1, eq. (21))**:
For `α > 0` and `y ∈ (-1/2, 3/2)` (in particular for all `y ∈ [0, 1]`), the excluded stopband alias
sum `1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y` is unconditionally bounded by
the sum of the two Gaussian tails:
`(1/2) exp(-π α^2 (y + 1/2)^2) / (π α (y + 1/2)) + (1/2) exp(-π α^2 (3/2 - y)^2) / (π α (3/2 - y))`. -/
theorem theorem3_stopband_alias_le_gaussian_tails
    (α y : ℝ) (hα : 0 < α) (hy_low : -1 / 2 < y) (hy_high : y < 3 / 2) :
    1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y ≤
      (1 / 2 : ℝ) * (Real.exp (-(Real.pi * α ^ 2 * (y + 1 / 2) ^ 2)) / (Real.pi * α * (y + 1 / 2))) +
      (1 / 2 : ℝ) * (Real.exp (-(Real.pi * α ^ 2 * (3 / 2 - y) ^ 2)) / (Real.pi * α * (3 / 2 - y))) := by
  rw [theorem3_telescoping_stopband_alias (realErfScaled α) (realErfScaled_neg α) y]
  have hz1 : 0 < y + 1 / 2 := by linarith
  have hz2 : 0 < 3 / 2 - y := by linarith
  have h1 := erfcScaled_realErfScaled_le_gaussian_tail α (y + 1 / 2) hα hz1
  have h2 := erfcScaled_realErfScaled_le_gaussian_tail α (3 / 2 - y) hα hz2
  linarith

/-- The paper's Gaussian width parameter schedule (`[MS]` §5.1, eqs. (20)–(21)):
`α = 2 √(p_work ln 2 / π)`. -/
noncomputable def alphaSchedule (p_work : ℕ) : ℝ :=
  2 * Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi)

/-- For `8 ≤ p_work`, `8 < Real.pi * alphaSchedule p_work`. -/
theorem pi_mul_alphaSchedule_gt_eight (p_work : ℕ) (hp : 8 ≤ p_work) :
    (8 : ℝ) < Real.pi * alphaSchedule p_work := by
  have hp_real : (8 : ℝ) ≤ (p_work : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p_work : ℝ) := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_pos : 0 < Real.log 2 := by linarith
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos hp_pos hlog2_pos) hpi
  have hα : 0 < alphaSchedule p_work := by
    unfold alphaSchedule
    exact mul_pos zero_lt_two (Real.sqrt_pos.mpr hrad_pos)
  have hpos : 0 < Real.pi * alphaSchedule p_work := mul_pos hpi hα
  have hsq_eq : (Real.pi * alphaSchedule p_work) ^ 2 =
      Real.pi * (4 * (p_work : ℝ) * Real.log 2) := by
    unfold alphaSchedule
    calc (Real.pi * (2 * Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi))) ^ 2
        = Real.pi * (Real.pi * (4 * (Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi)) ^ 2)) := by ring
      _ = Real.pi * (Real.pi * (4 * ((p_work : ℝ) * Real.log 2 / Real.pi))) := by
          rw [Real.sq_sqrt hrad_pos.le]
      _ = Real.pi * (4 * (p_work : ℝ) * Real.log 2) := by
          congr 1
          field_simp [hpi.ne']
  have h64 : (8 : ℝ) ^ 2 < (Real.pi * alphaSchedule p_work) ^ 2 := by
    rw [hsq_eq]
    have h1 : (22.18 : ℝ) < 4 * (p_work : ℝ) * Real.log 2 := by nlinarith
    nlinarith
  nlinarith

/-- Exact identity `Real.pi * (alphaSchedule p_work) ^ 2 = 4 * (p_work : ℝ) * Real.log 2` for `0 < p_work`. -/
theorem pi_mul_alphaSchedule_sq (p_work : ℕ) (hp : 0 < p_work) :
    Real.pi * (alphaSchedule p_work) ^ 2 = 4 * (p_work : ℝ) * Real.log 2 := by
  have hp_pos : (0 : ℝ) < (p_work : ℝ) := Nat.cast_pos.mpr hp
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos hp_pos hlog2_pos) hpi
  unfold alphaSchedule
  calc Real.pi * (2 * Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi)) ^ 2
      = Real.pi * (4 * (Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi)) ^ 2) := by ring
    _ = Real.pi * (4 * ((p_work : ℝ) * Real.log 2 / Real.pi)) := by rw [Real.sq_sqrt hrad_pos.le]
    _ = 4 * (p_work : ℝ) * Real.log 2 := by field_simp [hpi.ne']

/-- For `8 ≤ p_work` and `1 / 2 ≤ z`, `erfcScaled (realErfScaled (alphaSchedule p_work)) z < 0.25 * 2^{-p_work}`. -/
theorem erfcScaled_alphaSchedule_lt_quarter (p_work : ℕ) (hp : 8 ≤ p_work) (z : ℝ) (hz : 1 / 2 ≤ z) :
    erfcScaled (realErfScaled (alphaSchedule p_work)) z <
      (0.25 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) := by
  have hp_pos : 0 < p_work := by omega
  have hp_real : (8 : ℝ) ≤ (p_work : ℝ) := by exact_mod_cast hp
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos (Nat.cast_pos.mpr hp_pos) hlog2_pos) hpi
  have hα : 0 < alphaSchedule p_work := mul_pos zero_lt_two (Real.sqrt_pos.mpr hrad_pos)
  have hz_pos : 0 < z := by linarith
  have hpi_alpha_sq := pi_mul_alphaSchedule_sq p_work hp_pos
  have hz_sq : (1 / 4 : ℝ) ≤ z ^ 2 := by nlinarith
  have hexp_arg : (p_work : ℝ) * Real.log 2 ≤ Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2 := by
    rw [hpi_alpha_sq]
    have hprod_nonneg : 0 ≤ (p_work : ℝ) * Real.log 2 := by positivity
    nlinarith
  have hexp_le : Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) ≤
      (2 : ℝ) ^ (-(p_work : ℤ)) := by
    have h1 : Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) ≤
        Real.exp (-((p_work : ℝ) * Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-((p_work : ℝ) * Real.log 2)) = (2 : ℝ) ^ (-(p_work : ℤ)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log zero_lt_two, zpow_neg, zpow_natCast]
    exact h1.trans_eq h2
  have hpi_α_gt8 := pi_mul_alphaSchedule_gt_eight p_work hp
  have hdenom_gt : (4 : ℝ) < Real.pi * alphaSchedule p_work * z := by nlinarith
  have hdenom_pos : 0 < Real.pi * alphaSchedule p_work * z := by linarith
  have hinv_lt : 1 / (Real.pi * alphaSchedule p_work * z) < (0.25 : ℝ) := by
    rw [div_lt_iff₀ hdenom_pos]
    linarith
  calc erfcScaled (realErfScaled (alphaSchedule p_work)) z
      ≤ Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) /
          (Real.pi * alphaSchedule p_work * z) :=
        erfcScaled_realErfScaled_le_gaussian_tail (alphaSchedule p_work) z hα hz_pos
    _ = (1 / (Real.pi * alphaSchedule p_work * z)) *
          Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) := by ring
    _ ≤ (1 / (Real.pi * alphaSchedule p_work * z)) * (2 : ℝ) ^ (-(p_work : ℤ)) :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ < (0.25 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) :=
        mul_lt_mul_of_pos_right hinv_lt (zpow_pos (by norm_num) _)

/-- For `8 ≤ p_work` and `1 ≤ z`, `erfcScaled (realErfScaled (alphaSchedule p_work)) z < (1 / 8) * 2^{-(4 * p_work)} ≤ (1 / 40) * 2^{-p_work}`. -/
theorem erfcScaled_alphaSchedule_lt_of_ge_one (p_work : ℕ) (hp : 8 ≤ p_work) (z : ℝ) (hz : 1 ≤ z) :
    erfcScaled (realErfScaled (alphaSchedule p_work)) z <
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) ∧
    erfcScaled (realErfScaled (alphaSchedule p_work)) z <
      (1 / 40 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) := by
  have hp_pos : 0 < p_work := by omega
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos (Nat.cast_pos.mpr hp_pos) hlog2_pos) hpi
  have hα : 0 < alphaSchedule p_work := mul_pos zero_lt_two (Real.sqrt_pos.mpr hrad_pos)
  have hz_pos : 0 < z := by linarith
  have hpi_alpha_sq := pi_mul_alphaSchedule_sq p_work hp_pos
  have hz_sq : (1 : ℝ) ≤ z ^ 2 := by nlinarith
  have hexp_arg : ((4 * p_work : ℕ) : ℝ) * Real.log 2 ≤
      Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2 := by
    rw [hpi_alpha_sq]
    push_cast
    have hprod_nonneg : 0 ≤ (p_work : ℝ) * Real.log 2 := by positivity
    nlinarith
  have hexp_le : Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) ≤
      (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) := by
    have h1 : Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) ≤
        Real.exp (-(((4 * p_work : ℕ) : ℝ) * Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(((4 * p_work : ℕ) : ℝ) * Real.log 2)) =
        (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log zero_lt_two, zpow_neg, zpow_natCast]
    exact h1.trans_eq h2
  have hpi_α_gt8 := pi_mul_alphaSchedule_gt_eight p_work hp
  have hdenom_gt : (8 : ℝ) < Real.pi * alphaSchedule p_work * z := by nlinarith
  have hdenom_pos : 0 < Real.pi * alphaSchedule p_work * z := by linarith
  have hinv_lt : 1 / (Real.pi * alphaSchedule p_work * z) < (1 / 8 : ℝ) := by
    rw [div_lt_iff₀ hdenom_pos]
    linarith
  have hfirst : erfcScaled (realErfScaled (alphaSchedule p_work)) z <
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) := by
    calc erfcScaled (realErfScaled (alphaSchedule p_work)) z
        ≤ Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) /
            (Real.pi * alphaSchedule p_work * z) :=
          erfcScaled_realErfScaled_le_gaussian_tail (alphaSchedule p_work) z hα hz_pos
      _ = (1 / (Real.pi * alphaSchedule p_work * z)) *
            Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) := by ring
      _ ≤ (1 / (Real.pi * alphaSchedule p_work * z)) * (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ < (1 / 8 : ℝ) * (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) :=
          mul_lt_mul_of_pos_right hinv_lt (zpow_pos (by norm_num) _)
  refine ⟨hfirst, hfirst.trans_le ?_⟩
  have hzpow :
      (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) ≤
        (2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(p_work : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc (1 / 8 : ℝ) * (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ))
      ≤ (1 / 8 : ℝ) * ((2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(p_work : ℤ))) :=
        mul_le_mul_of_nonneg_left hzpow (by norm_num)
    _ = ((1 / 8 : ℝ) * (2 : ℝ) ^ (-24 : ℤ)) * (2 : ℝ) ^ (-(p_work : ℤ)) := by ring
    _ ≤ (1 / 40 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- **Concrete Gaussian Tail Bound `< 0.15 * 2^{-p_work}` at `α = alphaSchedule p_work` (`[MS]` §5.1, eqs. (20)–(21))**:
For `p_work ≥ 21` and `z ≥ 1 / 2`, `erfcScaled (realErfScaled (alphaSchedule p_work)) z < 0.15 * 2^{-p_work}`. -/
theorem erfcScaled_alphaSchedule_lt (p_work : ℕ) (hp : 21 ≤ p_work) (z : ℝ) (hz : 1 / 2 ≤ z) :
    erfcScaled (realErfScaled (alphaSchedule p_work)) z <
      (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) := by
  have hp_real : (21 : ℝ) ≤ (p_work : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p_work : ℝ) := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_pos : 0 < Real.log 2 := by linarith
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos hp_pos hlog2_pos) hpi
  have hα : 0 < alphaSchedule p_work := by
    unfold alphaSchedule
    exact mul_pos zero_lt_two (Real.sqrt_pos.mpr hrad_pos)
  have hz_pos : 0 < z := by linarith
  have hpi_alpha_sq := pi_mul_alphaSchedule_sq p_work (by omega)
  have hz_sq : (1 / 4 : ℝ) ≤ z ^ 2 := by nlinarith
  have hexp_arg : (p_work : ℝ) * Real.log 2 ≤ Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2 := by
    rw [hpi_alpha_sq]
    have hprod_nonneg : 0 ≤ (p_work : ℝ) * Real.log 2 := mul_nonneg hp_pos.le hlog2_pos.le
    nlinarith
  have hexp_le : Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) ≤
      (2 : ℝ) ^ (-(p_work : ℤ)) := by
    have h1 : Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) ≤
        Real.exp (-((p_work : ℝ) * Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-((p_work : ℝ) * Real.log 2)) = (2 : ℝ) ^ (-(p_work : ℤ)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log zero_lt_two, zpow_neg, zpow_natCast]
    exact h1.trans_eq h2
  have hdenom_pos : 0 < Real.pi * alphaSchedule p_work * z := mul_pos (mul_pos hpi hα) hz_pos
  have hdenom_sq : Real.pi * (p_work : ℝ) * Real.log 2 ≤
      (Real.pi * alphaSchedule p_work * z) ^ 2 := by
    calc Real.pi * (p_work : ℝ) * Real.log 2
        = Real.pi * ((p_work : ℝ) * Real.log 2) := by ring
      _ ≤ Real.pi * (Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2) :=
          mul_le_mul_of_nonneg_left hexp_arg hpi.le
      _ = (Real.pi * alphaSchedule p_work * z) ^ 2 := by ring
  have hpi_p : (3.14 : ℝ) * 21 ≤ Real.pi * (p_work : ℝ) := by nlinarith
  have hnum_sq : (20 / 3 : ℝ) ^ 2 < Real.pi * (p_work : ℝ) * Real.log 2 := by
    nlinarith
  have hdenom_gt : (20 / 3 : ℝ) < Real.pi * alphaSchedule p_work * z := by
    have hsq_lt : (20 / 3 : ℝ) ^ 2 < (Real.pi * alphaSchedule p_work * z) ^ 2 :=
      hnum_sq.trans_le hdenom_sq
    nlinarith
  have hinv_lt : 1 / (Real.pi * alphaSchedule p_work * z) < (0.15 : ℝ) := by
    rw [div_lt_iff₀ hdenom_pos]
    linarith
  calc erfcScaled (realErfScaled (alphaSchedule p_work)) z
      ≤ Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) /
          (Real.pi * alphaSchedule p_work * z) :=
        erfcScaled_realErfScaled_le_gaussian_tail (alphaSchedule p_work) z hα hz_pos
    _ = (1 / (Real.pi * alphaSchedule p_work * z)) *
          Real.exp (-(Real.pi * (alphaSchedule p_work) ^ 2 * z ^ 2)) := by ring
    _ ≤ (1 / (Real.pi * alphaSchedule p_work * z)) * (2 : ℝ) ^ (-(p_work : ℤ)) :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ < (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) :=
        mul_lt_mul_of_pos_right hinv_lt (zpow_pos (by norm_num) _)

/-- **`[MS]` Theorem 5.1 (Unconditional Stopband Alias Bound `< 0.15 * 2^{-p_work}` at `α = alphaSchedule p_work`, `[MS]` §5.1, eqs. (20)–(21))**:
For `p_work ≥ 8` and `y ∈ [0, 1]`, because `(y + 1 / 2) + (3 / 2 - y) = 2`, one argument of `erfcScaled`
is `≥ 1 / 2` and the other is `≥ 1`, so the excluded stopband alias sum satisfies strictly
`1 - c0Coeff (realErfScaled (alphaSchedule p_work)) y - c1Coeff (realErfScaled (alphaSchedule p_work)) y < 0.15 * 2^{-p_work}`. -/
theorem theorem3_stopband_alias_bound_alphaSchedule
    (p_work : ℕ) (hp : 8 ≤ p_work) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - c0Coeff (realErfScaled (alphaSchedule p_work)) y -
      c1Coeff (realErfScaled (alphaSchedule p_work)) y <
      (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) := by
  rw [theorem3_telescoping_stopband_alias (realErfScaled (alphaSchedule p_work))
    (realErfScaled_neg (alphaSchedule p_work)) y]
  have h_comb :
      (1 / 2 : ℝ) * ((0.25 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ))) +
        (1 / 2 : ℝ) * ((1 / 40 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ))) <
      (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) := by
    calc (1 / 2 : ℝ) * ((0.25 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ))) +
          (1 / 2 : ℝ) * ((1 / 40 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)))
        = (0.1375 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) := by ring
      _ < (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) :=
          mul_lt_mul_of_pos_right (by norm_num) (zpow_pos (by norm_num) _)
  rcases le_total y (1 / 2) with hy_half | hy_half
  · have h1 := erfcScaled_alphaSchedule_lt_quarter p_work hp (y + 1 / 2) (by linarith)
    have h2 := (erfcScaled_alphaSchedule_lt_of_ge_one p_work hp (3 / 2 - y) (by linarith)).2
    linarith
  · have h1 := (erfcScaled_alphaSchedule_lt_of_ge_one p_work hp (y + 1 / 2) (by linarith)).2
    have h2 := erfcScaled_alphaSchedule_lt_quarter p_work hp (3 / 2 - y) (by linarith)
    linarith

/-- Strict positivity of the Box-Gaussian passband `gHatBox (realErfScaled α) ξ` for `α > 0` and all `ξ : ℝ`. -/
theorem gHatBox_realErfScaled_pos (α ξ : ℝ) (hα : 0 < α) :
    0 < gHatBox (realErfScaled α) ξ := by
  rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α ξ 0).1]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) :=
    Real.continuous_exp.comp (continuous_pow 2).neg
  have hab : Real.sqrt Real.pi * α * (ξ - 1 / 2) < Real.sqrt Real.pi * α * (ξ + 1 / 2) := by
    have hc : 0 < Real.sqrt Real.pi * α := mul_pos hsqrt_pi hα
    linarith
  have hint := intervalIntegral.intervalIntegral_pos_of_pos
    (hcont.intervalIntegrable _ _) (fun t => Real.exp_pos _) hab
  exact mul_pos (div_pos one_pos hsqrt_pi) hint

/-- Strict positivity of the primary passband coefficient `c0Coeff (realErfScaled α) y` for `α > 0`. -/
theorem c0Coeff_realErfScaled_pos (α y : ℝ) (hα : 0 < α) :
    0 < c0Coeff (realErfScaled α) y :=
  gHatBox_realErfScaled_pos α y hα

/-- Strict positivity of the secondary passband coefficient `c1Coeff (realErfScaled α) y` for `α > 0`. -/
theorem c1Coeff_realErfScaled_pos (α y : ℝ) (hα : 0 < α) :
    0 < c1Coeff (realErfScaled α) y :=
  gHatBox_realErfScaled_pos α (1 - y) hα

/-- For `α > 0` and `0 ≤ y < 1 / 2`, the primary passband coefficient strictly dominates the
secondary passband coefficient: `c1Coeff (realErfScaled α) y < c0Coeff (realErfScaled α) y`. -/
theorem c1Coeff_lt_c0Coeff_of_lt_half (α y : ℝ) (hα : 0 < α) (hy0 : 0 ≤ y) (hy_half : y < 1 / 2) :
    c1Coeff (realErfScaled α) y < c0Coeff (realErfScaled α) y := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  set c := Real.sqrt Real.pi * α
  have hc : 0 < c := mul_pos hsqrt_pi hα
  set a := c * (y - 1 / 2)
  set b := c * (1 / 2 - y)
  have hab : a < b := by
    dsimp [a, b]
    nlinarith
  let f : ℝ → ℝ := fun t => Real.exp (-(t ^ 2))
  have hcont : Continuous f := Real.continuous_exp.comp (continuous_pow 2).neg
  have hc0 : c0Coeff (realErfScaled α) y = (1 / Real.sqrt Real.pi) * ∫ t in a..(a + c), f t := by
    unfold c0Coeff
    rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α y 0).1]
    have ha_c : c * (y + 1 / 2) = a + c := by dsimp [a]; ring
    rw [ha_c]
  have hc1 : c1Coeff (realErfScaled α) y = (1 / Real.sqrt Real.pi) * ∫ t in b..(b + c), f t := by
    unfold c1Coeff
    rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α (1 - y) 0).1]
    have hb_eq : c * (1 - y - 1 / 2) = b := by dsimp [b]; ring
    have hb_c : c * (1 - y + 1 / 2) = b + c := by dsimp [b]; ring
    rw [hb_eq, hb_c]
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) b (a + c))
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) b (a + c))
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (a + c) (b + c))
  have hdiff_int : (∫ t in a..(a + c), f t) - (∫ t in b..(b + c), f t) =
      (∫ t in a..b, f t) - (∫ t in (a + c)..(b + c), f t) := by
    linarith
  have hshift : (∫ t in a..b, f (t + c)) = ∫ t in (a + c)..(b + c), f t :=
    intervalIntegral.integral_comp_add_right f c
  have hcont_shift : Continuous (fun t : ℝ => f (t + c)) :=
    hcont.comp (continuous_id.add continuous_const)
  have hsub_int : (∫ t in a..b, f t) - (∫ t in a..b, f (t + c)) =
      ∫ t in a..b, (f t - f (t + c)) :=
    (intervalIntegral.integral_sub (hcont.intervalIntegrable a b)
      (hcont_shift.intervalIntegrable a b)).symm
  have hint_pos : 0 < ∫ t in a..b, (f t - f (t + c)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hcont.sub hcont_shift).intervalIntegrable a b) (fun t ht => ?_) hab
    dsimp [f]
    rw [sub_pos]
    refine Real.exp_lt_exp.mpr ?_
    have ht_gt : a < t := ht.1
    have h2a_c : 0 ≤ 2 * a + c := by
      dsimp [a]
      nlinarith
    have hsq_lt : t ^ 2 < (t + c) ^ 2 := by
      nlinarith
    linarith
  have hpos_diff : 0 < c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y := by
    rw [hc0, hc1, ← mul_sub, hdiff_int, ← hshift, hsub_int]
    exact mul_pos (div_pos one_pos hsqrt_pi) hint_pos
  linarith

/-- By symmetry (`y ↦ 1 - y`), for `α > 0` and `1 / 2 < y ≤ 1`,
`c0Coeff (realErfScaled α) y < c1Coeff (realErfScaled α) y`. -/
theorem c0Coeff_lt_c1Coeff_of_gt_half (α y : ℝ) (hα : 0 < α) (hy_half : 1 / 2 < y) (hy1 : y ≤ 1) :
    c0Coeff (realErfScaled α) y < c1Coeff (realErfScaled α) y := by
  have h := c1Coeff_lt_c0Coeff_of_lt_half α (1 - y) hα (by linarith) (by linarith)
  unfold c0Coeff c1Coeff at h ⊢
  have h1 : 1 - (1 - y) = y := by ring
  rwa [h1] at h

/-- Off the Nyquist frequency (`y ≠ 1 / 2`) on `[0, 1]`, `c0Coeff` and `c1Coeff` are distinct:
`c0Coeff (realErfScaled α) y ≠ c1Coeff (realErfScaled α) y`. -/
theorem c0Coeff_ne_c1Coeff_of_ne_half (α y : ℝ) (hα : 0 < α)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hne : y ≠ 1 / 2) :
    c0Coeff (realErfScaled α) y ≠ c1Coeff (realErfScaled α) y := by
  rcases lt_trichotomy y (1 / 2) with hlt | rfl | hgt
  · exact (c1Coeff_lt_c0Coeff_of_lt_half α y hα hy0 hlt).ne'
  · exact absurd rfl hne
  · exact (c0Coeff_lt_c1Coeff_of_gt_half α y hα hgt hy1).ne

/-- Strict positivity of `alphaSchedule p_work` for `0 < p_work`. -/
theorem alphaSchedule_pos (p_work : ℕ) (hp : 0 < p_work) :
    0 < alphaSchedule p_work := by
  unfold alphaSchedule
  have hp_pos : (0 : ℝ) < (p_work : ℝ) := Nat.cast_pos.mpr hp
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos hp_pos hlog2_pos) Real.pi_pos
  exact mul_pos zero_lt_two (Real.sqrt_pos.mpr hrad_pos)

/-- For `α > 0` and `0 ≤ y ≤ 1 / 2`, `c1Coeff (realErfScaled α) y ≤ c0Coeff (realErfScaled α) y`. -/
theorem c1Coeff_le_c0Coeff_of_le_half (α y : ℝ) (hα : 0 < α)
    (hy0 : 0 ≤ y) (hy_half : y ≤ 1 / 2) :
    c1Coeff (realErfScaled α) y ≤ c0Coeff (realErfScaled α) y := by
  rcases lt_or_eq_of_le hy_half with hlt | rfl
  · exact (c1Coeff_lt_c0Coeff_of_lt_half α y hα hy0 hlt).le
  · have h := theorem3_nyquist_passband_eq (realErfScaled α) (realErfScaled_zero α)
    linarith

/-- For `α > 0` and `1 / 2 ≤ y ≤ 1`, `c0Coeff (realErfScaled α) y ≤ c1Coeff (realErfScaled α) y`. -/
theorem c0Coeff_le_c1Coeff_of_ge_half (α y : ℝ) (hα : 0 < α)
    (hy_half : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    c0Coeff (realErfScaled α) y ≤ c1Coeff (realErfScaled α) y := by
  rcases lt_or_eq_of_le hy_half with hlt | h_eq
  · exact (c0Coeff_lt_c1Coeff_of_gt_half α y hα hlt hy1).le
  · subst h_eq
    have h := theorem3_nyquist_passband_eq (realErfScaled α) (realErfScaled_zero α)
    linarith

/-- **Concrete Passband Sum Lower Bound (`c_0(y) + c_1(y) > 1 - 0.15 * 2^{-p_work}`, `[MS]` §5.1, eqs. (20)–(21))**:
For `p_work ≥ 8` and `y ∈ [0, 1]`, the sum of the two passband coefficients exceeds
`1 - 0.15 * 2^{-p_work}`. -/
theorem c0_add_c1_alphaSchedule_gt
    (p_work : ℕ) (hp : 8 ≤ p_work) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) <
      c0Coeff (realErfScaled (alphaSchedule p_work)) y +
      c1Coeff (realErfScaled (alphaSchedule p_work)) y := by
  have h := theorem3_stopband_alias_bound_alphaSchedule p_work hp y hy0 hy1
  linarith

/-- Monotonicity of `c0Coeff (realErfScaled α)` toward Nyquist: for `α > 0` and `0 ≤ y ≤ 1 / 2`,
`c0Coeff (realErfScaled α) (1 / 2) ≤ c0Coeff (realErfScaled α) y`. -/
theorem c0Coeff_ge_at_half (α y : ℝ) (hα : 0 < α) (hy0 : 0 ≤ y) (hy_half : y ≤ 1 / 2) :
    c0Coeff (realErfScaled α) (1 / 2) ≤ c0Coeff (realErfScaled α) y := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  set c := Real.sqrt Real.pi * α
  have hc : 0 < c := mul_pos hsqrt_pi hα
  set a := c * (y - 1 / 2)
  have ha_nonpos : a ≤ 0 := by
    dsimp [a]
    nlinarith
  let f : ℝ → ℝ := fun t => Real.exp (-(t ^ 2))
  let g : ℝ → ℝ := fun t => f t - f (t + c)
  have hcont_f : Continuous f := Real.continuous_exp.comp (continuous_pow 2).neg
  have hcont_shift : Continuous (fun t : ℝ => f (t + c)) :=
    hcont_f.comp (continuous_id.add continuous_const)
  have hcont_g : Continuous g := hcont_f.sub hcont_shift
  have hc0_y : c0Coeff (realErfScaled α) y = (1 / Real.sqrt Real.pi) * ∫ t in a..(a + c), f t := by
    unfold c0Coeff
    rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α y 0).1]
    have ha_c : c * (y + 1 / 2) = a + c := by dsimp [a]; ring
    rw [ha_c]
  have hc0_half : c0Coeff (realErfScaled α) (1 / 2) = (1 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..c, f t := by
    unfold c0Coeff
    rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α (1 / 2) 0).1]
    have h0 : c * (1 / 2 - 1 / 2) = 0 := by ring
    have hc_eq : c * (1 / 2 + 1 / 2) = c := by ring
    rw [h0, hc_eq]
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) a 0)
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) 0 (a + c))
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) 0 (a + c))
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) (a + c) c)
  have hdiff_int : (∫ t in a..(a + c), f t) - (∫ t in (0 : ℝ)..c, f t) =
      (∫ t in a..0, f t) - (∫ t in (a + c)..c, f t) := by
    linarith
  have hshift : (∫ t in a..0, f (t + c)) = ∫ t in (a + c)..c, f t := by
    simpa only [zero_add] using intervalIntegral.integral_comp_add_right f c (a := a) (b := 0)
  have hsub_int : (∫ t in a..0, f t) - (∫ t in a..0, f (t + c)) = ∫ t in a..0, g t :=
    (intervalIntegral.integral_sub (hcont_f.intervalIntegrable a 0)
      (hcont_shift.intervalIntegrable a 0)).symm
  have hg_nonneg : ∀ t : ℝ, a ≤ t → 0 ≤ g t := by
    intro t ht
    dsimp [g, f]
    rw [sub_nonneg]
    refine Real.exp_le_exp.mpr ?_
    have h2a_c : 0 ≤ 2 * a + c := by
      have : 2 * a + c = 2 * c * y := by dsimp [a]; ring
      rw [this]
      exact mul_nonneg (by linarith) hy0
    have hsq_sub : (t + c) ^ 2 - t ^ 2 = c * (2 * (t - a) + (2 * a + c)) := by ring
    have hprod_nonneg : 0 ≤ c * (2 * (t - a) + (2 * a + c)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hint_nonneg : 0 ≤ ∫ t in a..0, g t :=
    intervalIntegral.integral_nonneg ha_nonpos (fun t ht => hg_nonneg t ht.1)
  have hdiff_nonneg : 0 ≤ c0Coeff (realErfScaled α) y - c0Coeff (realErfScaled α) (1 / 2) := by
    rw [hc0_y, hc0_half, ← mul_sub, hdiff_int, ← hshift, hsub_int]
    exact mul_nonneg (by positivity) hint_nonneg
  linarith

/-- For `0 ≤ y ≤ 1 / 2` and `8 ≤ p_work`, the primary passband coefficient satisfies
`0.49999999 < c0Coeff (realErfScaled (alphaSchedule p_work)) y`. -/
theorem c0Coeff_alphaSchedule_gt_049999999
    (p_work : ℕ) (hp : 8 ≤ p_work) (y : ℝ) (hy0 : 0 ≤ y) (hy_half : y ≤ 1 / 2) :
    (0.49999999 : ℝ) < c0Coeff (realErfScaled (alphaSchedule p_work)) y := by
  set α := alphaSchedule p_work
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  have hmono := c0Coeff_ge_at_half α y hα hy0 hy_half
  have hnyq := theorem3_nyquist_passband_eq (realErfScaled α) (realErfScaled_zero α)
  have htele := theorem3_telescoping_stopband_alias (realErfScaled α) (realErfScaled_neg α) (1 / 2)
  have h1 : (1 / 2 : ℝ) + 1 / 2 = 1 := by ring
  have h2 : (3 / 2 : ℝ) - 1 / 2 = 1 := by ring
  have hc1_eq : c1Coeff (realErfScaled α) (1 / 2) = c0Coeff (realErfScaled α) (1 / 2) :=
    hnyq.2.trans hnyq.1.symm
  rw [h1, h2, hc1_eq] at htele
  have herfc := (erfcScaled_alphaSchedule_lt_of_ge_one p_work hp 1 le_rfl).1
  have hzpow : (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-32 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h_bound :
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ)) ≤
        (1 / 34359738368 : ℝ) := by
    calc (1 / 8 : ℝ) * (2 : ℝ) ^ (-((4 * p_work : ℕ) : ℤ))
        ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-32 : ℤ) := mul_le_mul_of_nonneg_left hzpow (by norm_num)
      _ = (1 / 34359738368 : ℝ) := by norm_num
  have h_erfc_lt : erfcScaled (realErfScaled α) 1 < (1 / 34359738368 : ℝ) :=
    herfc.trans_le h_bound
  have h_c0_half : (0.49999999 : ℝ) < c0Coeff (realErfScaled α) (1 / 2) := by
    linarith
  exact h_c0_half.trans_le hmono

/-- For `1 / 2 ≤ y ≤ 1` and `8 ≤ p_work`, the secondary passband coefficient satisfies
`0.49999999 < c1Coeff (realErfScaled (alphaSchedule p_work)) y`. -/
theorem c1Coeff_alphaSchedule_gt_049999999
    (p_work : ℕ) (hp : 8 ≤ p_work) (y : ℝ) (hy_half : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    (0.49999999 : ℝ) < c1Coeff (realErfScaled (alphaSchedule p_work)) y := by
  unfold c1Coeff
  exact c0Coeff_alphaSchedule_gt_049999999 p_work hp (1 - y) (by linarith) (by linarith)

/-- **Concrete Dominant Passband Lower Bound (`max(c_0(y), c_1(y)) > 0.49999999`, `[MS]` §5.1, eq. (20))**:
For `p_work ≥ 8` and `y ∈ [0, 1]`, the dominant passband coefficient
`M(y) = max(c_0(y), c_1(y))` satisfies strictly `0.49999999 < M(y)`. -/
theorem max_c0_c1_alphaSchedule_gt_049999999
    (p_work : ℕ) (hp : 8 ≤ p_work) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (0.49999999 : ℝ) <
      max (c0Coeff (realErfScaled (alphaSchedule p_work)) y)
          (c1Coeff (realErfScaled (alphaSchedule p_work)) y) := by
  rcases le_total y (1 / 2) with hy_half | hy_half
  · exact (c0Coeff_alphaSchedule_gt_049999999 p_work hp y hy0 hy_half).trans_le (le_max_left _ _)
  · exact (c1Coeff_alphaSchedule_gt_049999999 p_work hp y hy_half hy1).trans_le (le_max_right _ _)

/-- **Global Upper Bound `realErf b - realErf a ≤ 2` for `a ≤ b`**:
Since `∫_{a}^{b} exp(-t^2) dt = ∫_{t ∈ Ioc a b} exp(-t^2) dt ≤ ∫_{t ∈ ℝ} exp(-t^2) dt = √π`,
multiplying by `2 / √π` proves `realErf b - realErf a ≤ 2` for all `a ≤ b`. -/
theorem realErf_sub_le_two (a b : ℝ) (hab : a ≤ b) :
    realErf b - realErf a ≤ 2 := by
  unfold realErf
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) :=
    Real.continuous_exp.comp (continuous_pow 2).neg
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 a)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) a b)
  have hsub : (∫ t in (0 : ℝ)..b, Real.exp (-(t ^ 2))) - (∫ t in (0 : ℝ)..a, Real.exp (-(t ^ 2))) =
      ∫ t in a..b, Real.exp (-(t ^ 2)) := by
    linarith
  rw [← mul_sub, hsub, intervalIntegral.integral_of_le hab]
  have hint : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq one_pos
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume] (fun t : ℝ => Real.exp (-(t ^ 2))) :=
    Filter.Eventually.of_forall fun t => (Real.exp_pos _).le
  have hle_int : (∫ t in Set.Ioc a b, Real.exp (-(t ^ 2))) ≤ ∫ t : ℝ, Real.exp (-(t ^ 2)) :=
    MeasureTheory.setIntegral_le_integral hint hnonneg
  have hgauss : (∫ t : ℝ, Real.exp (-(t ^ 2))) = Real.sqrt Real.pi := by
    simpa only [neg_one_mul, div_one] using integral_gaussian (1 : ℝ)
  rw [hgauss] at hle_int
  calc (2 / Real.sqrt Real.pi) * ∫ t in Set.Ioc a b, Real.exp (-(t ^ 2))
      ≤ (2 / Real.sqrt Real.pi) * Real.sqrt Real.pi :=
        mul_le_mul_of_nonneg_left hle_int (div_nonneg zero_le_two hsqrt_pi.le)
    _ = 2 := div_mul_cancel₀ 2 hsqrt_pi.ne'

/-- For any `α ≥ 0` and `a ≤ b`, `realErfScaled α b - realErfScaled α a ≤ 2`. -/
theorem realErfScaled_sub_le_two (α a b : ℝ) (hα : 0 ≤ α) (hab : a ≤ b) :
    realErfScaled α b - realErfScaled α a ≤ 2 := by
  unfold realErfScaled
  have hc : 0 ≤ Real.sqrt Real.pi * α := mul_nonneg (Real.sqrt_nonneg _) hα
  exact realErf_sub_le_two _ _ (mul_le_mul_of_nonneg_left hab hc)

/-- Telescoping sum of `gHatBox` over `[a, a + n] ⊂ ℤ` (`n : ℕ`). -/
theorem gHatBox_telescoping_sum_Icc_nat (erfScaled : ℝ → ℝ) (y : ℝ) (a : ℤ) (n : ℕ) :
    ∑ m ∈ Finset.Icc a (a + (n : ℤ)), gHatBox erfScaled (y - (m : ℝ)) =
      (1 / 2 : ℝ) * (erfScaled (y - (a : ℝ) + 1 / 2) -
        erfScaled (y - ((a + (n : ℤ) : ℤ) : ℝ) - 1 / 2)) := by
  induction n with
  | zero =>
    simp [gHatBox]
  | succ n ih =>
    have hstep : a + ((n + 1 : ℕ) : ℤ) = (a + (n : ℤ)) + 1 := by omega
    rw [hstep, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
        Finset.sum_insert (by simp), ih]
    unfold gHatBox
    push_cast
    ring

/-- **`[MS]` Theorem 5.1 (Telescoping Sum of `gHatBox` over any Integer Interval `[a, b]`, `[MS]` §5.1)**:
For any `a ≤ b` in `ℤ`,
`∑_{m = a}^{b} gHatBox(y - m) = (1/2) (erfScaled(y - a + 1/2) - erfScaled(y - b - 1/2))`. -/
theorem theorem3_gHatBox_telescoping_sum (erfScaled : ℝ → ℝ) (y : ℝ) (a b : ℤ) (hab : a ≤ b) :
    ∑ m ∈ Finset.Icc a b, gHatBox erfScaled (y - (m : ℝ)) =
      (1 / 2 : ℝ) * (erfScaled (y - (a : ℝ) + 1 / 2) - erfScaled (y - (b : ℝ) - 1 / 2)) := by
  have hb_eq : b = a + ((b - a).toNat : ℤ) := by omega
  conv_lhs => rw [hb_eq]
  rw [gHatBox_telescoping_sum_Icc_nat, ← hb_eq]

/-- For `α > 0` and any `a ≤ b` in `ℤ`, the sum of `gHatBox (realErfScaled α) (y - m)` over
`Finset.Icc a b` is at most `1`. -/
theorem sum_Icc_gHatBox_realErfScaled_le_one (α y : ℝ) (hα : 0 < α) (a b : ℤ) (hab : a ≤ b) :
    ∑ m ∈ Finset.Icc a b, gHatBox (realErfScaled α) (y - (m : ℝ)) ≤ 1 := by
  rw [theorem3_gHatBox_telescoping_sum (realErfScaled α) y a b hab]
  have hab_real : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hsub := realErfScaled_sub_le_two α (y - (b : ℝ) - 1 / 2) (y - (a : ℝ) + 1 / 2)
    hα.le (by linarith)
  linarith

/-- Every finite sum `∑ m ∈ s, gHatBox (realErfScaled α) (y - m)` over `s : Finset ℤ` is `≤ 1`. -/
theorem sum_finset_gHatBox_realErfScaled_le_one (α y : ℝ) (hα : 0 < α) (s : Finset ℤ) :
    ∑ m ∈ s, gHatBox (realErfScaled α) (y - (m : ℝ)) ≤ 1 := by
  let N : ℕ := s.sup Int.natAbs
  have hsub : s ⊆ Finset.Icc (-(N : ℤ)) ((N : ℤ) + 1) := by
    intro m hm
    have hle : m.natAbs ≤ N := Finset.le_sup hm
    rw [Finset.mem_Icc]
    omega
  have hnonneg : ∀ m ∈ Finset.Icc (-(N : ℤ)) ((N : ℤ) + 1), m ∉ s →
      0 ≤ gHatBox (realErfScaled α) (y - (m : ℝ)) :=
    fun m _ _ => (gHatBox_realErfScaled_pos α (y - (m : ℝ)) hα).le
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg).trans
    (sum_Icc_gHatBox_realErfScaled_le_one α y hα (-(N : ℤ)) ((N : ℤ) + 1) (by omega))

/-- **Unconditional Summability of `gHatBox (realErfScaled α)` over `ℤ` (`[MS]` §5.1)**:
For any `α > 0` and `y : ℝ`, `m ↦ gHatBox (realErfScaled α) (y - m)` is summable over `ℤ`. -/
theorem summable_gHatBox_realErfScaled (α y : ℝ) (hα : 0 < α) :
    Summable (fun m : ℤ => gHatBox (realErfScaled α) (y - (m : ℝ))) :=
  summable_of_sum_le (fun m => (gHatBox_realErfScaled_pos α (y - (m : ℝ)) hα).le)
    (sum_finset_gHatBox_realErfScaled_le_one α y hα)

/-- Stopband indicator of `gHatBox (realErfScaled α)`: vanishes on the 2-term passband `m ∈ {0, 1}`
and equals `gHatBox (realErfScaled α) (y - m)` for all stopband modes `m ∉ {0, 1}`. -/
noncomputable def stopbandGHatBox (α y : ℝ) (m : ℤ) : ℝ :=
  if m = 0 ∨ m = 1 then 0 else gHatBox (realErfScaled α) (y - (m : ℝ))

/-- Non-negativity of `stopbandGHatBox α y m` for `α > 0`. -/
theorem stopbandGHatBox_nonneg (α y : ℝ) (hα : 0 < α) (m : ℤ) :
    0 ≤ stopbandGHatBox α y m := by
  unfold stopbandGHatBox
  split_ifs
  · exact le_rfl
  · exact (gHatBox_realErfScaled_pos α (y - (m : ℝ)) hα).le

/-- Pointwise decomposition of `gHatBox (realErfScaled α) (y - m)` into the stopband indicator
`stopbandGHatBox α y m` and the two passband modes `m = 0` (`c0Coeff`) and `m = 1` (`c1Coeff`). -/
theorem stopbandGHatBox_add_passband_eq (α y : ℝ) (m : ℤ) :
    stopbandGHatBox α y m +
      (if m = 0 then c0Coeff (realErfScaled α) y else 0) +
      (if m = 1 then c1Coeff (realErfScaled α) y else 0) =
    gHatBox (realErfScaled α) (y - (m : ℝ)) := by
  unfold stopbandGHatBox c0Coeff c1Coeff
  by_cases hm0 : m = 0
  · subst hm0
    simp
  · by_cases hm1 : m = 1
    · subst hm1
      simp only [hm0, or_true, ↓reduceIte, zero_add, Int.cast_one]
      have heven := gHatBox_even (realErfScaled α) (realErfScaled_neg α) (1 - y)
      have hneg : -(1 - y) = y - 1 := by ring
      rw [hneg] at heven
      exact heven.symm
    · simp [hm0, hm1]

/-- Every finite sum of `stopbandGHatBox α y` over `s : Finset ℤ` is bounded above by
`1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y`. -/
theorem sum_finset_stopbandGHatBox_le (α y : ℝ) (hα : 0 < α) (s : Finset ℤ) :
    ∑ m ∈ s, stopbandGHatBox α y m ≤
      1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y := by
  let N : ℕ := s.sup Int.natAbs
  let I : Finset ℤ := Finset.Icc (-(N : ℤ)) ((N : ℤ) + 1)
  have hsub : s ⊆ I := by
    intro m hm
    have hle : m.natAbs ≤ N := Finset.le_sup hm
    rw [Finset.mem_Icc]
    omega
  have h0_mem : (0 : ℤ) ∈ I := by
    rw [Finset.mem_Icc]
    omega
  have h1_mem : (1 : ℤ) ∈ I := by
    rw [Finset.mem_Icc]
    omega
  have hle_I : ∑ m ∈ s, stopbandGHatBox α y m ≤ ∑ m ∈ I, stopbandGHatBox α y m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => stopbandGHatBox_nonneg α y hα m
  have hsum_I :
      (∑ m ∈ I, stopbandGHatBox α y m) +
        c0Coeff (realErfScaled α) y + c1Coeff (realErfScaled α) y =
      ∑ m ∈ I, gHatBox (realErfScaled α) (y - (m : ℝ)) := by
    have hcongr :
        ∑ m ∈ I, gHatBox (realErfScaled α) (y - (m : ℝ)) =
        ∑ m ∈ I, (stopbandGHatBox α y m +
          (if m = 0 then c0Coeff (realErfScaled α) y else 0) +
          (if m = 1 then c1Coeff (realErfScaled α) y else 0)) :=
      Finset.sum_congr rfl fun m _ => (stopbandGHatBox_add_passband_eq α y m).symm
    rw [hcongr, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq' I (0 : ℤ), if_pos h0_mem,
        Finset.sum_ite_eq' I (1 : ℤ), if_pos h1_mem]
  have hI_le_one : ∑ m ∈ I, gHatBox (realErfScaled α) (y - (m : ℝ)) ≤ 1 :=
    sum_Icc_gHatBox_realErfScaled_le_one α y hα (-(N : ℤ)) ((N : ℤ) + 1) (by omega)
  linarith

/-- Unconditional summability of `stopbandGHatBox α y` over `ℤ` for `α > 0`. -/
theorem summable_stopbandGHatBox (α y : ℝ) (hα : 0 < α) :
    Summable (stopbandGHatBox α y) :=
  summable_of_sum_le (stopbandGHatBox_nonneg α y hα) (sum_finset_stopbandGHatBox_le α y hα)

/-- **Infinite-Series Stopband Alias Upper Bound (`[MS]` §5.1, eq. (21))**:
For `α > 0` and `y : ℝ`, the infinite sum of `stopbandGHatBox α y m` over all `m ∈ ℤ` satisfies:
`∑' m : ℤ, stopbandGHatBox α y m ≤ 1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y`. -/
theorem tsum_stopbandGHatBox_le (α y : ℝ) (hα : 0 < α) :
    (∑' m : ℤ, stopbandGHatBox α y m) ≤
      1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y :=
  (summable_stopbandGHatBox α y hα).tsum_le_of_sum_le (sum_finset_stopbandGHatBox_le α y hα)

/-- For `8 ≤ p_work`, the scaled passband width `c = √π * alphaSchedule p_work` satisfies `4.7 ≤ c`. -/
theorem sqrt_pi_mul_alphaSchedule_ge_47 (p_work : ℕ) (hp : 8 ≤ p_work) :
    (4.7 : ℝ) ≤ Real.sqrt Real.pi * alphaSchedule p_work := by
  have hp_real : (8 : ℝ) ≤ (p_work : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p_work : ℝ) := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_pos : 0 < Real.log 2 := by linarith
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos hp_pos hlog2_pos) hpi
  have hα : 0 < alphaSchedule p_work := alphaSchedule_pos p_work (by omega)
  have hc_pos : 0 < Real.sqrt Real.pi * alphaSchedule p_work := mul_pos hsqrt_pi hα
  have hsq : (Real.sqrt Real.pi * alphaSchedule p_work) ^ 2 = 4 * (p_work : ℝ) * Real.log 2 := by
    unfold alphaSchedule
    calc (Real.sqrt Real.pi * (2 * Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi))) ^ 2
        = (Real.sqrt Real.pi) ^ 2 * 4 * (Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi)) ^ 2 := by ring
      _ = Real.pi * 4 * ((p_work : ℝ) * Real.log 2 / Real.pi) := by
          rw [Real.sq_sqrt hpi.le, Real.sq_sqrt hrad_pos.le]
      _ = 4 * (p_work : ℝ) * Real.log 2 := by field_simp [hpi.ne']
  have h47 : (4.7 : ℝ) ^ 2 ≤ (Real.sqrt Real.pi * alphaSchedule p_work) ^ 2 := by
    rw [hsq]
    nlinarith
  by_contra! hlt
  nlinarith

/-- For `24 ≤ p_work`, the scaled passband width `c = √π * alphaSchedule p_work` satisfies `8 ≤ c`. -/
theorem sqrt_pi_mul_alphaSchedule_ge_eight (p_work : ℕ) (hp : 24 ≤ p_work) :
    (8 : ℝ) ≤ Real.sqrt Real.pi * alphaSchedule p_work := by
  have hp_real : (24 : ℝ) ≤ (p_work : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p_work : ℝ) := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_pos : 0 < Real.log 2 := by linarith
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos hp_pos hlog2_pos) hpi
  have hα : 0 < alphaSchedule p_work := alphaSchedule_pos p_work (by omega)
  have hc_pos : 0 < Real.sqrt Real.pi * alphaSchedule p_work := mul_pos hsqrt_pi hα
  have hsq : (Real.sqrt Real.pi * alphaSchedule p_work) ^ 2 = 4 * (p_work : ℝ) * Real.log 2 := by
    unfold alphaSchedule
    calc (Real.sqrt Real.pi * (2 * Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi))) ^ 2
        = (Real.sqrt Real.pi) ^ 2 * 4 * (Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi)) ^ 2 := by ring
      _ = Real.pi * 4 * ((p_work : ℝ) * Real.log 2 / Real.pi) := by
          rw [Real.sq_sqrt hpi.le, Real.sq_sqrt hrad_pos.le]
      _ = 4 * (p_work : ℝ) * Real.log 2 := by field_simp [hpi.ne']
  have h64 : (8 : ℝ) ^ 2 ≤ (Real.sqrt Real.pi * alphaSchedule p_work) ^ 2 := by
    rw [hsq]
    nlinarith
  by_contra! hlt
  nlinarith

/-- For any `α > 0` and `y : ℝ`, the sum of the two passband coefficients is at most `1`:
`c0Coeff (realErfScaled α) y + c1Coeff (realErfScaled α) y ≤ 1`. -/
theorem c0_add_c1_realErfScaled_le_one (α y : ℝ) (hα : 0 < α) :
    c0Coeff (realErfScaled α) y + c1Coeff (realErfScaled α) y ≤ 1 := by
  have h := sum_finset_stopbandGHatBox_le α y hα ∅
  simp at h
  linarith

/-- Pointwise polynomial lower bound on `exp(-t^2) - exp(-(t + c)^2)` for `t ∈ [-1, 1]` and `c ≥ 4.7`:
`0.995 - t^2 + t^4 / 4 ≤ exp(-t^2) - exp(-(t + c)^2)`. -/
theorem poly_le_exp_sub_exp_shift_47 (t c : ℝ) (hc : (4.7 : ℝ) ≤ c) (ht1 : -1 ≤ t) (ht2 : t ≤ 1) :
    (0.995 : ℝ) - t ^ 2 + t ^ 4 / 4 ≤ Real.exp (-(t ^ 2)) - Real.exp (-((t + c) ^ 2)) := by
  have htsq : t ^ 2 ≤ 1 := by nlinarith
  have hexp_half : 1 - t ^ 2 / 2 ≤ Real.exp (-(t ^ 2 / 2)) := by
    have h := Real.add_one_le_exp (-(t ^ 2 / 2))
    linarith
  have hexp_t : 1 - t ^ 2 + t ^ 4 / 4 ≤ Real.exp (-(t ^ 2)) := by
    have hsplit : -(t ^ 2) = -(t ^ 2 / 2) + -(t ^ 2 / 2) := by ring
    rw [hsplit, Real.exp_add]
    have hnonneg : 0 ≤ 1 - t ^ 2 / 2 := by linarith
    have hmul : (1 - t ^ 2 / 2) * (1 - t ^ 2 / 2) ≤
        Real.exp (-(t ^ 2 / 2)) * Real.exp (-(t ^ 2 / 2)) :=
      mul_le_mul hexp_half hexp_half hnonneg (Real.exp_pos _).le
    have hsq : (1 - t ^ 2 / 2) * (1 - t ^ 2 / 2) = 1 - t ^ 2 + t ^ 4 / 4 := by ring
    linarith
  have hexp3 : (4 : ℝ) ≤ Real.exp 3 := by
    have h := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hexp6 : (16 : ℝ) ≤ Real.exp 6 := by
    have h6 : (6 : ℝ) = 3 + 3 := by ring
    rw [h6, Real.exp_add]
    nlinarith [Real.exp_pos 3]
  have hexp12 : (200 : ℝ) ≤ Real.exp 12 := by
    have h12 : (12 : ℝ) = 6 + 6 := by ring
    rw [h12, Real.exp_add]
    nlinarith [Real.exp_pos 6]
  have htc_sq : (12 : ℝ) ≤ (t + c) ^ 2 := by nlinarith
  have hexp_tc_ge : (200 : ℝ) ≤ Real.exp ((t + c) ^ 2) :=
    hexp12.trans (Real.exp_le_exp.mpr htc_sq)
  have hexp_prod : Real.exp (-((t + c) ^ 2)) * Real.exp ((t + c) ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hexp_tc_pos : 0 ≤ Real.exp (-((t + c) ^ 2)) := (Real.exp_pos _).le
  have hexp_tc_le : Real.exp (-((t + c) ^ 2)) ≤ (0.005 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hexp_tc_ge hexp_tc_pos
    linarith
  linarith

/-- Pointwise polynomial lower bound on `exp(-t^2) - exp(-(t + c)^2)` for `t ∈ [-1, 1]` and `c ≥ 8`:
`0.98 - t^2 + t^4 / 4 ≤ exp(-t^2) - exp(-(t + c)^2)`. -/
theorem poly_le_exp_sub_exp_shift (t c : ℝ) (hc : (8 : ℝ) ≤ c) (ht1 : -1 ≤ t) (ht2 : t ≤ 1) :
    (0.98 : ℝ) - t ^ 2 + t ^ 4 / 4 ≤ Real.exp (-(t ^ 2)) - Real.exp (-((t + c) ^ 2)) := by
  have h := poly_le_exp_sub_exp_shift_47 t c (by linarith) ht1 ht2
  linarith

/-- Quantitative passband gap lower bound for `4.7 ≤ √π * α` and `0 < δ ≤ 1`:
`0.78 * δ ≤ c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y`. -/
theorem c0_sub_c1_ge_of_delta_47 (α y δ : ℝ)
    (hc_ge : (4.7 : ℝ) ≤ Real.sqrt Real.pi * α)
    (hy0 : 0 ≤ y) (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ_b : δ ≤ (Real.sqrt Real.pi * α) * (1 / 2 - y)) :
    (0.78 : ℝ) * δ ≤ c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hsqrt_pi_lt : Real.sqrt Real.pi < (1.7725 : ℝ) := by
    by_contra! hge
    have hsq := Real.sq_sqrt hpi.le
    have hpi_lt : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
    nlinarith
  set c := Real.sqrt Real.pi * α
  set a := c * (y - 1 / 2)
  set b := c * (1 / 2 - y)
  have ha_eq : a = -b := by dsimp [a, b]; ring
  have ha_le_neg_δ : a ≤ -δ := by linarith
  have hneg_δ_le_δ : -δ ≤ δ := by linarith
  let f : ℝ → ℝ := fun t => Real.exp (-(t ^ 2))
  let g : ℝ → ℝ := fun t => f t - f (t + c)
  have hcont_f : Continuous f := Real.continuous_exp.comp (continuous_pow 2).neg
  have hcont_shift : Continuous (fun t : ℝ => f (t + c)) :=
    hcont_f.comp (continuous_id.add continuous_const)
  have hcont_g : Continuous g := hcont_f.sub hcont_shift
  have hc0 : c0Coeff (realErfScaled α) y = (1 / Real.sqrt Real.pi) * ∫ t in a..(a + c), f t := by
    unfold c0Coeff
    rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α y 0).1]
    have ha_c : c * (y + 1 / 2) = a + c := by dsimp [a]; ring
    rw [ha_c]
  have hc1 : c1Coeff (realErfScaled α) y = (1 / Real.sqrt Real.pi) * ∫ t in b..(b + c), f t := by
    unfold c1Coeff
    rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α (1 - y) 0).1]
    have hb_eq : c * (1 - y - 1 / 2) = b := by dsimp [b]; ring
    have hb_c : c * (1 - y + 1 / 2) = b + c := by dsimp [b]; ring
    rw [hb_eq, hb_c]
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) b (a + c))
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) b (a + c))
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) (a + c) (b + c))
  have hdiff_int : (∫ t in a..(a + c), f t) - (∫ t in b..(b + c), f t) =
      (∫ t in a..b, f t) - (∫ t in (a + c)..(b + c), f t) := by
    linarith
  have hshift : (∫ t in a..b, f (t + c)) = ∫ t in (a + c)..(b + c), f t :=
    intervalIntegral.integral_comp_add_right f c
  have hsub_int : (∫ t in a..b, f t) - (∫ t in a..b, f (t + c)) = ∫ t in a..b, g t :=
    (intervalIntegral.integral_sub (hcont_f.intervalIntegrable a b)
      (hcont_shift.intervalIntegrable a b)).symm
  have hg_nonneg : ∀ t : ℝ, a ≤ t → 0 ≤ g t := by
    intro t ht
    dsimp [g, f]
    rw [sub_nonneg]
    refine Real.exp_le_exp.mpr ?_
    have h2a_c : 0 ≤ 2 * a + c := by
      have : 2 * a + c = 2 * c * y := by dsimp [a]; ring
      rw [this]
      exact mul_nonneg (by linarith) hy0
    have hsq_sub : (t + c) ^ 2 - t ^ 2 = c * (2 * (t - a) + (2 * a + c)) := by ring
    have hprod_nonneg : 0 ≤ c * (2 * (t - a) + (2 * a + c)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hadj_g1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) a (-δ))
    (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) (-δ) δ)
  have hadj_g2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) a δ)
    (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) δ b)
  have hint_left_nonneg : 0 ≤ ∫ t in a..(-δ), g t :=
    intervalIntegral.integral_nonneg ha_le_neg_δ (fun t ht => hg_nonneg t ht.1)
  have hint_right_nonneg : 0 ≤ ∫ t in δ..b, g t :=
    intervalIntegral.integral_nonneg hδ_b (fun t ht => hg_nonneg t (by linarith [ht.1]))
  have hint_ge_mid : (∫ t in (-δ)..δ, g t) ≤ ∫ t in a..b, g t := by
    linarith
  let F : ℝ → ℝ := fun t => (0.98 : ℝ) * t - t ^ 3 / 3 + t ^ 5 / 20
  let F' : ℝ → ℝ := fun t => (0.98 : ℝ) - t ^ 2 + t ^ 4 / 4
  have hderiv : ∀ t ∈ Set.uIcc (-δ) δ, HasDerivAt F (F' t) t := by
    intro t _
    have hd1 : HasDerivAt (fun x : ℝ => (0.98 : ℝ) * x) ((0.98 : ℝ) * 1) t :=
      (hasDerivAt_id t).const_mul (0.98 : ℝ)
    have hd2 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (3 * t ^ 2 * 1 / 3) t :=
      ((hasDerivAt_id t).pow 3).div_const 3
    have hd3 : HasDerivAt (fun x : ℝ => x ^ 5 / 20) (5 * t ^ 4 * 1 / 20) t :=
      ((hasDerivAt_id t).pow 5).div_const 20
    refine ((hd1.sub hd2).add hd3).congr_deriv ?_
    dsimp [F']
    ring
  have hcont_F' : Continuous F' :=
    (continuous_const.sub (continuous_pow 2)).add ((continuous_pow 4).div_const 4)
  have hint_F' : IntervalIntegrable F' volume (-δ) δ := hcont_F'.intervalIntegrable (-δ) δ
  have hftc : (∫ t in (-δ)..δ, F' t) = F δ - F (-δ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_F'
  have hmono : (∫ t in (-δ)..δ, F' t) ≤ ∫ t in (-δ)..δ, g t := by
    refine intervalIntegral.integral_mono_on hneg_δ_le_δ hint_F'
      (hcont_g.intervalIntegrable (-δ) δ) fun t ht => ?_
    have h47 := poly_le_exp_sub_exp_shift_47 t c hc_ge (by linarith [ht.1]) (by linarith [ht.2])
    dsimp [F', g, f]
    linarith
  have hF_eval : (1.39 : ℝ) * δ ≤ F δ - F (-δ) := by
    have hδ2_le : δ ^ 2 ≤ 1 := by
      have := mul_le_mul hδ1 hδ1 hδ_pos.le zero_le_one
      linarith
    have hident : (F δ - F (-δ)) - (1.39 : ℝ) * δ =
        δ * ((1 - δ ^ 2) * (17 / 30 - 1 / 10 * δ ^ 2) + 1 / 300) := by
      dsimp [F]
      ring
    have hnonneg : 0 ≤ δ * ((1 - δ ^ 2) * (17 / 30 - 1 / 10 * δ ^ 2) + 1 / 300) :=
      mul_nonneg hδ_pos.le (add_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num))
    linarith
  have hint_ab_ge : (1.39 : ℝ) * δ ≤ ∫ t in a..b, g t := by linarith
  have hdiff_eq : c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y =
      (1 / Real.sqrt Real.pi) * ∫ t in a..b, g t := by
    rw [hc0, hc1, ← mul_sub, hdiff_int, ← hshift, hsub_int]
  have hmul_pi : (0.78 : ℝ) * δ * Real.sqrt Real.pi ≤ (0.78 : ℝ) * δ * (1.7725 : ℝ) :=
    mul_le_mul_of_nonneg_left hsqrt_pi_lt.le (by positivity)
  rw [hdiff_eq, one_div_mul_eq_div, le_div_iff₀ hsqrt_pi]
  linarith

/-- Quantitative passband gap lower bound: if `8 ≤ √π * α`, `0 ≤ y`, and `0 < δ ≤ 1` with
`δ ≤ (√π * α) * (1 / 2 - y)`, then `0.78 * δ ≤ c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y`. -/
theorem c0_sub_c1_ge_of_delta (α y δ : ℝ)
    (hc_ge : (8 : ℝ) ≤ Real.sqrt Real.pi * α)
    (hy0 : 0 ≤ y) (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ_b : δ ≤ (Real.sqrt Real.pi * α) * (1 / 2 - y)) :
    (0.78 : ℝ) * δ ≤ c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y :=
  c0_sub_c1_ge_of_delta_47 α y δ (by linarith) hy0 hδ_pos hδ1 hδ_b

/-- Sharper passband gap lower bound for small `0 < δ ≤ 0.4` and `4.7 ≤ √π * α`:
`1.062 * δ ≤ c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y`. -/
theorem c0_sub_c1_ge_of_delta_small (α y δ : ℝ)
    (hc_ge : (4.7 : ℝ) ≤ Real.sqrt Real.pi * α)
    (hy0 : 0 ≤ y) (hδ_pos : 0 < δ) (hδ04 : δ ≤ (0.4 : ℝ))
    (hδ_b : δ ≤ (Real.sqrt Real.pi * α) * (1 / 2 - y)) :
    (1.062 : ℝ) * δ ≤ c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hsqrt_pi_lt : Real.sqrt Real.pi < (1.7725 : ℝ) := by
    by_contra! hge
    have hsq := Real.sq_sqrt hpi.le
    have hpi_lt : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
    nlinarith
  set c := Real.sqrt Real.pi * α
  set a := c * (y - 1 / 2)
  set b := c * (1 / 2 - y)
  have ha_eq : a = -b := by dsimp [a, b]; ring
  have ha_le_neg_δ : a ≤ -δ := by linarith
  have hneg_δ_le_δ : -δ ≤ δ := by linarith
  let f : ℝ → ℝ := fun t => Real.exp (-(t ^ 2))
  let g : ℝ → ℝ := fun t => f t - f (t + c)
  have hcont_f : Continuous f := Real.continuous_exp.comp (continuous_pow 2).neg
  have hcont_shift : Continuous (fun t : ℝ => f (t + c)) :=
    hcont_f.comp (continuous_id.add continuous_const)
  have hcont_g : Continuous g := hcont_f.sub hcont_shift
  have hc0 : c0Coeff (realErfScaled α) y = (1 / Real.sqrt Real.pi) * ∫ t in a..(a + c), f t := by
    unfold c0Coeff
    rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α y 0).1]
    have ha_c : c * (y + 1 / 2) = a + c := by dsimp [a]; ring
    rw [ha_c]
  have hc1 : c1Coeff (realErfScaled α) y = (1 / Real.sqrt Real.pi) * ∫ t in b..(b + c), f t := by
    unfold c1Coeff
    rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α (1 - y) 0).1]
    have hb_eq : c * (1 - y - 1 / 2) = b := by dsimp [b]; ring
    have hb_c : c * (1 - y + 1 / 2) = b + c := by dsimp [b]; ring
    rw [hb_eq, hb_c]
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) b (a + c))
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) b (a + c))
    (hcont_f.intervalIntegrable (μ := MeasureTheory.volume) (a + c) (b + c))
  have hdiff_int : (∫ t in a..(a + c), f t) - (∫ t in b..(b + c), f t) =
      (∫ t in a..b, f t) - (∫ t in (a + c)..(b + c), f t) := by
    linarith
  have hshift : (∫ t in a..b, f (t + c)) = ∫ t in (a + c)..(b + c), f t :=
    intervalIntegral.integral_comp_add_right f c
  have hsub_int : (∫ t in a..b, f t) - (∫ t in a..b, f (t + c)) = ∫ t in a..b, g t :=
    (intervalIntegral.integral_sub (hcont_f.intervalIntegrable a b)
      (hcont_shift.intervalIntegrable a b)).symm
  have hg_nonneg : ∀ t : ℝ, a ≤ t → 0 ≤ g t := by
    intro t ht
    dsimp [g, f]
    rw [sub_nonneg]
    refine Real.exp_le_exp.mpr ?_
    have h2a_c : 0 ≤ 2 * a + c := by
      have : 2 * a + c = 2 * c * y := by dsimp [a]; ring
      rw [this]
      exact mul_nonneg (by linarith) hy0
    have hsq_sub : (t + c) ^ 2 - t ^ 2 = c * (2 * (t - a) + (2 * a + c)) := by ring
    have hprod_nonneg : 0 ≤ c * (2 * (t - a) + (2 * a + c)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hadj_g1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) a (-δ))
    (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) (-δ) δ)
  have hadj_g2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) a δ)
    (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) δ b)
  have hint_left_nonneg : 0 ≤ ∫ t in a..(-δ), g t :=
    intervalIntegral.integral_nonneg ha_le_neg_δ (fun t ht => hg_nonneg t ht.1)
  have hint_right_nonneg : 0 ≤ ∫ t in δ..b, g t :=
    intervalIntegral.integral_nonneg hδ_b (fun t ht => hg_nonneg t (by linarith [ht.1]))
  have hint_ge_mid : (∫ t in (-δ)..δ, g t) ≤ ∫ t in a..b, g t := by
    linarith
  let F : ℝ → ℝ := fun t => (0.995 : ℝ) * t - t ^ 3 / 3 + t ^ 5 / 20
  let F' : ℝ → ℝ := fun t => (0.995 : ℝ) - t ^ 2 + t ^ 4 / 4
  have hderiv : ∀ t ∈ Set.uIcc (-δ) δ, HasDerivAt F (F' t) t := by
    intro t _
    have hd1 : HasDerivAt (fun x : ℝ => (0.995 : ℝ) * x) ((0.995 : ℝ) * 1) t :=
      (hasDerivAt_id t).const_mul (0.995 : ℝ)
    have hd2 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (3 * t ^ 2 * 1 / 3) t :=
      ((hasDerivAt_id t).pow 3).div_const 3
    have hd3 : HasDerivAt (fun x : ℝ => x ^ 5 / 20) (5 * t ^ 4 * 1 / 20) t :=
      ((hasDerivAt_id t).pow 5).div_const 20
    refine ((hd1.sub hd2).add hd3).congr_deriv ?_
    dsimp [F']
    ring
  have hcont_F' : Continuous F' :=
    (continuous_const.sub (continuous_pow 2)).add ((continuous_pow 4).div_const 4)
  have hint_F' : IntervalIntegrable F' volume (-δ) δ := hcont_F'.intervalIntegrable (-δ) δ
  have hftc : (∫ t in (-δ)..δ, F' t) = F δ - F (-δ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_F'
  have hmono : (∫ t in (-δ)..δ, F' t) ≤ ∫ t in (-δ)..δ, g t := by
    refine intervalIntegral.integral_mono_on hneg_δ_le_δ hint_F'
      (hcont_g.intervalIntegrable (-δ) δ) fun t ht => ?_
    exact poly_le_exp_sub_exp_shift_47 t c hc_ge (by linarith [ht.1]) (by linarith [ht.2])
  have hF_eval : (1.883 : ℝ) * δ ≤ F δ - F (-δ) := by
    have hδ2_le : δ ^ 2 ≤ (0.16 : ℝ) := by
      have := mul_le_mul hδ04 hδ04 hδ_pos.le (by norm_num)
      linarith
    have hident : (F δ - F (-δ)) - (1.883 : ℝ) * δ =
        δ * (((0.16 : ℝ) - δ ^ 2) * (2 / 3 - 1 / 10 * δ ^ 2) + 1 / 3000 + (0.016 : ℝ) * δ ^ 2) := by
      dsimp [F]
      ring
    have hnonneg : 0 ≤ δ * (((0.16 : ℝ) - δ ^ 2) * (2 / 3 - 1 / 10 * δ ^ 2) + 1 / 3000 + (0.016 : ℝ) * δ ^ 2) :=
      mul_nonneg hδ_pos.le (add_nonneg (add_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)) (by positivity))
    linarith
  have hint_ab_ge : (1.883 : ℝ) * δ ≤ ∫ t in a..b, g t := by linarith
  have hdiff_eq : c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y =
      (1 / Real.sqrt Real.pi) * ∫ t in a..b, g t := by
    rw [hc0, hc1, ← mul_sub, hdiff_int, ← hshift, hsub_int]
  have hmul_pi : (1.062 : ℝ) * δ * Real.sqrt Real.pi ≤ (1.062 : ℝ) * δ * (1.7725 : ℝ) :=
    mul_le_mul_of_nonneg_left hsqrt_pi_lt.le (by positivity)
  rw [hdiff_eq, one_div_mul_eq_div, le_div_iff₀ hsqrt_pi]
  linarith

/-- For `24 ≤ p_work`, `0 < t1`, `0 ≤ y`, and `1 / (4 * t1) ≤ 1 / 2 - y`, the passband gap
`c0Coeff (realErfScaled (alphaSchedule p_work)) y - c1Coeff (realErfScaled (alphaSchedule p_work)) y`
is bounded below by `1.56 / max t1 2`. -/
theorem c0_sub_c1_alphaSchedule_ge
    (p_work : ℕ) (hp : 24 ≤ p_work) (t1 : ℕ) (ht1 : 0 < t1)
    (y : ℝ) (hy0 : 0 ≤ y) (hy_gap : 1 / (4 * (t1 : ℝ)) ≤ 1 / 2 - y) :
    (1.56 : ℝ) / ((max t1 2 : ℕ) : ℝ) ≤
      c0Coeff (realErfScaled (alphaSchedule p_work)) y -
      c1Coeff (realErfScaled (alphaSchedule p_work)) y := by
  have hc_ge : (8 : ℝ) ≤ Real.sqrt Real.pi * alphaSchedule p_work :=
    sqrt_pi_mul_alphaSchedule_ge_eight p_work hp
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr ht1
  have hm_ge_two : (2 : ℝ) ≤ ((max t1 2 : ℕ) : ℝ) := by exact_mod_cast le_max_right t1 2
  have hm_ge_t1 : (t1 : ℝ) ≤ ((max t1 2 : ℕ) : ℝ) := by exact_mod_cast le_max_left t1 2
  have hm_pos : (0 : ℝ) < ((max t1 2 : ℕ) : ℝ) := by linarith
  set δ := (2 : ℝ) / ((max t1 2 : ℕ) : ℝ)
  have hδ_pos : 0 < δ := div_pos zero_lt_two hm_pos
  have hδ1 : δ ≤ 1 := (div_le_one hm_pos).mpr hm_ge_two
  have hδ_le_t1 : δ ≤ (2 : ℝ) / (t1 : ℝ) :=
    div_le_div_of_nonneg_left zero_le_two ht1_pos hm_ge_t1
  have h_two_div_t1 : (2 : ℝ) / (t1 : ℝ) = (8 : ℝ) * (1 / (4 * (t1 : ℝ))) := by
    field_simp [ht1_pos.ne']
    ring
  have hδ_b : δ ≤ (Real.sqrt Real.pi * alphaSchedule p_work) * (1 / 2 - y) := by
    have hmul := mul_le_mul hc_ge hy_gap (by positivity) (by linarith)
    linarith
  have h := c0_sub_c1_ge_of_delta (alphaSchedule p_work) y δ hc_ge hy0 hδ_pos hδ1 hδ_b
  have h078 : (0.78 : ℝ) * δ = (1.56 : ℝ) / ((max t1 2 : ℕ) : ℝ) := by
    dsimp [δ]
    ring
  linarith

/-- For `8 ≤ p_work`, `3 ≤ t1`, `0 ≤ y`, and `1 / (4 * t1) ≤ 1 / 2 - y`, the passband gap
`c0Coeff (realErfScaled (alphaSchedule p_work)) y - c1Coeff (realErfScaled (alphaSchedule p_work)) y`
is bounded below by `1.2 / t1`. -/
theorem c0_sub_c1_alphaSchedule_ge_of_ge_three
    (p_work : ℕ) (hp : 8 ≤ p_work) (t1 : ℕ) (ht1 : 3 ≤ t1)
    (y : ℝ) (hy0 : 0 ≤ y) (hy_gap : 1 / (4 * (t1 : ℝ)) ≤ 1 / 2 - y) :
    (1.2 : ℝ) / (t1 : ℝ) ≤
      c0Coeff (realErfScaled (alphaSchedule p_work)) y -
      c1Coeff (realErfScaled (alphaSchedule p_work)) y := by
  have hc_ge : (4.7 : ℝ) ≤ Real.sqrt Real.pi * alphaSchedule p_work :=
    sqrt_pi_mul_alphaSchedule_ge_47 p_work hp
  have ht1_ge3 : (3 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := by linarith
  set δ := (1.175 : ℝ) / (t1 : ℝ)
  have hδ_pos : 0 < δ := div_pos (by norm_num) ht1_pos
  have hδ04 : δ ≤ (0.4 : ℝ) := by
    dsimp [δ]
    rw [div_le_iff₀ ht1_pos]
    linarith
  have h_div_t1 : (1.175 : ℝ) / (t1 : ℝ) = (4.7 : ℝ) * (1 / (4 * (t1 : ℝ))) := by
    field_simp [ht1_pos.ne']
    ring
  have hδ_b : δ ≤ (Real.sqrt Real.pi * alphaSchedule p_work) * (1 / 2 - y) := by
    dsimp [δ]
    rw [h_div_t1]
    exact mul_le_mul hc_ge hy_gap (by positivity) (by linarith)
  have h := c0_sub_c1_ge_of_delta_small (alphaSchedule p_work) y δ hc_ge hy0 hδ_pos hδ04 hδ_b
  have h12 : (1.2 : ℝ) / (t1 : ℝ) ≤ (1.062 : ℝ) * δ := by
    dsimp [δ]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by norm_num) ht1_pos.le
  linarith

/-- **General Wrap-Around Ratio Bound `≤ 0.15` for `0 ≤ y ≤ 1 / 2 - 1 / (4 * t1)` (`[MS]` §5.1, eq. (22))**:
For `8 ≤ p_work`, `0 < t1`, and any `y : ℝ` satisfying `0 ≤ y` and `1 / (4 * t1) ≤ 1 / 2 - y`,
`(c1Coeff (realErfScaled (alphaSchedule p_work)) y / c0Coeff (realErfScaled (alphaSchedule p_work)) y) ^ t1 ≤ 0.15`. -/
theorem c1_div_c0_pow_le_015_of_le_half
    (p_work : ℕ) (hp : 8 ≤ p_work) (t1 : ℕ) (ht1 : 0 < t1)
    (y : ℝ) (hy0 : 0 ≤ y) (hy_gap : 1 / (4 * (t1 : ℝ)) ≤ 1 / 2 - y) :
    (c1Coeff (realErfScaled (alphaSchedule p_work)) y /
      c0Coeff (realErfScaled (alphaSchedule p_work)) y) ^ t1 ≤ (0.15 : ℝ) := by
  set α := alphaSchedule p_work
  set c0 := c0Coeff (realErfScaled α) y
  set c1 := c1Coeff (realErfScaled α) y
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  have hc0_pos : 0 < c0 := c0Coeff_realErfScaled_pos α y hα
  have hc1_pos : 0 < c1 := c1Coeff_realErfScaled_pos α y hα
  have hsum : c0 + c1 ≤ 1 := c0_add_c1_realErfScaled_le_one α y hα
  have hdiv_nonneg : 0 ≤ c1 / c0 := div_nonneg hc1_pos.le hc0_pos.le
  have hc_ge : (4.7 : ℝ) ≤ Real.sqrt Real.pi * α := sqrt_pi_mul_alphaSchedule_ge_47 p_work hp
  rcases lt_or_ge t1 3 with ht1_lt3 | ht1_ge3
  · interval_cases t1
    · have hδ_b : (1 : ℝ) ≤ (Real.sqrt Real.pi * α) * (1 / 2 - y) := by
        norm_num at hy_gap
        nlinarith
      have hdiff := c0_sub_c1_ge_of_delta_47 α y 1 hc_ge hy0 zero_lt_one le_rfl hδ_b
      have hc1_le : c1 ≤ (0.15 : ℝ) * c0 := by linarith
      have hdiv_le : c1 / c0 ≤ (0.15 : ℝ) := (div_le_iff₀ hc0_pos).mpr hc1_le
      simpa using hdiv_le
    · have hδ_b : (0.5875 : ℝ) ≤ (Real.sqrt Real.pi * α) * (1 / 2 - y) := by
        norm_num at hy_gap
        nlinarith
      have hdiff := c0_sub_c1_ge_of_delta_47 α y (0.5875 : ℝ) hc_ge hy0 (by norm_num) (by norm_num) hδ_b
      have hc1_le : c1 ≤ (0.38 : ℝ) * c0 := by linarith
      have hdiv_le : c1 / c0 ≤ (0.38 : ℝ) := (div_le_iff₀ hc0_pos).mpr hc1_le
      calc (c1 / c0) ^ 2
          ≤ (0.38 : ℝ) ^ 2 := pow_le_pow_left₀ hdiv_nonneg hdiv_le 2
        _ ≤ (0.15 : ℝ) := by norm_num
  · have hdiff := c0_sub_c1_alphaSchedule_ge_of_ge_three p_work hp t1 ht1_ge3 y hy0 hy_gap
    rcases lt_or_ge t1 6 with ht1_lt6 | ht1_ge6
    · interval_cases t1
      · norm_num at hdiff
        have hdiv_le : c1 / c0 ≤ (3 / 7 : ℝ) := (div_le_iff₀ hc0_pos).mpr (by linarith)
        calc (c1 / c0) ^ 3 ≤ (3 / 7 : ℝ) ^ 3 := pow_le_pow_left₀ hdiv_nonneg hdiv_le 3
          _ ≤ (0.15 : ℝ) := by norm_num
      · norm_num at hdiff
        have hdiv_le : c1 / c0 ≤ (7 / 13 : ℝ) := (div_le_iff₀ hc0_pos).mpr (by linarith)
        calc (c1 / c0) ^ 4 ≤ (7 / 13 : ℝ) ^ 4 := pow_le_pow_left₀ hdiv_nonneg hdiv_le 4
          _ ≤ (0.15 : ℝ) := by norm_num
      · norm_num at hdiff
        have hdiv_le : c1 / c0 ≤ (19 / 31 : ℝ) := (div_le_iff₀ hc0_pos).mpr (by linarith)
        calc (c1 / c0) ^ 5 ≤ (19 / 31 : ℝ) ^ 5 := pow_le_pow_left₀ hdiv_nonneg hdiv_le 5
          _ ≤ (0.15 : ℝ) := by norm_num
    · set D := (1.2 : ℝ) / (t1 : ℝ)
      have ht1_ge6_real : (6 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1_ge6
      have ht1_pos : (0 : ℝ) < (t1 : ℝ) := by linarith
      have hD_pos : 0 < D := div_pos (by norm_num) ht1_pos
      have hD_le : D ≤ (0.2 : ℝ) := by
        dsimp [D]
        rw [div_le_iff₀ ht1_pos]
        linarith
      have hident : (1 - D) * c0 - (1 + D) * c1 = (c0 - c1 - D) + D * (1 - c0 - c1) := by ring
      have hterm1 : 0 ≤ D * (1 - c0 - c1) := mul_nonneg hD_pos.le (by linarith)
      have h1D_c1 : (1 + D) * c1 ≤ (1 - D) * c0 := by linarith
      have h53_D : (5 / 3 : ℝ) * D = (2 : ℝ) / (t1 : ℝ) := by
        dsimp [D]
        ring
      have h_lhs_le : 1 - D ≤ (1 + D) * (1 - (5 / 3 : ℝ) * D) := by
        have hdiff_D : (1 + D) * (1 - (5 / 3 : ℝ) * D) - (1 - D) =
            (1 / 3 : ℝ) * D * (1 - 5 * D) := by ring
        have hnonneg : 0 ≤ (1 / 3 : ℝ) * D * (1 - 5 * D) :=
          mul_nonneg (mul_nonneg (by norm_num) hD_pos.le) (by linarith)
        linarith
      have hprod_le : (1 + D) * c1 ≤ (1 + D) * ((1 - (5 / 3 : ℝ) * D) * c0) := by
        calc (1 + D) * c1
            ≤ (1 - D) * c0 := h1D_c1
          _ ≤ ((1 + D) * (1 - (5 / 3 : ℝ) * D)) * c0 :=
              mul_le_mul_of_nonneg_right h_lhs_le hc0_pos.le
          _ = (1 + D) * ((1 - (5 / 3 : ℝ) * D) * c0) := by ring
      have hc1_le : c1 ≤ (1 - (5 / 3 : ℝ) * D) * c0 :=
        le_of_mul_le_mul_left hprod_le (by linarith)
      rw [h53_D] at hc1_le
      have hdiv_le : c1 / c0 ≤ 1 - (2 : ℝ) / (t1 : ℝ) := (div_le_iff₀ hc0_pos).mpr hc1_le
      have hexp_step : 1 - (2 : ℝ) / (t1 : ℝ) ≤ Real.exp (-((2 : ℝ) / (t1 : ℝ))) := by
        have h := Real.add_one_le_exp (-((2 : ℝ) / (t1 : ℝ)))
        linarith
      have hpow_le : (c1 / c0) ^ t1 ≤ (Real.exp (-((2 : ℝ) / (t1 : ℝ)))) ^ t1 :=
        pow_le_pow_left₀ hdiv_nonneg (hdiv_le.trans hexp_step) t1
      have hexp_pow : (Real.exp (-((2 : ℝ) / (t1 : ℝ)))) ^ t1 = Real.exp (-2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp [ht1_pos.ne']
      rw [hexp_pow] at hpow_le
      have he1 : (2.71 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have he2 : (7.3 : ℝ) ≤ Real.exp 2 := by
        have h2 : (2 : ℝ) = 1 + 1 := by norm_num
        rw [h2, Real.exp_add]
        have hmul := mul_le_mul he1.le he1.le (by norm_num) (Real.exp_pos _).le
        linarith
      have hprod : Real.exp (-2) * Real.exp 2 = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hpos : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
      have hexp_neg2_le : Real.exp (-2) ≤ (0.15 : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left he2 hpos
        linarith
      exact hpow_le.trans hexp_neg2_le

/-- **`[MS]` Theorem 5.1 (Forward Wrap-Around Ratio Bound `≤ 0.15` for Balanced Splits `r ≤ 2 * t1`, `[MS]` §5.1, eq. (22))**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, `r ≤ 2 * t1`, and `2 * u2 < r`,
`(c1Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r) / c0Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r)) ^ t1 ≤ 0.15`. -/
theorem c1_div_c0_pow_le_015_of_balanced
    (p_work t1 r u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hr_le : r ≤ 2 * t1) (hu2 : 2 * u2 < r) :
    (c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) /
      c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ))) ^ t1 ≤ (0.15 : ℝ) := by
  have hy0 : 0 ≤ (u2 : ℝ) / (r : ℝ) := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hu2_real : 2 * (u2 : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast (by omega : 2 * u2 + 1 ≤ r)
  have hr_real : (r : ℝ) ≤ 2 * (t1 : ℝ) := by exact_mod_cast hr_le
  have h1 : 1 / (4 * (t1 : ℝ)) ≤ 1 / (2 * (r : ℝ)) :=
    div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
  have h2 : 1 / (2 * (r : ℝ)) ≤ 1 / 2 - (u2 : ℝ) / (r : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have hrew : (1 / 2 - (u2 : ℝ) / (r : ℝ)) * (2 * (r : ℝ)) = (r : ℝ) - 2 * (u2 : ℝ) := by
      field_simp [hr_pos.ne']
    linarith
  exact c1_div_c0_pow_le_015_of_le_half p_work hp t1 ht1 ((u2 : ℝ) / (r : ℝ)) hy0 (h1.trans h2)

/-- **`[MS]` Theorem 5.1 (Backward Wrap-Around Ratio Bound `≤ 0.15` for Balanced Splits `r ≤ 2 * t1`, `[MS]` §5.1, eq. (22))**:
By symmetry (`y ↦ 1 - y`), for `8 ≤ p_work`, `0 < t1`, `0 < r`, `r ≤ 2 * t1`, `r < 2 * u2`, and `u2 < r`,
`(c0Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r) / c1Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r)) ^ t1 ≤ 0.15`. -/
theorem c0_div_c1_pow_le_015_of_balanced
    (p_work t1 r u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hr_le : r ≤ 2 * t1) (hu2_gt : r < 2 * u2) (hu2_lt : u2 < r) :
    (c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) /
      c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ))) ^ t1 ≤ (0.15 : ℝ) := by
  have h := c1_div_c0_pow_le_015_of_balanced p_work t1 r (r - u2) hp ht1 hr hr_le (by omega)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hsub : ((r - u2 : ℕ) : ℝ) / (r : ℝ) = 1 - (u2 : ℝ) / (r : ℝ) := by
    rw [Nat.cast_sub hu2_lt.le]
    field_simp [hr_pos.ne']
  have hc1_symm : c1Coeff (realErfScaled (alphaSchedule p_work)) (((r - u2 : ℕ) : ℝ) / (r : ℝ)) =
      c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) := by
    rw [hsub]
    unfold c1Coeff c0Coeff
    have h1 : 1 - (1 - (u2 : ℝ) / (r : ℝ)) = (u2 : ℝ) / (r : ℝ) := by ring
    rw [h1]
  have hc0_symm : c0Coeff (realErfScaled (alphaSchedule p_work)) (((r - u2 : ℕ) : ℝ) / (r : ℝ)) =
      c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) := by
    rw [hsub]
    rfl
  rwa [hc1_symm, hc0_symm] at h

/-- **Formal Infinite-Series Poisson Spread vs. Ideal 2-Term Passband Error Bound (`[MS]` §5.1, eqs. (20)–(21))**:
For `p_work ≥ 8`, `y ∈ [0, 1]`, and any bounded mode sequence `X : ℤ → ℂ` with `‖X m‖ ≤ B_X`
(`B_X ≥ 0`), the difference between the full infinite Poisson alias series
`∑' m : ℤ, gHatBox (realErfScaled (alphaSchedule p_work)) (y - m) * X (u_1 - m)`
and the 2-term passband approximation `c_0(y) X(u_1) + c_1(y) X(u_1 - 1)` is bounded in norm by
`0.15 * 2^{-p_work} * B_X`. -/
theorem infinite_poisson_spread_sub_passband_norm_le
    (p_work : ℕ) (hp : 8 ≤ p_work) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (X : ℤ → ℂ) (B_X : ℝ) (hB : 0 ≤ B_X) (hX : ∀ m : ℤ, ‖X m‖ ≤ B_X) (u1 : ℤ) :
    ‖(∑' m : ℤ, (gHatBox (realErfScaled (alphaSchedule p_work)) (y - (m : ℝ)) : ℂ) * X (u1 - m)) -
      ((c0Coeff (realErfScaled (alphaSchedule p_work)) y : ℂ) * X u1 +
       (c1Coeff (realErfScaled (alphaSchedule p_work)) y : ℂ) * X (u1 - 1))‖ ≤
      (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X := by
  set α := alphaSchedule p_work
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  let f : ℤ → ℂ := fun m => (gHatBox (realErfScaled α) (y - (m : ℝ)) : ℂ) * X (u1 - m)
  let f_stop : ℤ → ℂ := fun m => (stopbandGHatBox α y m : ℂ) * X (u1 - m)
  let f0 : ℤ → ℂ := fun m => if m = 0 then (c0Coeff (realErfScaled α) y : ℂ) * X u1 else 0
  let f1 : ℤ → ℂ := fun m => if m = 1 then (c1Coeff (realErfScaled α) y : ℂ) * X (u1 - 1) else 0
  have hf_eq : ∀ m : ℤ, f m = f_stop m + (f0 m + f1 m) := by
    intro m
    dsimp [f, f_stop, f0, f1]
    have hdecomp := stopbandGHatBox_add_passband_eq α y m
    by_cases hm0 : m = 0
    · subst hm0
      simp only [↓reduceIte, sub_zero, zero_ne_one, add_zero]
      rw [← hdecomp]
      simp [add_mul]
    · by_cases hm1 : m = 1
      · subst hm1
        simp only [hm0, ↓reduceIte, zero_add]
        rw [← hdecomp]
        simp [hm0, add_mul]
      · simp only [hm0, hm1, ↓reduceIte, add_zero]
        rw [← hdecomp]
        simp [hm0, hm1]
  have hnorm_stop_le : ∀ m : ℤ, ‖f_stop m‖ ≤ stopbandGHatBox α y m * B_X := by
    intro m
    dsimp [f_stop]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (stopbandGHatBox_nonneg α y hα m)]
    exact mul_le_mul_of_nonneg_left (hX (u1 - m)) (stopbandGHatBox_nonneg α y hα m)
  have hsum_stop_majorant : Summable (fun m : ℤ => stopbandGHatBox α y m * B_X) :=
    (summable_stopbandGHatBox α y hα).mul_right B_X
  have hsum_norm_stop : Summable (fun m : ℤ => ‖f_stop m‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm_stop_le hsum_stop_majorant
  have hsum_stop : Summable f_stop := hsum_norm_stop.of_norm
  have hsum_f0 : Summable f0 := (hasSum_ite_eq (0 : ℤ) _).summable
  have hsum_f1 : Summable f1 := (hasSum_ite_eq (1 : ℤ) _).summable
  have htsum_f0 : (∑' m : ℤ, f0 m) = (c0Coeff (realErfScaled α) y : ℂ) * X u1 :=
    tsum_ite_eq (0 : ℤ) _
  have htsum_f1 : (∑' m : ℤ, f1 m) = (c1Coeff (realErfScaled α) y : ℂ) * X (u1 - 1) :=
    tsum_ite_eq (1 : ℤ) _
  have htsum_split :
      (∑' m : ℤ, f m) -
        ((c0Coeff (realErfScaled α) y : ℂ) * X u1 +
         (c1Coeff (realErfScaled α) y : ℂ) * X (u1 - 1)) =
      ∑' m : ℤ, f_stop m := by
    have hfun : f = fun m => f_stop m + (f0 m + f1 m) := funext hf_eq
    rw [hfun, hsum_stop.tsum_add (hsum_f0.add hsum_f1), hsum_f0.tsum_add hsum_f1,
        htsum_f0, htsum_f1, add_sub_cancel_right]
  rw [htsum_split]
  calc ‖∑' m : ℤ, f_stop m‖
      ≤ ∑' m : ℤ, ‖f_stop m‖ := norm_tsum_le_tsum_norm hsum_norm_stop
    _ ≤ ∑' m : ℤ, (stopbandGHatBox α y m * B_X) :=
        hsum_norm_stop.tsum_le_tsum hnorm_stop_le hsum_stop_majorant
    _ = (∑' m : ℤ, stopbandGHatBox α y m) * B_X := tsum_mul_right
    _ ≤ (1 - c0Coeff (realErfScaled α) y - c1Coeff (realErfScaled α) y) * B_X :=
        mul_le_mul_of_nonneg_right (tsum_stopbandGHatBox_le α y hα) hB
    _ ≤ (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X :=
        mul_le_mul_of_nonneg_right
          (theorem3_stopband_alias_bound_alphaSchedule p_work hp y hy0 hy1).le hB

/-- **Continuous Fourier Transform of `sincGaussian` Equals `gHatBox (realErfScaled α)` (`[MS]` §4.2, eq. (16) & §5.1)**:
For any `α > 0` and `ξ : ℝ`, Mathlib's continuous Lebesgue Fourier transform
`𝓕 (fun t : ℝ => (sincGaussian α t : ℂ)) ξ` equals `(gHatBox (realErfScaled α) ξ : ℂ)`. -/
theorem fourier_sincGaussian_eq_gHatBox (α ξ : ℝ) (hα : 0 < α) :
    (𝓕 fun t : ℝ => (sincGaussian α t : ℂ)) ξ = (gHatBox (realErfScaled α) ξ : ℂ) := by
  rw [fourier_sincGaussian_eq_box_gaussian_integral α ξ hα,
      (theorem3_concrete_box_gaussian_integral_and_telescoping α ξ 0).1]

/-- **Unconditional Fourier-Series Summability (`h_sum`) for `sincGaussianModulatedMap` (`[MS]` §4.2 & §5.1)**:
Discharges Mathlib's `h_sum` hypothesis (`Summable fun m : ℤ => 𝓕 f m`) for the shifted/modulated
Sinc-Gaussian kernel at any `α > 0`. -/
theorem summable_fourier_sincGaussian_modulated (α z ξ : ℝ) (hα : 0 < α) :
    Summable fun m : ℤ => 𝓕 (sincGaussianModulatedMap α z ξ : ℝ → ℂ) m := by
  have hnorm_eq : ∀ m : ℤ,
      ‖𝓕 (sincGaussianModulatedMap α z ξ : ℝ → ℂ) m‖ =
        gHatBox (realErfScaled α) (ξ - (m : ℝ)) := by
    intro m
    have hfun : (sincGaussianModulatedMap α z ξ : ℝ → ℂ) =
        fun t : ℝ => (sincGaussian α (z - t) : ℂ) * stdChar (ξ * t) := rfl
    rw [hfun, fourier_modulated_shift (fun t : ℝ => (sincGaussian α t : ℂ)) z ξ (m : ℝ),
        fourier_sincGaussian_eq_gHatBox α (ξ - (m : ℝ)) hα, norm_mul, norm_stdChar, one_mul,
        Complex.norm_real, Real.norm_of_nonneg (gHatBox_realErfScaled_pos α (ξ - (m : ℝ)) hα).le]
  have hsum_norm : Summable fun m : ℤ => ‖𝓕 (sincGaussianModulatedMap α z ξ : ℝ → ℂ) m‖ := by
    simp_rw [hnorm_eq]
    exact summable_gHatBox_realErfScaled α ξ hα
  exact hsum_norm.of_norm

/-- **Unconditional Continuous 1D Poisson Summation for the Sinc-Gaussian Kernel (`[MS]` §4.2, proof of Theorem 4.2)**:
For any `α > 0` and `z, ξ : ℝ` (with zero external summability hypotheses),
`∑' k : ℤ, sincGaussian α (z - k) * stdChar (ξ * k) =
 ∑' m : ℤ, gHatBox (realErfScaled α) (ξ - m) * stdChar ((ξ - m) * z)`. -/
theorem sincGaussian_modulated_poisson_summation (α z ξ : ℝ) (hα : 0 < α) :
    (∑' k : ℤ, (sincGaussian α (z - (k : ℝ)) : ℂ) * stdChar (ξ * (k : ℝ))) =
      ∑' m : ℤ, (gHatBox (realErfScaled α) (ξ - (m : ℝ)) : ℂ) * stdChar ((ξ - (m : ℝ)) * z) := by
  have hP := continuous_modulated_poisson_summation
    (fun t : ℝ => (sincGaussian α t : ℂ)) z ξ
    (sincGaussianModulatedMap α z ξ)
    (fun _ => rfl)
    (summable_norm_restrict_sincGaussian_modulated α z ξ hα)
    (summable_fourier_sincGaussian_modulated α z ξ hα)
  rw [hP]
  congr 1 with m
  rw [fourier_sincGaussian_eq_gHatBox α (ξ - (m : ℝ)) hα]

/-- **Unconditional `[MS]` Theorem 4.2 for the Sinc-Gaussian Kernel (`sincGaussian` → `gHatBox` · `dft1DGrid`, `[MS]` §4.2, eq. (18))**:
For any `t_1, r > 0`, `α > 0`, `x : ℕ → ℂ`, `u_1, u_2 : ℕ`, and `u1_tilde : ℤ → ℕ`, `q : ℤ → ℤ`
satisfying `u_1 - m = u1_tilde m + q m * t_1` (with zero external summability hypotheses),
the 2D DFT of the infinite-lattice Sinc-Gaussian spread equals:
`∑' m : ℤ, gHatBox (realErfScaled α) (u_2 / r - m) * dft1DGrid t1 r x u2 (u1_tilde m)`. -/
theorem theorem2_sincGaussian_poisson_to_dft1DGrid
    (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (α : ℝ) (hα : 0 < α) (x : ℕ → ℂ)
    (u1 u2 : ℕ) (u1_tilde : ℤ → ℕ) (q : ℤ → ℤ)
    (hu1 : ∀ m : ℤ, (u1 : ℤ) - m = (u1_tilde m : ℤ) + q m * (t1 : ℤ)) :
    (1 / ((t1 * r : ℕ) : ℂ)) *
      (∑ j1 ∈ Finset.range t1, stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
        ∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) *
          (∑' k : ℤ, (sincGaussian α (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) - (k : ℝ)) : ℂ) *
            stdChar (((u2 : ℝ) / (r : ℝ)) * (k : ℝ)))) =
    ∑' m : ℤ, (gHatBox (realErfScaled α) ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
      dft1DGrid t1 r x u2 (u1_tilde m) := by
  have h := theorem2_continuous_poisson_to_dft1DGrid t1 r ht1 hr
    (fun t : ℝ => (sincGaussian α t : ℂ)) x u1 u2 u1_tilde q hu1
    (fun j1 j2 => sincGaussianModulatedMap α ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) ((u2 : ℝ) / (r : ℝ)))
    (fun _ _ _ => rfl)
    (fun j1 j2 K => summable_norm_restrict_sincGaussian_modulated α
      ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) ((u2 : ℝ) / (r : ℝ)) hα K)
    (fun j1 j2 => summable_fourier_sincGaussian_modulated α
      ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) ((u2 : ℝ) / (r : ℝ)) hα)
  rw [h]
  congr 1 with m
  rw [fourier_sincGaussian_eq_gHatBox α ((u2 : ℝ) / (r : ℝ) - (m : ℝ)) hα]

/-- Equivalence `(Fin r × ℤ) ≃ ℤ` given by Euclidean division `(k2, l) ↦ k2 + l * r` (`r > 0`). -/
def finProdIntEquiv (r : ℕ) (hr : 0 < r) : Fin r × ℤ ≃ ℤ where
  toFun p := (p.1.val : ℤ) + p.2 * (r : ℤ)
  invFun k := (⟨(k % (r : ℤ)).toNat, by
    have hlt : k % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos k (by omega)
    have hnonneg : 0 ≤ k % (r : ℤ) := Int.emod_nonneg k (by omega)
    omega⟩, k / (r : ℤ))
  left_inv := fun ⟨⟨k2, hk2⟩, l⟩ => by
    ext
    · dsimp only
      rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
    · dsimp only
      rw [Int.add_mul_ediv_right _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]
  right_inv k := by
    dsimp only
    have hnonneg : 0 ≤ k % (r : ℤ) := Int.emod_nonneg k (by omega)
    rw [Int.toNat_of_nonneg hnonneg]
    have h := Int.emod_add_mul_ediv k (r : ℤ)
    linarith

/-- Partitioning a summable `ℤ`-series by residue classes `k2 ∈ Finset.range r` modulo `r > 0`:
`∑ k2 ∈ Finset.range r, ∑' l : ℤ, F (k2 + l * r) = ∑' k : ℤ, F k`. -/
theorem sum_range_tsum_lattice_fold (r : ℕ) (hr : 0 < r) (F : ℤ → ℂ) (hF : Summable F) :
    (∑ k2 ∈ Finset.range r, ∑' l : ℤ, F ((k2 : ℤ) + l * (r : ℤ))) = ∑' k : ℤ, F k := by
  let e := finProdIntEquiv r hr
  have hFe : Summable (F ∘ e) := e.summable_iff.mpr hF
  have hprod : (∑' p : Fin r × ℤ, (F ∘ e) p) = ∑' k : ℤ, F k := e.tsum_eq F
  rw [← hprod, hFe.tsum_prod, tsum_fintype, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- Unfolding the pre-folded `r`-periodic `sincGaussian` row sum into the full `ℤ`-lattice sum:
for `r > 0` and `α > 0`,
`∑_{k_2 < r} (∑'_{l ∈ ℤ} sincGaussian α (k_2 + l r - z)) e(k_2 u_2 / r) =
 ∑'_{k ∈ ℤ} sincGaussian α (z - k) e((u_2 / r) k)`. -/
theorem sum_range_tsum_sincGaussian_lattice_fold
    (r : ℕ) (hr : 0 < r) (α z : ℝ) (hα : 0 < α) (u2 : ℕ) :
    (∑ k2 ∈ Finset.range r,
      (∑' l : ℤ, (sincGaussian α ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - z) : ℂ)) *
        stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))) =
    ∑' k : ℤ, (sincGaussian α (z - (k : ℝ)) : ℂ) * stdChar (((u2 : ℝ) / (r : ℝ)) * (k : ℝ)) := by
  let F : ℤ → ℂ := fun k =>
    (sincGaussian α (z - (k : ℝ)) : ℂ) * stdChar (((u2 : ℝ) / (r : ℝ)) * (k : ℝ))
  have hF : Summable F := (summable_norm_sincGaussian_modulated α z ((u2 : ℝ) / (r : ℝ)) hα).of_norm
  rw [← sum_range_tsum_lattice_fold r hr F hF]
  refine Finset.sum_congr rfl fun k2 _ => ?_
  rw [← tsum_mul_right]
  congr 1 with l
  dsimp [F]
  have heven : sincGaussian α ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - z) =
      sincGaussian α (z - (((k2 : ℤ) + l * (r : ℤ) : ℤ) : ℝ)) := by
    have hneg : (k2 : ℝ) + (l : ℝ) * (r : ℝ) - z =
        -(z - (((k2 : ℤ) + l * (r : ℤ) : ℤ) : ℝ)) := by push_cast; ring
    rw [hneg, sincGaussian_even]
  have hfold := (stdChar_lattice_fold r hr (k2 : ℤ) l (u2 : ℤ)).symm
  have hcast1 : (((k2 * u2 : ℕ) : ℝ) / (r : ℝ)) =
      (((k2 : ℤ) : ℝ) * ((u2 : ℤ) : ℝ)) / (r : ℝ) := by push_cast; ring
  have hcast2 : ((((k2 : ℤ) + l * (r : ℤ) : ℤ) : ℝ) * ((u2 : ℤ) : ℝ)) / (r : ℝ) =
      ((u2 : ℝ) / (r : ℝ)) * (((k2 : ℤ) + l * (r : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [heven, hcast1, hfold, hcast2]

/-- **Pointwise Spatial Tail Bound for `sincGaussian` (`|t| ≥ W_real > 0`, `[MS]` §6.1, Lemma 6.1)**:
For `0 < α`, `0 < W_real`, and `W_real ≤ |t|`,
`|sincGaussian α t| ≤ (1 / (Real.pi * W_real)) * Real.exp (-(Real.pi * t ^ 2 / α ^ 2))`. -/
theorem abs_sincGaussian_le_of_le_abs
    (α t W_real : ℝ) (hα : 0 < α) (hW : 0 < W_real) (ht : W_real ≤ |t|) :
    |sincGaussian α t| ≤ (1 / (Real.pi * W_real)) * Real.exp (-(Real.pi * t ^ 2 / α ^ 2)) := by
  have _ := hα
  have ht_pos : 0 < |t| := hW.trans_le ht
  have ht_ne : t ≠ 0 := abs_pos.mp ht_pos
  have h1 := abs_sincGaussian_le α t ht_ne
  have h2 : 1 / (Real.pi * |t|) ≤ 1 / (Real.pi * W_real) :=
    one_div_le_one_div_of_le (mul_pos Real.pi_pos hW)
      (mul_le_mul_of_nonneg_left ht Real.pi_pos.le)
  have hexp_eq : -(Real.pi / α ^ 2) * t ^ 2 = -(Real.pi * t ^ 2 / α ^ 2) := by ring
  rw [hexp_eq] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)

/-- **Pointwise Geometric Majorant for `sincGaussian` Beyond Window Half-Width `m_1` (`[MS]` §6.1, Lemma 6.1)**:
For `0 < α`, `1 ≤ m1`, and any `t : ℝ`, `k : ℕ` with `(m1 : ℝ) + (k : ℝ) ≤ |t|`,
since `t^2 ≥ (m_1 + k)^2 ≥ m_1^2 + 2 m_1 k`, we have:
`|sincGaussian α t| ≤ ((1 / (π m_1)) * exp(-π m_1^2 / α^2)) * (exp(-2 π m_1 / α^2))^k`. -/
theorem abs_sincGaussian_le_geometric_of_le_abs
    (α t : ℝ) (m1 k : ℕ) (hα : 0 < α) (hm1 : 1 ≤ m1)
    (ht : (m1 : ℝ) + (k : ℝ) ≤ |t|) :
    |sincGaussian α t| ≤
      ((1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2))) *
        (Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))) ^ k := by
  have hm1_pos : (0 : ℝ) < (m1 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hm1_le_abs : (m1 : ℝ) ≤ |t| := by linarith
  have h1 := abs_sincGaussian_le_of_le_abs α t (m1 : ℝ) hα hm1_pos hm1_le_abs
  have hexp_le :
      Real.exp (-(Real.pi * t ^ 2 / α ^ 2)) ≤
        Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2)) *
          (Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h_lhs : -(Real.pi * t ^ 2 / α ^ 2) = -(Real.pi / α ^ 2) * t ^ 2 := by ring
    have h_rhs : -(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2) +
        (k : ℝ) * -(2 * Real.pi * (m1 : ℝ) / α ^ 2) =
        -(Real.pi / α ^ 2) * ((m1 : ℝ) ^ 2 + 2 * (m1 : ℝ) * (k : ℝ)) := by ring
    rw [h_lhs, h_rhs]
    have hsq : (m1 : ℝ) ^ 2 + 2 * (m1 : ℝ) * (k : ℝ) ≤ t ^ 2 := by
      have habs : ((m1 : ℝ) + (k : ℝ)) ^ 2 ≤ |t| ^ 2 := by nlinarith
      rw [sq_abs] at habs
      nlinarith
    have hc : 0 ≤ Real.pi / α ^ 2 := (div_pos Real.pi_pos (sq_pos_of_pos hα)).le
    nlinarith
  calc |sincGaussian α t|
      ≤ (1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * t ^ 2 / α ^ 2)) := h1
    _ ≤ (1 / (Real.pi * (m1 : ℝ))) *
          (Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2)) *
            (Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))) ^ k) :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ = ((1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2))) *
          (Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))) ^ k := by ring

/-- **Geometric Series Tail Bound for `sincGaussian` Beyond Window Half-Width `m_1` (`[MS]` §6.1, Lemma 6.1)**:
For `0 < α`, `1 ≤ m1`, and fractional shift offset `δ ∈ [0, 1]`, both the positive spatial tail
`∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|` and the negative spatial tail
`∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|` are summable and bounded above by
`((1 / (π * m_1)) * exp(-π m_1^2 / α^2)) / (1 - exp(-2 π m_1 / α^2))`. -/
theorem tsum_abs_sincGaussian_tails_le
    (α δ : ℝ) (m1 : ℕ) (hα : 0 < α) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hm1 : 1 ≤ m1) :
    Summable (fun k : ℕ => |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) ∧
    Summable (fun k : ℕ => |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) ∧
    (∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) ≤
      ((1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2))) /
        (1 - Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))) ∧
    (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) ≤
      ((1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2))) /
        (1 - Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))) := by
  set C := (1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2))
  set q := Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))
  have hm1_pos : (0 : ℝ) < (m1 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < 2 * Real.pi * (m1 : ℝ) / α ^ 2 :=
      div_pos (mul_pos (mul_pos zero_lt_two Real.pi_pos) hm1_pos) (sq_pos_of_pos hα)
    linarith
  have hsum_geom : Summable (fun k : ℕ => C * q ^ k) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left C
  have htsum_geom : (∑' k : ℕ, C * q ^ k) = C / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq_nonneg hq_lt_one, div_eq_mul_inv]
  have hpos_le : ∀ k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)| ≤ C * q ^ k := by
    intro k
    refine abs_sincGaussian_le_geometric_of_le_abs α ((m1 + 1 + k : ℝ) - δ) m1 k hα hm1 ?_
    have hle : (m1 : ℝ) + (k : ℝ) ≤ (m1 + 1 + k : ℝ) - δ := by linarith
    exact hle.trans (le_abs_self _)
  have hneg_le : ∀ k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)| ≤ C * q ^ k := by
    intro k
    refine abs_sincGaussian_le_geometric_of_le_abs α (-((m1 + 1 + k : ℝ)) - δ) m1 k hα hm1 ?_
    have hle : (m1 : ℝ) + (k : ℝ) ≤ -(-((m1 + 1 + k : ℝ)) - δ) := by linarith
    exact hle.trans (neg_le_abs _)
  have hsum_pos : Summable (fun k : ℕ => |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpos_le hsum_geom
  have hsum_neg : Summable (fun k : ℕ => |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hneg_le hsum_geom
  refine ⟨hsum_pos, hsum_neg, ?_, ?_⟩
  · rw [← htsum_geom]
    exact hsum_pos.tsum_le_tsum hpos_le hsum_geom
  · rw [← htsum_geom]
    exact hsum_neg.tsum_le_tsum hneg_le hsum_geom

/-- **`[MS]` Lemma 6.1 (Part 1: Finite-Tap Spatial Window Truncation Tail Bound `< 0.4 * 2^{-p_child}`, `[MS]` §6.1, Lemma 6.1 & §6.3, Lemma 6.5)**:
Under the window half-width rule `(p_child : ℝ) * Real.log 2 ≤ π * m_1^2 / α^2`
(corresponding to `m_{1,ℓ} = ⌈α_ℓ √(p_{ℓ+1} ln 2 / π)⌉`), when `8 ≤ m1` and
`1 / 2 ≤ 2 π m_1 / α^2` (so `1 - exp(-2 π m_1 / α^2) ≥ 1 - (1 + 1/2)⁻¹ = 1 / 3`),
the combined two-sided spatial truncation tail over `|d| > m_1` for any fractional offset
`δ ∈ [0, 1]` satisfies:
`(∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) +
 (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) ≤ (6 / (8 * π)) * 2^{-p_child} < 0.4 * 2^{-p_child}`. -/
theorem lemma2_sincGaussian_spatial_tail_bound
    (α δ : ℝ) (m1 p_child : ℕ) (hα : 0 < α)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hm1 : 8 ≤ m1)
    (h_win : (p_child : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2)
    (h_step : (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2) :
    (∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) +
      (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) ≤
      (6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ)) ∧
    (∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) +
      (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) <
      (0.4 : ℝ) * (2 : ℝ) ^ (-(p_child : ℤ)) := by
  have h_tails := tsum_abs_sincGaussian_tails_le α δ m1 hα hδ0 hδ1 (by omega)
  have hm1_real : (8 : ℝ) ≤ (m1 : ℝ) := by exact_mod_cast hm1
  have hpi : 0 < Real.pi := Real.pi_pos
  have h_inv_m1 : 1 / (Real.pi * (m1 : ℝ)) ≤ 1 / (8 * Real.pi) :=
    one_div_le_one_div_of_le (mul_pos (by norm_num) hpi) (by nlinarith)
  have hexp_win : Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2)) ≤ (2 : ℝ) ^ (-(p_child : ℤ)) := by
    have h1 : Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2)) ≤
        Real.exp (-((p_child : ℝ) * Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-((p_child : ℝ) * Real.log 2)) = (2 : ℝ) ^ (-(p_child : ℤ)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log zero_lt_two, zpow_neg, zpow_natCast]
    exact h1.trans_eq h2
  have h_num_le :
      (1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2)) ≤
        (1 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ)) :=
    mul_le_mul h_inv_m1 hexp_win (Real.exp_pos _).le (by positivity)
  have hexp_step : Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2)) ≤ (2 / 3 : ℝ) := by
    have h1 : Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2)) ≤ Real.exp (-(1 / 2 : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
      linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have h3 : Real.exp (-(1 / 2 : ℝ)) ≤ (2 / 3 : ℝ) := by
      rw [Real.exp_neg, inv_eq_one_div]
      have hdiv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 2) h2
      norm_num at hdiv ⊢
      exact hdiv
    exact h1.trans h3
  have h_denom : (1 / 3 : ℝ) ≤ 1 - Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2)) := by
    linarith
  have h_one_side :
      ((1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2))) /
        (1 - Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))) ≤
      (3 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ)) := by
    calc ((1 / (Real.pi * (m1 : ℝ))) * Real.exp (-(Real.pi * (m1 : ℝ) ^ 2 / α ^ 2))) /
          (1 - Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2)))
        ≤ ((1 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ))) /
            (1 - Real.exp (-(2 * Real.pi * (m1 : ℝ) / α ^ 2))) :=
          div_le_div_of_nonneg_right h_num_le (by linarith)
      _ ≤ ((1 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ))) / (1 / 3 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) h_denom
      _ = (3 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ)) := by ring
  have h_two_side :
      (∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) +
        (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) ≤
      (6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ)) := by
    calc (∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) +
          (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|)
        ≤ (3 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ)) +
            (3 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ)) :=
          add_le_add (h_tails.2.2.1.trans h_one_side) (h_tails.2.2.2.trans h_one_side)
      _ = (6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(p_child : ℤ)) := by ring
  refine ⟨h_two_side, h_two_side.trans_lt ?_⟩
  have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h8pi_pos : 0 < 8 * Real.pi := by positivity
  have h_frac_lt : 6 / (8 * Real.pi) < (0.4 : ℝ) := by
    rw [div_lt_iff₀ h8pi_pos]
    linarith
  exact mul_lt_mul_of_pos_right h_frac_lt (zpow_pos (by norm_num) _)

/-- Evaluating `dft2D` on the lattice-folded `sincGaussian` spread array equals the modulated
Poisson spatial sum on the left-hand side of `theorem2_sincGaussian_poisson_to_dft1DGrid`. -/
theorem dft2D_sincGaussian_spread_eq_poisson_lhs
    (t1 r : ℕ) (hr : 0 < r) (α : ℝ) (hα : 0 < α) (x : ℕ → ℂ) (u1 u2 : ℕ) :
    dft2D t1 r
      (fun j1 k2 =>
        ∑ j2 ∈ Finset.range r,
          x (j1 + t1 * j2) *
            ∑' l : ℤ,
              (sincGaussian α
                ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ))) : ℂ))
      u1 u2 =
    (1 / ((t1 * r : ℕ) : ℂ)) *
      (∑ j1 ∈ Finset.range t1, stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
        ∑ j2 ∈ Finset.range r, x (j1 + t1 * j2) *
          (∑' k : ℤ, (sincGaussian α (((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) - (k : ℝ)) : ℂ) *
            stdChar (((u2 : ℝ) / (r : ℝ)) * (k : ℝ)))) := by
  unfold dft2D
  congr 1
  refine Finset.sum_congr rfl fun j1 _ => ?_
  rw [Finset.mul_sum]
  trans (∑ k2 ∈ Finset.range r, ∑ j2 ∈ Finset.range r,
    stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
      (x (j1 + t1 * j2) *
        ((∑' l : ℤ,
          (sincGaussian α
            ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ))) : ℂ)) *
          stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ)))))
  · refine Finset.sum_congr rfl fun k2 _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j2 _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j2 _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum,
        sum_range_tsum_sincGaussian_lattice_fold r hr α ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) hα u2]

/-- **Composed `[MS]` Theorem 4.2 & Theorem 5.1 Bound (`sincGaussian` 2D DFT vs. 2-Term Passband, `[MS]` §4.2 & §5.1)**:
Combines `dft2D_sincGaussian_spread_eq_poisson_lhs`, `theorem2_sincGaussian_poisson_to_dft1DGrid`,
`infinite_poisson_spread_sub_passband_norm_le`, and `dft1D_norm_le` (via `dft1DGrid_eq_dft1D`):
for `p_work ≥ 8`, `t1, r > 0`, `u2 < r`, and `‖x k‖ ≤ B_X` for all `k < t1 * r`, the 2D DFT of the
lattice-folded `sincGaussian` spread differs from the 2-term passband combination
`c_0(u_2 / r) X(u_2, u_1 mod t_1) + c_1(u_2 / r) X(u_2, (u_1 - 1) mod t_1)` by at most
`0.15 * 2^{-p_work} * B_X`. -/
theorem theorem2_sincGaussian_dft2D_sub_passband_norm_le
    (p_work t1 r : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (u1 u2 : ℕ) (hu2 : u2 < r) (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 ≤ B_X)
    (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X) :
    ‖dft2D t1 r
        (fun j1 k2 =>
          ∑ j2 ∈ Finset.range r,
            x (j1 + t1 * j2) *
              ∑' l : ℤ,
                (sincGaussian (alphaSchedule p_work)
                  ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ))) : ℂ))
        u1 u2 -
      ((c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ) *
        dft1DGrid t1 r x u2 ((((u1 : ℤ) - 0).emod (t1 : ℤ)).toNat) +
       (c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ) *
        dft1DGrid t1 r x u2 ((((u1 : ℤ) - 1).emod (t1 : ℤ)).toNat))‖ ≤
      (0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X := by
  have hα : 0 < alphaSchedule p_work := alphaSchedule_pos p_work (by omega)
  rw [dft2D_sincGaussian_spread_eq_poisson_lhs t1 r hr (alphaSchedule p_work) hα x u1 u2]
  let u1_tilde : ℤ → ℕ := fun m => (((u1 : ℤ) - m).emod (t1 : ℤ)).toNat
  let q : ℤ → ℤ := fun m => ((u1 : ℤ) - m) / (t1 : ℤ)
  have hu1_mod : ∀ m : ℤ, (u1 : ℤ) - m = (u1_tilde m : ℤ) + q m * (t1 : ℤ) := by
    intro m
    dsimp [u1_tilde, q]
    change (u1 : ℤ) - m = ((((u1 : ℤ) - m) % (t1 : ℤ)).toNat : ℤ) + ((u1 : ℤ) - m) / (t1 : ℤ) * (t1 : ℤ)
    have hnonneg : 0 ≤ ((u1 : ℤ) - m) % (t1 : ℤ) := Int.emod_nonneg _ (by omega)
    rw [Int.toNat_of_nonneg hnonneg]
    have hdiv := Int.emod_add_mul_ediv ((u1 : ℤ) - m) (t1 : ℤ)
    linarith
  rw [theorem2_sincGaussian_poisson_to_dft1DGrid t1 r ht1 hr (alphaSchedule p_work) hα x
    u1 u2 u1_tilde q hu1_mod]
  let X : ℤ → ℂ := fun k => dft1DGrid t1 r x u2 ((k.emod (t1 : ℤ)).toNat)
  have hX_bound : ∀ k : ℤ, ‖X k‖ ≤ B_X := by
    intro k
    dsimp [X]
    set w : ℕ := (k.emod (t1 : ℤ)).toNat
    have hgrid : dft1DGrid t1 r x u2 w = dft1D (t1 * r) x (u2 + r * w) := by
      have hmod : (u2 + r * w) % r = u2 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu2]
      have hdiv : (u2 + r * w) / r = w := by
        rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hu2, zero_add]
      rw [← dft1DGrid_eq_dft1D t1 r x (u2 + r * w), hmod, hdiv]
    rw [hgrid]
    exact dft1D_norm_le (t1 * r) (Nat.mul_pos ht1 hr) x B_X
      (fun j hj => hx j (Finset.mem_range.mp hj)) (u2 + r * w)
  have hy0 : 0 ≤ (u2 : ℝ) / (r : ℝ) := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hy1 : (u2 : ℝ) / (r : ℝ) ≤ 1 :=
    (div_le_one (Nat.cast_pos.mpr hr)).mpr (by exact_mod_cast hu2.le)
  have hbound := infinite_poisson_spread_sub_passband_norm_le p_work hp
    ((u2 : ℝ) / (r : ℝ)) hy0 hy1 X B_X hB hX_bound (u1 : ℤ)
  have hX0 : X (u1 : ℤ) = dft1DGrid t1 r x u2 ((((u1 : ℤ) - 0).emod (t1 : ℤ)).toNat) := by
    dsimp [X]
    rw [sub_zero]
  rw [← hX0]
  exact hbound

/-! ## 2. `[MS]` Theorem 5.1(2) (§5.1): Cyclic 2-Term Bidiagonal Solver & Uniform Conditioning -/

/-- Particular solution recurrence for the forward bidiagonal sweep (`c_0 ≥ c_1`):
`Z_part(0) = 0`, `Z_part(u_1 + 1) = Y(u_1 + 1) / c_0 + (-c_1 / c_0) * Z_part(u_1)`. -/
noncomputable def zPartFwd (c0 c1 : ℂ) (Y : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | u1 + 1 => Y (u1 + 1) / c0 + (-c1 / c0) * zPartFwd c0 c1 Y u1

@[simp]
theorem zPartFwd_succ (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) :
    zPartFwd c0 c1 Y (u1 + 1) = Y (u1 + 1) / c0 + (-c1 / c0) * zPartFwd c0 c1 Y u1 :=
  rfl

/-- Homogeneous solution `Z_hom(u_1) = (-c_1 / c_0)^{u_1}` for the forward bidiagonal sweep. -/
noncomputable def zHomFwd (c0 c1 : ℂ) (u1 : ℕ) : ℂ :=
  (-c1 / c0) ^ u1

/-- Reconstructed column vector `Z(u_1) = Z_part(u_1) + Z_0 * Z_hom(u_1)` where `Z_0` is solved
from the cyclic boundary condition at `u_1 = 0`. -/
noncomputable def solveBidiagonalFwd (t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) : ℂ :=
  let Z0 := (Y 0 - c1 * zPartFwd c0 c1 Y (t1 - 1)) / (c0 + c1 * zHomFwd c0 c1 (t1 - 1))
  zPartFwd c0 c1 Y u1 + Z0 * zHomFwd c0 c1 u1

/-- **`[MS]` Theorem 5.1 (Part 2a: Exact Satisfaction of Interior Bidiagonal Equations)**:
For `c_0 ≠ 0` and every `u_1 ∈ ℕ`, `solveBidiagonalFwd` satisfies
`c_0 Z(u_1 + 1) + c_1 Z(u_1) = Y(u_1 + 1)` identically. -/
theorem theorem3_bidiagonal_fwd_interior_exact
    (t1 : ℕ) (c0 c1 : ℂ) (hc0 : c0 ≠ 0) (Y : ℕ → ℂ) (u1 : ℕ) :
    c0 * solveBidiagonalFwd t1 c0 c1 Y (u1 + 1) +
      c1 * solveBidiagonalFwd t1 c0 c1 Y u1 = Y (u1 + 1) := by
  unfold solveBidiagonalFwd zHomFwd
  dsimp only
  rw [zPartFwd_succ, pow_succ]
  field_simp [hc0]
  ring

/-- **`[MS]` Theorem 5.1 (Part 2b: Exact Satisfaction of Cyclic Wrap-Around Boundary Equation)**:
For `t_1 ≥ 1` and non-vanishing cyclic determinant `c_0 + c_1 (-c_1 / c_0)^{t_1 - 1} ≠ 0`,
`solveBidiagonalFwd` satisfies `c_0 Z(0) + c_1 Z(t_1 - 1) = Y(0)` identically. -/
theorem theorem3_bidiagonal_fwd_boundary_exact
    (t1 : ℕ) (c0 c1 : ℂ) (hdenom : c0 + c1 * zHomFwd c0 c1 (t1 - 1) ≠ 0) (Y : ℕ → ℂ) :
    c0 * solveBidiagonalFwd t1 c0 c1 Y 0 +
      c1 * solveBidiagonalFwd t1 c0 c1 Y (t1 - 1) = Y 0 := by
  unfold solveBidiagonalFwd
  dsimp only
  have hz0_part : zPartFwd c0 c1 Y 0 = 0 := rfl
  have hz0_hom : zHomFwd c0 c1 0 = 1 := rfl
  rw [hz0_part, hz0_hom]
  field_simp [hdenom]
  ring

/-- **`[MS]` Theorem 5.1 (Part 2c: Uniform Conditioning Bound `< 2.36 t_1`, `[MS]` §5.1, eq. (24))**:
For `M ≥ 0.49999999` and cyclic wrap-around ratio `ratio_t1 ≤ 0.15`, the cyclic boundary
denominator `M * (1 - ratio_t1)` is strictly `> 0.424`, and the error amplification factor
`1 / (M * (1 - ratio_t1))` is strictly `< 2.36`. -/
theorem theorem3_bidiagonal_conditioning
    (M ratio_t1 : ℝ) (hM : (0.49999999 : ℝ) ≤ M) (hratio : ratio_t1 ≤ (0.15 : ℝ)) :
    (0.424 : ℝ) < M * (1 - ratio_t1) ∧
    1 / (M * (1 - ratio_t1)) < (2.36 : ℝ) := by
  have hdenom : (0.424 : ℝ) < M * (1 - ratio_t1) := by nlinarith
  refine ⟨hdenom, ?_⟩
  have hpos : (0 : ℝ) < M * (1 - ratio_t1) := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- **`[MS]` Theorem 5.1 (Part 2d: Perturbation / Error Amplification Bound of Forward Bidiagonal Sweep)**:
If `‖c0‖ ≥ M > 0`, `‖c1 / c0‖ ≤ ρ < 1` (`0 ≤ ρ`), and two right-hand side vectors `Y, Y' : ℕ → ℂ`
satisfy `‖Y' u - Y u‖ ≤ ε` (`0 ≤ ε`) for all `u`, then for every row `u1 ∈ ℕ`:
`‖zPartFwd c0 c1 Y' u1 - zPartFwd c0 c1 Y u1‖ ≤ ε / (M * (1 - ρ))`. -/
theorem zPartFwd_error_amplification_bound
    (c0 c1 : ℂ) (M ρ ε : ℝ)
    (hM : 0 < M) (hc0 : M ≤ ‖c0‖)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hratio : ‖c1 / c0‖ ≤ ρ)
    (hε : 0 ≤ ε) (Y Y' : ℕ → ℂ) (hY : ∀ u, ‖Y' u - Y u‖ ≤ ε)
    (u1 : ℕ) :
    ‖zPartFwd c0 c1 Y' u1 - zPartFwd c0 c1 Y u1‖ ≤ ε / (M * (1 - ρ)) := by
  have h1m : 0 < 1 - ρ := by linarith
  have hM1m : 0 < M * (1 - ρ) := mul_pos hM h1m
  induction u1 with
  | zero =>
    simp only [zPartFwd, sub_self, norm_zero]
    exact div_nonneg hε hM1m.le
  | succ u1 ih =>
    simp only [zPartFwd_succ]
    have hsplit : (Y' (u1 + 1) / c0 + -c1 / c0 * zPartFwd c0 c1 Y' u1) -
        (Y (u1 + 1) / c0 + -c1 / c0 * zPartFwd c0 c1 Y u1) =
        (Y' (u1 + 1) - Y (u1 + 1)) / c0 +
          (-(c1 / c0)) * (zPartFwd c0 c1 Y' u1 - zPartFwd c0 c1 Y u1) := by ring
    rw [hsplit]
    have htri := norm_add_le ((Y' (u1 + 1) - Y (u1 + 1)) / c0)
      ((-(c1 / c0)) * (zPartFwd c0 c1 Y' u1 - zPartFwd c0 c1 Y u1))
    rw [norm_div, norm_mul, norm_neg] at htri
    have hc0_pos : 0 < ‖c0‖ := lt_of_lt_of_le hM hc0
    have hterm1 : ‖Y' (u1 + 1) - Y (u1 + 1)‖ / ‖c0‖ ≤ ε / M := by
      calc ‖Y' (u1 + 1) - Y (u1 + 1)‖ / ‖c0‖
          ≤ ε / ‖c0‖ := div_le_div_of_nonneg_right (hY (u1 + 1)) hc0_pos.le
        _ ≤ ε / M := div_le_div_of_nonneg_left hε hM hc0
    have hterm2 : ‖c1 / c0‖ * ‖zPartFwd c0 c1 Y' u1 - zPartFwd c0 c1 Y u1‖ ≤
        ρ * (ε / (M * (1 - ρ))) :=
      mul_le_mul hratio ih (norm_nonneg _) hρ0
    have hident : ε / M + ρ * (ε / (M * (1 - ρ))) = ε / (M * (1 - ρ)) := by
      have hM_ne : M ≠ 0 := hM.ne'
      have h1m_ne : 1 - ρ ≠ 0 := h1m.ne'
      field_simp [hM_ne, h1m_ne]
      ring
    linarith

/-- Closed-form expression for `zPartFwd c0 c1 Y u1` for `u1 < t1` when `Y` is generated from `X` by
`Y (u1 + 1) = c0 * X (u1 + 1) + c1 * X u1` for all `u1 + 1 < t1`:
`zPartFwd c0 c1 Y u1 = X u1 - X 0 * zHomFwd c0 c1 u1`. -/
theorem zPartFwd_eq_sub_zHomFwd
    (c0 c1 : ℂ) (t1 : ℕ) (hc0 : c0 ≠ 0) (X Y : ℕ → ℂ)
    (h_int : ∀ u1 : ℕ, u1 + 1 < t1 → Y (u1 + 1) = c0 * X (u1 + 1) + c1 * X u1)
    (u1 : ℕ) (hu1 : u1 < t1) :
    zPartFwd c0 c1 Y u1 = X u1 - X 0 * zHomFwd c0 c1 u1 := by
  induction u1 with
  | zero =>
    simp [zPartFwd, zHomFwd]
  | succ u1 ih =>
    unfold zHomFwd at ih ⊢
    rw [zPartFwd_succ, pow_succ, h_int u1 hu1, ih (Nat.lt_of_succ_lt hu1)]
    field_simp [hc0]
    ring

/-- **`[MS]` Theorem 5.1 (Part 2e: Exact Left-Inverse / Mode Recovery of `solveBidiagonalFwd`)**:
If `Y : ℕ → ℂ` is generated from the true 1D DFT mode vector `X : ℕ → ℂ` by the cyclic 2-term
passband relation `Y 0 = c0 * X 0 + c1 * X (t1 - 1)` and `Y (u1 + 1) = c0 * X (u1 + 1) + c1 * X u1`
for all `u1 + 1 < t1`, then `solveBidiagonalFwd t1 c0 c1 Y u1 = X u1` for all `u1 < t1`. -/
theorem solveBidiagonalFwd_recover_exact
    (t1 : ℕ) (c0 c1 : ℂ) (ht1 : 0 < t1) (hc0 : c0 ≠ 0)
    (hdenom : c0 + c1 * zHomFwd c0 c1 (t1 - 1) ≠ 0)
    (X Y : ℕ → ℂ)
    (h_bnd : Y 0 = c0 * X 0 + c1 * X (t1 - 1))
    (h_int : ∀ u1 : ℕ, u1 + 1 < t1 → Y (u1 + 1) = c0 * X (u1 + 1) + c1 * X u1)
    (u1 : ℕ) (hu1 : u1 < t1) :
    solveBidiagonalFwd t1 c0 c1 Y u1 = X u1 := by
  unfold solveBidiagonalFwd
  dsimp only
  have ht1_sub : t1 - 1 < t1 := Nat.sub_lt ht1 zero_lt_one
  rw [zPartFwd_eq_sub_zHomFwd c0 c1 t1 hc0 X Y h_int (t1 - 1) ht1_sub,
      zPartFwd_eq_sub_zHomFwd c0 c1 t1 hc0 X Y h_int u1 hu1,
      h_bnd]
  field_simp [hdenom]
  ring

/-- Helper: if `0 < c0`, `0 < c1`, and `c0 ≠ c1`, then `c0 + c1 * (-c1 / c0) ^ n ≠ 0` for all `n : ℕ`. -/
theorem real_bidiagonal_denom_ne_zero (c0 c1 : ℝ) (n : ℕ)
    (hc0 : 0 < c0) (hc1 : 0 < c1) (hne : c0 ≠ c1) :
    c0 + c1 * (-c1 / c0) ^ n ≠ 0 := by
  intro hzero
  have heq : c1 * (-c1 / c0) ^ n = -c0 := by linarith
  have habs := congrArg abs heq
  simp only [abs_mul, abs_pow, abs_div, abs_neg, abs_of_pos hc0, abs_of_pos hc1] at habs
  rcases lt_trichotomy c1 c0 with hlt | rfl | hgt
  · have hdiv_nonneg : 0 ≤ c1 / c0 := div_nonneg hc1.le hc0.le
    have hdiv_le : c1 / c0 ≤ 1 := (div_le_one hc0).mpr hlt.le
    have hpow_le : (c1 / c0) ^ n ≤ 1 := pow_le_one₀ hdiv_nonneg hdiv_le
    have hmul_le : c1 * (c1 / c0) ^ n ≤ c1 := by nlinarith
    linarith
  · exact hne rfl
  · have hdiv_ge : 1 ≤ c1 / c0 := (one_le_div hc0).mpr hgt.le
    have hpow_ge : 1 ≤ (c1 / c0) ^ n := one_le_pow₀ hdiv_ge
    have hmul_ge : c1 ≤ c1 * (c1 / c0) ^ n := by nlinarith
    linarith

/-- **Non-Vanishing of the Cyclic Bidiagonal Denominator off Nyquist (`y ≠ 1/2`)**:
For `α > 0`, `t1 > 0`, and `y ∈ [0, 1]` with `y ≠ 1 / 2`, the cyclic bidiagonal denominator
`c_0(y) + c_1(y) * (-c_1(y) / c_0(y))^{t_1 - 1}` is strictly non-zero in `ℂ`. -/
theorem c0_c1_realErfScaled_denom_ne_zero (α y : ℝ) (t1 : ℕ) (hα : 0 < α) (ht1 : 0 < t1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hne : y ≠ 1 / 2) :
    (c0Coeff (realErfScaled α) y : ℂ) +
      (c1Coeff (realErfScaled α) y : ℂ) *
        zHomFwd (c0Coeff (realErfScaled α) y : ℂ) (c1Coeff (realErfScaled α) y : ℂ) (t1 - 1) ≠ 0 := by
  have _ := ht1
  unfold zHomFwd
  have hc0 : 0 < c0Coeff (realErfScaled α) y := c0Coeff_realErfScaled_pos α y hα
  have hc1 : 0 < c1Coeff (realErfScaled α) y := c1Coeff_realErfScaled_pos α y hα
  have hne_c : c0Coeff (realErfScaled α) y ≠ c1Coeff (realErfScaled α) y :=
    c0Coeff_ne_c1Coeff_of_ne_half α y hα hy0 hy1 hne
  have hreal := real_bidiagonal_denom_ne_zero
    (c0Coeff (realErfScaled α) y) (c1Coeff (realErfScaled α) y) (t1 - 1) hc0 hc1 hne_c
  exact_mod_cast hreal

/-- Particular solution recurrence for the backward bidiagonal sweep (`c_1 ≥ c_0`),
indexed by distance `d = t_1 - 1 - u_1` down from `u_1 = t_1 - 1`:
`zPartBwd(0) = 0`, `zPartBwd(d + 1) = Y(t_1 - 1 - d) / c_1 + (-c_0 / c_1) * zPartBwd(d)`. -/
noncomputable def zPartBwd (t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | d + 1 => Y (t1 - 1 - d) / c1 + (-c0 / c1) * zPartBwd t1 c0 c1 Y d

@[simp]
theorem zPartBwd_succ (t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (d : ℕ) :
    zPartBwd t1 c0 c1 Y (d + 1) = Y (t1 - 1 - d) / c1 + (-c0 / c1) * zPartBwd t1 c0 c1 Y d :=
  rfl

/-- Homogeneous solution `zHomBwd(d) = (-c_0 / c_1)^d` for the backward bidiagonal sweep. -/
noncomputable def zHomBwd (c0 c1 : ℂ) (d : ℕ) : ℂ :=
  (-c0 / c1) ^ d

/-- Reconstructed column vector `Z(u_1)` via backward cyclic bidiagonal sweep from `t_1 - 1` down to `0`. -/
noncomputable def solveBidiagonalBwd (t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) : ℂ :=
  let d := t1 - 1 - u1
  let Z_last := (Y 0 - c0 * zPartBwd t1 c0 c1 Y (t1 - 1)) / (c1 + c0 * zHomBwd c0 c1 (t1 - 1))
  zPartBwd t1 c0 c1 Y d + Z_last * zHomBwd c0 c1 d

/-- **`[MS]` Theorem 5.1 (Perturbation / Error Amplification Bound of Backward Bidiagonal Sweep)**:
If `‖c1‖ ≥ M > 0`, `‖c0 / c1‖ ≤ ρ < 1` (`0 ≤ ρ`), and two right-hand side vectors `Y, Y' : ℕ → ℂ`
satisfy `‖Y' u - Y u‖ ≤ ε` (`0 ≤ ε`) for all `u`, then for every step `d ∈ ℕ`:
`‖zPartBwd t1 c0 c1 Y' d - zPartBwd t1 c0 c1 Y d‖ ≤ ε / (M * (1 - ρ))`. -/
theorem zPartBwd_error_amplification_bound
    (t1 : ℕ) (c0 c1 : ℂ) (M ρ ε : ℝ)
    (hM : 0 < M) (hc1 : M ≤ ‖c1‖)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hratio : ‖c0 / c1‖ ≤ ρ)
    (hε : 0 ≤ ε) (Y Y' : ℕ → ℂ) (hY : ∀ u, ‖Y' u - Y u‖ ≤ ε)
    (d : ℕ) :
    ‖zPartBwd t1 c0 c1 Y' d - zPartBwd t1 c0 c1 Y d‖ ≤ ε / (M * (1 - ρ)) := by
  have h1m : 0 < 1 - ρ := by linarith
  have hM1m : 0 < M * (1 - ρ) := mul_pos hM h1m
  induction d with
  | zero =>
    simp only [zPartBwd, sub_self, norm_zero]
    exact div_nonneg hε hM1m.le
  | succ d ih =>
    simp only [zPartBwd_succ]
    have hsplit : (Y' (t1 - 1 - d) / c1 + -c0 / c1 * zPartBwd t1 c0 c1 Y' d) -
        (Y (t1 - 1 - d) / c1 + -c0 / c1 * zPartBwd t1 c0 c1 Y d) =
        (Y' (t1 - 1 - d) - Y (t1 - 1 - d)) / c1 +
          (-(c0 / c1)) * (zPartBwd t1 c0 c1 Y' d - zPartBwd t1 c0 c1 Y d) := by ring
    rw [hsplit]
    have htri := norm_add_le ((Y' (t1 - 1 - d) - Y (t1 - 1 - d)) / c1)
      ((-(c0 / c1)) * (zPartBwd t1 c0 c1 Y' d - zPartBwd t1 c0 c1 Y d))
    rw [norm_div, norm_mul, norm_neg] at htri
    have hc1_pos : 0 < ‖c1‖ := lt_of_lt_of_le hM hc1
    have hterm1 : ‖Y' (t1 - 1 - d) - Y (t1 - 1 - d)‖ / ‖c1‖ ≤ ε / M := by
      calc ‖Y' (t1 - 1 - d) - Y (t1 - 1 - d)‖ / ‖c1‖
          ≤ ε / ‖c1‖ := div_le_div_of_nonneg_right (hY (t1 - 1 - d)) hc1_pos.le
        _ ≤ ε / M := div_le_div_of_nonneg_left hε hM hc1
    have hterm2 : ‖c0 / c1‖ * ‖zPartBwd t1 c0 c1 Y' d - zPartBwd t1 c0 c1 Y d‖ ≤
        ρ * (ε / (M * (1 - ρ))) :=
      mul_le_mul hratio ih (norm_nonneg _) hρ0
    have hident : ε / M + ρ * (ε / (M * (1 - ρ))) = ε / (M * (1 - ρ)) := by
      have hM_ne : M ≠ 0 := hM.ne'
      have h1m_ne : 1 - ρ ≠ 0 := h1m.ne'
      field_simp [hM_ne, h1m_ne]
      ring
    linarith

/-- Closed-form expression for `zPartBwd t1 c0 c1 Y d` for `d < t1` when `Y` is generated from `X` by
`Y (u1 + 1) = c0 * X (u1 + 1) + c1 * X u1` for all `u1 + 1 < t1`:
`zPartBwd t1 c0 c1 Y d = X (t1 - 1 - d) - X (t1 - 1) * zHomBwd c0 c1 d`. -/
theorem zPartBwd_eq_sub_zHomBwd
    (t1 : ℕ) (c0 c1 : ℂ) (hc1 : c1 ≠ 0) (X Y : ℕ → ℂ)
    (h_int : ∀ u1 : ℕ, u1 + 1 < t1 → Y (u1 + 1) = c0 * X (u1 + 1) + c1 * X u1)
    (d : ℕ) (hd : d < t1) :
    zPartBwd t1 c0 c1 Y d = X (t1 - 1 - d) - X (t1 - 1) * zHomBwd c0 c1 d := by
  induction d with
  | zero =>
    simp [zPartBwd, zHomBwd]
  | succ d ih =>
    unfold zHomBwd at ih ⊢
    have hu1_eq : t1 - 1 - d = (t1 - 1 - (d + 1)) + 1 := by omega
    have hu1_lt : (t1 - 1 - (d + 1)) + 1 < t1 := by omega
    have hY_d : Y (t1 - 1 - d) = c0 * X (t1 - 1 - d) + c1 * X (t1 - 1 - (d + 1)) := by
      rw [hu1_eq, h_int (t1 - 1 - (d + 1)) hu1_lt]
    rw [zPartBwd_succ, pow_succ, hY_d, ih (Nat.lt_of_succ_lt hd)]
    field_simp [hc1]
    ring

/-- **`[MS]` Theorem 5.1 (Exact Left-Inverse / Mode Recovery of `solveBidiagonalBwd`)**:
If `Y : ℕ → ℂ` is generated from the true 1D DFT mode vector `X : ℕ → ℂ` by the cyclic 2-term
passband relation `Y 0 = c0 * X 0 + c1 * X (t1 - 1)` and `Y (u1 + 1) = c0 * X (u1 + 1) + c1 * X u1`
for all `u1 + 1 < t1`, then `solveBidiagonalBwd t1 c0 c1 Y u1 = X u1` for all `u1 < t1`. -/
theorem solveBidiagonalBwd_recover_exact
    (t1 : ℕ) (c0 c1 : ℂ) (ht1 : 0 < t1) (hc1 : c1 ≠ 0)
    (hdenom : c1 + c0 * zHomBwd c0 c1 (t1 - 1) ≠ 0)
    (X Y : ℕ → ℂ)
    (h_bnd : Y 0 = c0 * X 0 + c1 * X (t1 - 1))
    (h_int : ∀ u1 : ℕ, u1 + 1 < t1 → Y (u1 + 1) = c0 * X (u1 + 1) + c1 * X u1)
    (u1 : ℕ) (hu1 : u1 < t1) :
    solveBidiagonalBwd t1 c0 c1 Y u1 = X u1 := by
  unfold solveBidiagonalBwd
  dsimp only
  have ht1_sub : t1 - 1 < t1 := Nat.sub_lt ht1 zero_lt_one
  have hd_lt : t1 - 1 - u1 < t1 := by omega
  have hu1_sub : t1 - 1 - (t1 - 1 - u1) = u1 := by omega
  rw [zPartBwd_eq_sub_zHomBwd t1 c0 c1 hc1 X Y h_int (t1 - 1) ht1_sub,
      zPartBwd_eq_sub_zHomBwd t1 c0 c1 hc1 X Y h_int (t1 - 1 - u1) hd_lt,
      Nat.sub_self, hu1_sub, h_bnd]
  field_simp [hdenom]
  ring

/-- **Non-Vanishing of the Backward Cyclic Bidiagonal Denominator off Nyquist (`y ≠ 1/2`)**:
For `α > 0`, `t1 > 0`, and `y ∈ [0, 1]` with `y ≠ 1 / 2`, the backward cyclic bidiagonal
denominator `c_1(y) + c_0(y) * (-c_0(y) / c_1(y))^{t_1 - 1}` is strictly non-zero in `ℂ`. -/
theorem c0_c1_realErfScaled_bwd_denom_ne_zero (α y : ℝ) (t1 : ℕ) (hα : 0 < α) (ht1 : 0 < t1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hne : y ≠ 1 / 2) :
    (c1Coeff (realErfScaled α) y : ℂ) +
      (c0Coeff (realErfScaled α) y : ℂ) *
        zHomBwd (c0Coeff (realErfScaled α) y : ℂ) (c1Coeff (realErfScaled α) y : ℂ) (t1 - 1) ≠ 0 := by
  have _ := ht1
  unfold zHomBwd
  have hc0 : 0 < c0Coeff (realErfScaled α) y := c0Coeff_realErfScaled_pos α y hα
  have hc1 : 0 < c1Coeff (realErfScaled α) y := c1Coeff_realErfScaled_pos α y hα
  have hne_c : c1Coeff (realErfScaled α) y ≠ c0Coeff (realErfScaled α) y :=
    (c0Coeff_ne_c1Coeff_of_ne_half α y hα hy0 hy1 hne).symm
  have hreal := real_bidiagonal_denom_ne_zero
    (c1Coeff (realErfScaled α) y) (c0Coeff (realErfScaled α) y) (t1 - 1) hc1 hc0 hne_c
  exact_mod_cast hreal

/-- Linearity of `zPartFwd` with respect to subtraction of right-hand side vectors. -/
theorem zPartFwd_sub (c0 c1 : ℂ) (Y Y' : ℕ → ℂ) (u1 : ℕ) :
    zPartFwd c0 c1 Y' u1 - zPartFwd c0 c1 Y u1 =
      zPartFwd c0 c1 (fun k => Y' k - Y k) u1 := by
  induction u1 with
  | zero => simp [zPartFwd]
  | succ u1 ih =>
    simp only [zPartFwd_succ, ← ih]
    ring

/-- Linearity of `solveBidiagonalFwd` with respect to subtraction of right-hand side vectors. -/
theorem solveBidiagonalFwd_sub (t1 : ℕ) (c0 c1 : ℂ) (Y Y' : ℕ → ℂ) (u1 : ℕ) :
    solveBidiagonalFwd t1 c0 c1 Y' u1 - solveBidiagonalFwd t1 c0 c1 Y u1 =
      solveBidiagonalFwd t1 c0 c1 (fun k => Y' k - Y k) u1 := by
  unfold solveBidiagonalFwd
  dsimp only
  rw [← zPartFwd_sub c0 c1 Y Y' u1, ← zPartFwd_sub c0 c1 Y Y' (t1 - 1)]
  ring

/-- Finite-horizon open-loop norm bound for `zPartFwd` when `‖c1‖ ≤ ‖c0‖` and `0 < M ≤ ‖c0‖`. -/
theorem zPartFwd_norm_le_linear
    (c0 c1 : ℂ) (ΔY : ℕ → ℂ) (M ε : ℝ) (u1 : ℕ)
    (hM_pos : 0 < M) (hM : M ≤ ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖) (hε : 0 ≤ ε)
    (hΔY : ∀ k : ℕ, ‖ΔY k‖ ≤ ε) :
    ‖zPartFwd c0 c1 ΔY u1‖ ≤ (u1 : ℝ) * (ε / M) := by
  have hc0_pos : 0 < ‖c0‖ := lt_of_lt_of_le hM_pos hM
  have hratio_le : ‖-c1 / c0‖ ≤ 1 := by
    rw [norm_div, norm_neg]
    exact (div_le_one hc0_pos).mpr hc10
  induction u1 with
  | zero =>
    simp [zPartFwd]
  | succ u1 ih =>
    rw [zPartFwd_succ]
    have htri := norm_add_le (ΔY (u1 + 1) / c0) ((-c1 / c0) * zPartFwd c0 c1 ΔY u1)
    rw [norm_div, norm_mul] at htri
    have h1 : ‖ΔY (u1 + 1)‖ / ‖c0‖ ≤ ε / M := by
      calc ‖ΔY (u1 + 1)‖ / ‖c0‖
          ≤ ε / ‖c0‖ := div_le_div_of_nonneg_right (hΔY (u1 + 1)) hc0_pos.le
        _ ≤ ε / M := div_le_div_of_nonneg_left hε hM_pos hM
    have h2 : ‖-c1 / c0‖ * ‖zPartFwd c0 c1 ΔY u1‖ ≤ 1 * ((u1 : ℝ) * (ε / M)) :=
      mul_le_mul hratio_le ih (norm_nonneg _) zero_le_one
    push_cast
    linarith

/-- **Finite-Horizon Open-Loop Perturbation Bound for `zPartFwd` (`‖c1‖ ≤ ‖c0‖`)**:
Without assuming a strict geometric contraction `ρ < 1`, if `0 < M ≤ ‖c0‖` and `‖c1‖ ≤ ‖c0‖`,
then `‖zPartFwd c0 c1 Y' u1 - zPartFwd c0 c1 Y u1‖ ≤ u1 * (ε / M)`. -/
theorem zPartFwd_norm_sub_le_linear
    (c0 c1 : ℂ) (Y Y' : ℕ → ℂ) (M ε : ℝ) (u1 : ℕ)
    (hM_pos : 0 < M) (hM : M ≤ ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖) (hε : 0 ≤ ε)
    (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε) :
    ‖zPartFwd c0 c1 Y' u1 - zPartFwd c0 c1 Y u1‖ ≤ (u1 : ℝ) * (ε / M) := by
  rw [zPartFwd_sub]
  exact zPartFwd_norm_le_linear c0 c1 (fun k => Y' k - Y k) M ε u1 hM_pos hM hc10 hε hY

/-- Shift-offset decomposition of the forward particular sweep `zPartFwd`:
for any `u1, m : ℕ`, `zPartFwd c0 c1 Y (u1 + m)` splits into `(-c1 / c0) ^ m * zPartFwd c0 c1 Y u1`
plus the `m`-step forward sweep starting from offset `u1`. -/
theorem zPartFwd_add_offset
    (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 m : ℕ) :
    zPartFwd c0 c1 Y (u1 + m) =
      (-c1 / c0) ^ m * zPartFwd c0 c1 Y u1 + zPartFwd c0 c1 (fun j => Y (u1 + j)) m := by
  induction m with
  | zero =>
    simp [zPartFwd]
  | succ m ih =>
    rw [← Nat.add_assoc, zPartFwd_succ, ih, zPartFwd_succ, pow_succ']
    ring

/-- **Exact Cyclic Telescoping Identity for `solveBidiagonalFwd` (`u1 < t1`)**:
Multiplying `solveBidiagonalFwd t1 c0 c1 Y u1` by the cyclic determinant
`denom = c0 + c1 * zHomFwd c0 c1 (t1 - 1)` cancels the wrap-around term in `zPartFwd c0 c1 Y u1`,
leaving a sum of `u1` steps before `u1`, the boundary term `Y 0`, and `t1 - 1 - u1` steps after `u1`. -/
theorem denom_mul_solveBidiagonalFwd_eq
    (t1 : ℕ) (c0 c1 : ℂ) (hdenom : c0 + c1 * zHomFwd c0 c1 (t1 - 1) ≠ 0)
    (Y : ℕ → ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    (c0 + c1 * zHomFwd c0 c1 (t1 - 1)) * solveBidiagonalFwd t1 c0 c1 Y u1 =
      c0 * zPartFwd c0 c1 Y u1 +
      zHomFwd c0 c1 u1 * Y 0 -
      c1 * zHomFwd c0 c1 u1 * zPartFwd c0 c1 (fun j => Y (u1 + j)) (t1 - 1 - u1) := by
  have h1 : (c0 + c1 * zHomFwd c0 c1 (t1 - 1)) * solveBidiagonalFwd t1 c0 c1 Y u1 =
      (c0 + c1 * zHomFwd c0 c1 (t1 - 1)) * zPartFwd c0 c1 Y u1 +
      (Y 0 - c1 * zPartFwd c0 c1 Y (t1 - 1)) * zHomFwd c0 c1 u1 := by
    unfold solveBidiagonalFwd
    dsimp only
    field_simp [hdenom]
  have hm : u1 + (t1 - 1 - u1) = t1 - 1 := by omega
  have hpart : zPartFwd c0 c1 Y (t1 - 1) =
      (-c1 / c0) ^ (t1 - 1 - u1) * zPartFwd c0 c1 Y u1 +
      zPartFwd c0 c1 (fun j => Y (u1 + j)) (t1 - 1 - u1) := by
    conv_lhs => rw [← hm]
    exact zPartFwd_add_offset c0 c1 Y u1 (t1 - 1 - u1)
  have hhom : zHomFwd c0 c1 (t1 - 1) = (-c1 / c0) ^ (t1 - 1 - u1) * zHomFwd c0 c1 u1 := by
    unfold zHomFwd
    conv_lhs => rw [← hm]
    rw [pow_add, mul_comm]
  rw [h1, hpart, hhom]
  ring

/-- Uniform `t1 * ε` upper bound on `‖(c0 + c1 * zHomFwd c0 c1 (t1 - 1)) * solveBidiagonalFwd t1 c0 c1 ΔY u1‖`
for all `u1 < t1` when `0 < ‖c0‖`, `‖c1‖ ≤ ‖c0‖`, and `∀ k, ‖ΔY k‖ ≤ ε`. -/
theorem norm_denom_mul_solveBidiagonalFwd_le
    (t1 : ℕ) (c0 c1 : ℂ) (hc0_pos : 0 < ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖)
    (hdenom : c0 + c1 * zHomFwd c0 c1 (t1 - 1) ≠ 0)
    (ΔY : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hΔY : ∀ k : ℕ, ‖ΔY k‖ ≤ ε)
    (u1 : ℕ) (hu1 : u1 < t1) :
    ‖(c0 + c1 * zHomFwd c0 c1 (t1 - 1)) * solveBidiagonalFwd t1 c0 c1 ΔY u1‖ ≤
      (t1 : ℝ) * ε := by
  rw [denom_mul_solveBidiagonalFwd_eq t1 c0 c1 hdenom ΔY u1 hu1]
  have hhom_le : ‖zHomFwd c0 c1 u1‖ ≤ 1 := by
    unfold zHomFwd
    rw [norm_pow, norm_div, norm_neg]
    exact pow_le_one₀ (div_nonneg (norm_nonneg _) hc0_pos.le) ((div_le_one hc0_pos).mpr hc10)
  have hpart1 := zPartFwd_norm_le_linear c0 c1 ΔY ‖c0‖ ε u1 hc0_pos le_rfl hc10 hε hΔY
  have hpart2 := zPartFwd_norm_le_linear c0 c1 (fun j => ΔY (u1 + j)) ‖c0‖ ε (t1 - 1 - u1)
    hc0_pos le_rfl hc10 hε (fun j => hΔY (u1 + j))
  have ht1 : ‖c0 * zPartFwd c0 c1 ΔY u1‖ ≤ (u1 : ℝ) * ε := by
    rw [norm_mul]
    calc ‖c0‖ * ‖zPartFwd c0 c1 ΔY u1‖
        ≤ ‖c0‖ * ((u1 : ℝ) * (ε / ‖c0‖)) := mul_le_mul_of_nonneg_left hpart1 hc0_pos.le
      _ = (u1 : ℝ) * ε := by field_simp [hc0_pos.ne']
  have ht2 : ‖zHomFwd c0 c1 u1 * ΔY 0‖ ≤ ε := by
    rw [norm_mul]
    calc ‖zHomFwd c0 c1 u1‖ * ‖ΔY 0‖
        ≤ 1 * ε := mul_le_mul hhom_le (hΔY 0) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  have ht3 : ‖c1 * zHomFwd c0 c1 u1 * zPartFwd c0 c1 (fun j => ΔY (u1 + j)) (t1 - 1 - u1)‖ ≤
      ((t1 - 1 - u1 : ℕ) : ℝ) * ε := by
    rw [norm_mul, norm_mul]
    have hc1_hom : ‖c1‖ * ‖zHomFwd c0 c1 u1‖ ≤ ‖c0‖ := by
      calc ‖c1‖ * ‖zHomFwd c0 c1 u1‖
          ≤ ‖c0‖ * 1 := mul_le_mul hc10 hhom_le (norm_nonneg _) hc0_pos.le
        _ = ‖c0‖ := mul_one _
    calc ‖c1‖ * ‖zHomFwd c0 c1 u1‖ * ‖zPartFwd c0 c1 (fun j => ΔY (u1 + j)) (t1 - 1 - u1)‖
        ≤ ‖c0‖ * (((t1 - 1 - u1 : ℕ) : ℝ) * (ε / ‖c0‖)) :=
          mul_le_mul hc1_hom hpart2 (norm_nonneg _) hc0_pos.le
      _ = ((t1 - 1 - u1 : ℕ) : ℝ) * ε := by field_simp [hc0_pos.ne']
  have htri1 := norm_sub_le (c0 * zPartFwd c0 c1 ΔY u1 + zHomFwd c0 c1 u1 * ΔY 0)
    (c1 * zHomFwd c0 c1 u1 * zPartFwd c0 c1 (fun j => ΔY (u1 + j)) (t1 - 1 - u1))
  have htri2 := norm_add_le (c0 * zPartFwd c0 c1 ΔY u1) (zHomFwd c0 c1 u1 * ΔY 0)
  have hnat : (u1 : ℝ) + 1 + ((t1 - 1 - u1 : ℕ) : ℝ) = (t1 : ℝ) := by
    have : u1 + 1 + (t1 - 1 - u1) = t1 := by omega
    exact_mod_cast this
  nlinarith

/-- **`[MS]` Theorem 5.1 (Full Cyclic Perturbation Bound `< 2.36 * t_1 * ε` for `solveBidiagonalFwd`, `[MS]` §5.1, eq. (24))**:
For `t1 > 0`, `0.49999999 ≤ M ≤ ‖c0‖`, `‖c1‖ ≤ ‖c0‖`, and `(‖c1‖ / ‖c0‖) ^ t1 ≤ ratio_t1 ≤ 0.15`,
any perturbation `‖Y' k - Y k‖ ≤ ε` (`0 ≤ ε`) is amplified across the full cyclic forward
bidiagonal solve by at most `2.36 * t_1`:
`‖solveBidiagonalFwd t1 c0 c1 Y' u1 - solveBidiagonalFwd t1 c0 c1 Y u1‖ ≤ 2.36 * t1 * ε`. -/
theorem solveBidiagonalFwd_cyclic_error_bound
    (t1 : ℕ) (ht1 : 0 < t1) (c0 c1 : ℂ) (Y Y' : ℕ → ℂ) (M ratio_t1 ε : ℝ)
    (hM : (0.49999999 : ℝ) ≤ M) (hc0 : M ≤ ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖)
    (hratio : (‖c1‖ / ‖c0‖) ^ t1 ≤ ratio_t1) (hratio_le : ratio_t1 ≤ (0.15 : ℝ))
    (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε) (u1 : ℕ) (hu1 : u1 < t1) :
    ‖solveBidiagonalFwd t1 c0 c1 Y' u1 - solveBidiagonalFwd t1 c0 c1 Y u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε := by
  have hM_pos : 0 < M := by linarith
  have hc0_pos : 0 < ‖c0‖ := lt_of_lt_of_le hM_pos hc0
  have hcond := theorem3_bidiagonal_conditioning M ratio_t1 hM hratio_le
  have h1m_pos : 0 ≤ 1 - ratio_t1 := by linarith
  have htail_eq : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ = ‖c0‖ * (‖c1‖ / ‖c0‖) ^ t1 := by
    unfold zHomFwd
    rw [norm_mul, norm_pow, norm_div, norm_neg]
    have ht1_eq : t1 = (t1 - 1) + 1 := by omega
    conv_rhs => rw [ht1_eq, pow_succ]
    field_simp [hc0_pos.ne']
  have htail_le : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ ≤ ‖c0‖ * ratio_t1 := by
    rw [htail_eq]
    exact mul_le_mul_of_nonneg_left hratio hc0_pos.le
  have hdenom_ge_c0 : ‖c0‖ * (1 - ratio_t1) ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ := by
    have htri : ‖c0‖ ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ + ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ := by
      have hsub : c0 = (c0 + c1 * zHomFwd c0 c1 (t1 - 1)) - c1 * zHomFwd c0 c1 (t1 - 1) := by ring
      conv_lhs => rw [hsub]
      exact norm_sub_le _ _
    linarith
  have hdenom_ge_M : M * (1 - ratio_t1) ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ :=
    (mul_le_mul_of_nonneg_right hc0 h1m_pos).trans hdenom_ge_c0
  have hdenom_pos : 0 < ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ := by linarith [hcond.1]
  have hdenom_ne : c0 + c1 * zHomFwd c0 c1 (t1 - 1) ≠ 0 := norm_pos_iff.mp hdenom_pos
  rw [solveBidiagonalFwd_sub]
  have hprod_le := norm_denom_mul_solveBidiagonalFwd_le t1 c0 c1 hc0_pos hc10 hdenom_ne
    (fun k => Y' k - Y k) ε hε hY u1 hu1
  rw [norm_mul] at hprod_le
  have hdiv_le : ‖solveBidiagonalFwd t1 c0 c1 (fun k => Y' k - Y k) u1‖ ≤
      ((t1 : ℝ) * ε) / (M * (1 - ratio_t1)) := by
    have h1 : ‖solveBidiagonalFwd t1 c0 c1 (fun k => Y' k - Y k) u1‖ ≤
        ((t1 : ℝ) * ε) / ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ :=
      (le_div_iff₀' hdenom_pos).mpr hprod_le
    refine h1.trans (div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg t1) hε) ?_ hdenom_ge_M)
    linarith [hcond.1]
  have hrew : ((t1 : ℝ) * ε) / (M * (1 - ratio_t1)) =
      (1 / (M * (1 - ratio_t1))) * ((t1 : ℝ) * ε) := by ring
  rw [hrew] at hdiv_le
  calc ‖solveBidiagonalFwd t1 c0 c1 (fun k => Y' k - Y k) u1‖
      ≤ (1 / (M * (1 - ratio_t1))) * ((t1 : ℝ) * ε) := hdiv_le
    _ ≤ (2.36 : ℝ) * ((t1 : ℝ) * ε) :=
        mul_le_mul_of_nonneg_right hcond.2.le (mul_nonneg (Nat.cast_nonneg t1) hε)
    _ = (2.36 : ℝ) * (t1 : ℝ) * ε := by ring

/-- **Reversed Right-Hand Side Indexing (`bwdRevRHS`, `[MS]` §5.1, Theorem 5.1(2), eq. (23) & §5.2 — Note on `k = 0` Boundary Indexing)**:
Maps the backward bidiagonal sweep to a forward sweep with `(c0, c1)` swapped to `(c1, c0)`:
`bwdRevRHS t1 Y k = if k = 0 then Y 0 else Y (t1 - k)`.

*Note on Backward Index Reversal*: In an earlier `[MS]` draft (corrected in `[MS]` §5.1, eq. (23) and §5.2), the backward-to-forward index reversal
was written informally as `Y'(d) = Y(t_1 - 1 - d)`. In fact:
1. For the interior particular sweep steps `d + 1` (`0 ≤ d < t_1 - 1`, i.e., `k = d + 1 ≥ 1`),
   the backward equation `c_0 Z(u_1 + 1) + c_1 Z(u_1) = Y(u_1 + 1)` at `u_1 = t_1 - 1 - (d + 1)`
   uses right-hand side `Y((t_1 - 1 - d - 1) + 1) = Y(t_1 - 1 - d) = Y(t_1 - (d + 1)) = bwdRevRHS t1 Y (d + 1)`.
2. At the cyclic wrap-around boundary `k = 0`, the cyclic equation closing `Z(t_1 - 1)` and `Z(0)`
   is `c_0 Z(0) + c_1 Z(t_1 - 1) = Y(0)` (NOT `Y(t_1 - 1)`!).
Thus the exact reversed right-hand side is `bwdRevRHS t1 Y k = if k = 0 then Y 0 else Y (t1 - k)`,
as proved in `zPartBwd_eq_zPartFwd_rev` and `solveBidiagonalBwd_eq_solveBidiagonalFwd_rev`. -/
def bwdRevRHS (t1 : ℕ) (Y : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 0 then Y 0 else Y (t1 - k)

/-- The backward particular sweep `zPartBwd t1 c0 c1 Y d` equals the forward particular sweep
`zPartFwd c1 c0 (bwdRevRHS t1 Y) d`. -/
theorem zPartBwd_eq_zPartFwd_rev (t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (d : ℕ) :
    zPartBwd t1 c0 c1 Y d = zPartFwd c1 c0 (bwdRevRHS t1 Y) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [zPartBwd_succ, zPartFwd_succ, ih]
    unfold bwdRevRHS
    rw [if_neg (Nat.succ_ne_zero d)]
    have hsub : t1 - 1 - d = t1 - (d + 1) := by omega
    rw [hsub]

/-- The backward cyclic bidiagonal solver `solveBidiagonalBwd t1 c0 c1 Y u1` equals the forward
cyclic bidiagonal solver `solveBidiagonalFwd t1 c1 c0 (bwdRevRHS t1 Y) (t1 - 1 - u1)`. -/
theorem solveBidiagonalBwd_eq_solveBidiagonalFwd_rev
    (t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) :
    solveBidiagonalBwd t1 c0 c1 Y u1 =
      solveBidiagonalFwd t1 c1 c0 (bwdRevRHS t1 Y) (t1 - 1 - u1) := by
  unfold solveBidiagonalBwd solveBidiagonalFwd zHomBwd zHomFwd
  dsimp only
  rw [zPartBwd_eq_zPartFwd_rev t1 c0 c1 Y (t1 - 1 - u1),
      zPartBwd_eq_zPartFwd_rev t1 c0 c1 Y (t1 - 1)]
  rfl

/-- **Finite-Horizon Open-Loop Perturbation Bound for `zPartBwd` (`‖c0‖ ≤ ‖c1‖`)**:
Without assuming a strict geometric contraction `ρ < 1`, if `0 < M ≤ ‖c1‖` and `‖c0‖ ≤ ‖c1‖`,
then `‖zPartBwd t1 c0 c1 Y' d - zPartBwd t1 c0 c1 Y d‖ ≤ d * (ε / M)`. -/
theorem zPartBwd_norm_sub_le_linear
    (t1 : ℕ) (c0 c1 : ℂ) (Y Y' : ℕ → ℂ) (M ε : ℝ) (d : ℕ)
    (hM_pos : 0 < M) (hM : M ≤ ‖c1‖) (hc01 : ‖c0‖ ≤ ‖c1‖) (hε : 0 ≤ ε)
    (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε) :
    ‖zPartBwd t1 c0 c1 Y' d - zPartBwd t1 c0 c1 Y d‖ ≤ (d : ℝ) * (ε / M) := by
  rw [zPartBwd_eq_zPartFwd_rev, zPartBwd_eq_zPartFwd_rev]
  refine zPartFwd_norm_sub_le_linear c1 c0 (bwdRevRHS t1 Y) (bwdRevRHS t1 Y') M ε d
    hM_pos hM hc01 hε fun k => ?_
  unfold bwdRevRHS
  split_ifs <;> exact hY _

/-- **`[MS]` Theorem 5.1 (Full Cyclic Perturbation Bound `< 2.36 * t_1 * ε` for `solveBidiagonalBwd`, `[MS]` §5.1, eq. (24))**:
For `t1 > 0`, `0.49999999 ≤ M ≤ ‖c1‖`, `‖c0‖ ≤ ‖c1‖`, and `(‖c0‖ / ‖c1‖) ^ t1 ≤ ratio_t1 ≤ 0.15`,
any perturbation `‖Y' k - Y k‖ ≤ ε` (`0 ≤ ε`) is amplified across the full cyclic backward
bidiagonal solve by at most `2.36 * t_1`:
`‖solveBidiagonalBwd t1 c0 c1 Y' u1 - solveBidiagonalBwd t1 c0 c1 Y u1‖ ≤ 2.36 * t1 * ε`. -/
theorem solveBidiagonalBwd_cyclic_error_bound
    (t1 : ℕ) (ht1 : 0 < t1) (c0 c1 : ℂ) (Y Y' : ℕ → ℂ) (M ratio_t1 ε : ℝ)
    (hM : (0.49999999 : ℝ) ≤ M) (hc1 : M ≤ ‖c1‖) (hc01 : ‖c0‖ ≤ ‖c1‖)
    (hratio : (‖c0‖ / ‖c1‖) ^ t1 ≤ ratio_t1) (hratio_le : ratio_t1 ≤ (0.15 : ℝ))
    (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε) (u1 : ℕ) (hu1 : u1 < t1) :
    ‖solveBidiagonalBwd t1 c0 c1 Y' u1 - solveBidiagonalBwd t1 c0 c1 Y u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε := by
  have _ := hu1
  rw [solveBidiagonalBwd_eq_solveBidiagonalFwd_rev, solveBidiagonalBwd_eq_solveBidiagonalFwd_rev]
  refine solveBidiagonalFwd_cyclic_error_bound t1 ht1 c1 c0 (bwdRevRHS t1 Y) (bwdRevRHS t1 Y')
    M ratio_t1 ε hM hc1 hc01 hratio hratio_le hε (fun k => ?_) (t1 - 1 - u1) (by omega)
  unfold bwdRevRHS
  split_ifs <;> exact hY _

/-- **Unconditional Forward Cyclic Perturbation Bound `< 2.36 * t_1 * ε` for Balanced Splits (`2 * u_2 < r ≤ 2 * t_1`, `[MS]` §5.1, eq. (24))**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, `r ≤ 2 * t1`, and `2 * u2 < r`, the concrete passband
coefficients `c0 = c0Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r)` and
`c1 = c1Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r)` automatically satisfy
`0.49999999 ≤ ‖c0‖`, `‖c1‖ ≤ ‖c0‖`, and `(‖c1‖ / ‖c0‖) ^ t1 ≤ 0.15`, yielding the hypothesis-free
cyclic perturbation bound `≤ 2.36 * t1 * ε`. -/
theorem solveBidiagonalFwd_cyclic_error_bound_of_balanced
    (p_work t1 r u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hr_le : r ≤ 2 * t1) (hu2 : 2 * u2 < r)
    (Y Y' : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε)
    (u1 : ℕ) (hu1 : u1 < t1) :
    let α := alphaSchedule p_work
    let y := (u2 : ℝ) / (r : ℝ)
    let c0 : ℂ := (c0Coeff (realErfScaled α) y : ℂ)
    let c1 : ℂ := (c1Coeff (realErfScaled α) y : ℂ)
    ‖solveBidiagonalFwd t1 c0 c1 Y' u1 - solveBidiagonalFwd t1 c0 c1 Y u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε := by
  dsimp only
  set α := alphaSchedule p_work
  set y := (u2 : ℝ) / (r : ℝ)
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy_half : y ≤ 1 / 2 := by
    dsimp [y]
    rw [div_le_iff₀ hr_pos]
    have hu2_real : 2 * (u2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hu2.le
    linarith
  have hc0_pos : 0 < c0Coeff (realErfScaled α) y := c0Coeff_realErfScaled_pos α y hα
  have hc1_pos : 0 < c1Coeff (realErfScaled α) y := c1Coeff_realErfScaled_pos α y hα
  have hnorm_c0 : ‖(c0Coeff (realErfScaled α) y : ℂ)‖ = c0Coeff (realErfScaled α) y := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc0_pos.le]
  have hnorm_c1 : ‖(c1Coeff (realErfScaled α) y : ℂ)‖ = c1Coeff (realErfScaled α) y := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc1_pos.le]
  refine solveBidiagonalFwd_cyclic_error_bound t1 ht1
    (c0Coeff (realErfScaled α) y : ℂ) (c1Coeff (realErfScaled α) y : ℂ)
    Y Y' (0.49999999 : ℝ) (0.15 : ℝ) ε le_rfl ?_ ?_ ?_ le_rfl hε hY u1 hu1
  · rw [hnorm_c0]
    exact (c0Coeff_alphaSchedule_gt_049999999 p_work (by omega) y hy0 hy_half).le
  · rw [hnorm_c1, hnorm_c0]
    exact c1Coeff_le_c0Coeff_of_le_half α y hα hy0 hy_half
  · rw [hnorm_c1, hnorm_c0]
    exact c1_div_c0_pow_le_015_of_balanced p_work t1 r u2 hp ht1 hr hr_le hu2

/-- **Unconditional Backward Cyclic Perturbation Bound `< 2.36 * t_1 * ε` for Balanced Splits (`r < 2 * u_2`, `u_2 < r ≤ 2 * t_1`, `[MS]` §5.1, eq. (24))**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, `r ≤ 2 * t1`, `r < 2 * u2`, and `u2 < r`, the concrete passband
coefficients `c0 = c0Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r)` and
`c1 = c1Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r)` automatically satisfy
`0.49999999 ≤ ‖c1‖`, `‖c0‖ ≤ ‖c1‖`, and `(‖c0‖ / ‖c1‖) ^ t1 ≤ 0.15`, yielding the hypothesis-free
cyclic perturbation bound `≤ 2.36 * t1 * ε`. -/
theorem solveBidiagonalBwd_cyclic_error_bound_of_balanced
    (p_work t1 r u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hr_le : r ≤ 2 * t1) (hu2_gt : r < 2 * u2) (hu2_lt : u2 < r)
    (Y Y' : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε)
    (u1 : ℕ) (hu1 : u1 < t1) :
    let α := alphaSchedule p_work
    let y := (u2 : ℝ) / (r : ℝ)
    let c0 : ℂ := (c0Coeff (realErfScaled α) y : ℂ)
    let c1 : ℂ := (c1Coeff (realErfScaled α) y : ℂ)
    ‖solveBidiagonalBwd t1 c0 c1 Y' u1 - solveBidiagonalBwd t1 c0 c1 Y u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε := by
  dsimp only
  set α := alphaSchedule p_work
  set y := (u2 : ℝ) / (r : ℝ)
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy_half : 1 / 2 ≤ y := by
    dsimp [y]
    rw [le_div_iff₀ hr_pos]
    have hu2_real : (r : ℝ) ≤ 2 * (u2 : ℝ) := by exact_mod_cast hu2_gt.le
    linarith
  have hy1 : y ≤ 1 := by
    dsimp [y]
    exact (div_le_one hr_pos).mpr (by exact_mod_cast hu2_lt.le)
  have hc0_pos : 0 < c0Coeff (realErfScaled α) y := c0Coeff_realErfScaled_pos α y hα
  have hc1_pos : 0 < c1Coeff (realErfScaled α) y := c1Coeff_realErfScaled_pos α y hα
  have hnorm_c0 : ‖(c0Coeff (realErfScaled α) y : ℂ)‖ = c0Coeff (realErfScaled α) y := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc0_pos.le]
  have hnorm_c1 : ‖(c1Coeff (realErfScaled α) y : ℂ)‖ = c1Coeff (realErfScaled α) y := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc1_pos.le]
  refine solveBidiagonalBwd_cyclic_error_bound t1 ht1
    (c0Coeff (realErfScaled α) y : ℂ) (c1Coeff (realErfScaled α) y : ℂ)
    Y Y' (0.49999999 : ℝ) (0.15 : ℝ) ε le_rfl ?_ ?_ ?_ le_rfl hε hY u1 hu1
  · rw [hnorm_c1]
    exact (c1Coeff_alphaSchedule_gt_049999999 p_work (by omega) y hy_half hy1).le
  · rw [hnorm_c0, hnorm_c1]
    exact c0Coeff_le_c1Coeff_of_ge_half α y hα hy_half hy1
  · rw [hnorm_c0, hnorm_c1]
    exact c0_div_c1_pow_le_015_of_balanced p_work t1 r u2 hp ht1 hr hr_le hu2_gt hu2_lt

/-- The 2D spatial array `(j_1, k_2) ↦ Y_{j_1}(k_2)` formed by spreading `x(j_1 + t_1 j_2)` against
the `r`-periodically lattice-folded `sincGaussian` kernel (`[MS]` §4.2, eqs. (17)–(18)). -/
noncomputable def sincGaussianSpreadArray (α : ℝ) (t1 r : ℕ) (x : ℕ → ℂ) (j1 k2 : ℕ) : ℂ :=
  ∑ j2 ∈ Finset.range r,
    x (j1 + t1 * j2) *
      ∑' l : ℤ,
        (sincGaussian α
          ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ))) : ℂ)

/-- Helper: for `u1 < t1`, `(((u1 : ℤ) - 0).emod (t1 : ℤ)).toNat = u1`. -/
theorem emod_sub_zero_toNat (t1 u1 : ℕ) (hu1 : u1 < t1) :
    ((((u1 : ℤ) - 0).emod (t1 : ℤ)).toNat) = u1 := by
  change (((u1 : ℤ) - 0) % (t1 : ℤ)).toNat = u1
  rw [sub_zero, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

/-- Helper: for `0 < t1`, `((((0 : ℕ) : ℤ) - 1).emod (t1 : ℤ)).toNat = t1 - 1`. -/
theorem emod_zero_sub_one_toNat (t1 : ℕ) (ht1 : 0 < t1) :
    (((((0 : ℕ) : ℤ) - 1).emod (t1 : ℤ)).toNat) = t1 - 1 := by
  change ((((0 : ℕ) : ℤ) - 1) % (t1 : ℤ)).toNat = t1 - 1
  have hrew : ((0 : ℕ) : ℤ) - 1 = ((t1 - 1 : ℕ) : ℤ) + (-1 : ℤ) * (t1 : ℤ) := by omega
  rw [hrew, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

/-- Helper: for `u1 + 1 < t1`, `(((((u1 + 1 : ℕ) : ℤ) - 1).emod (t1 : ℤ)).toNat) = u1`. -/
theorem emod_succ_sub_one_toNat (t1 u1 : ℕ) (hu1 : u1 + 1 < t1) :
    (((((u1 + 1 : ℕ) : ℤ) - 1).emod (t1 : ℤ)).toNat) = u1 := by
  change ((((u1 + 1 : ℕ) : ℤ) - 1) % (t1 : ℤ)).toNat = u1
  have hrew : ((u1 + 1 : ℕ) : ℤ) - 1 = (u1 : ℤ) := by omega
  rw [hrew, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

/-- **Composed `[MS]` Theorem 4.2 & Theorem 5.1 Forward Bidiagonal Deconvolution Bound (`2 * u_2 < r`, `[MS]` §5.1, eq. (24))**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, `2 * u2 < r`, wrap-around ratio
`(c_1(u_2 / r) / c_0(u_2 / r))^{t_1} ≤ 0.15`, and input sequence `‖x k‖ ≤ B_X` (`k < t1 * r`),
applying `solveBidiagonalFwd` to the 2D DFT of the lattice-folded `sincGaussianSpreadArray`
recovers the exact 1D DFT mode `dft1DGrid t1 r x u2 u1` (`u1 < t1`) up to error at most
`2.36 * t_1 * (0.15 * 2^{-p_work} * B_X)`. -/
theorem solveBidiagonalFwd_sincGaussian_dft2D_error_le
    (p_work t1 r u1 u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hu2_half : 2 * u2 < r)
    (hratio :
      (c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) /
        c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ))) ^ t1 ≤ (0.15 : ℝ))
    (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 ≤ B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (hu1 : u1 < t1) :
    ‖solveBidiagonalFwd t1
        (c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule p_work) t1 r x) k u2)
        u1 -
      dft1DGrid t1 r x u2 u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X) := by
  set α := alphaSchedule p_work
  set y := (u2 : ℝ) / (r : ℝ)
  set c0R := c0Coeff (realErfScaled α) y
  set c1R := c1Coeff (realErfScaled α) y
  set c0 : ℂ := (c0R : ℂ)
  set c1 : ℂ := (c1R : ℂ)
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  have hu2 : u2 < r := by omega
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hy_lt_half : y < 1 / 2 := by
    dsimp [y]
    rw [div_lt_iff₀ hr_pos]
    have h2u2 : 2 * (u2 : ℝ) < (r : ℝ) := by exact_mod_cast hu2_half
    linarith
  have hy_half : y ≤ 1 / 2 := hy_lt_half.le
  have hy1 : y ≤ 1 := by linarith
  have hne_half : y ≠ 1 / 2 := hy_lt_half.ne
  have hc0R_gt : (0.49999999 : ℝ) < c0R :=
    c0Coeff_alphaSchedule_gt_049999999 p_work hp y hy0 hy_half
  have hc0R_pos : 0 < c0R := c0Coeff_realErfScaled_pos α y hα
  have hc1R_pos : 0 < c1R := c1Coeff_realErfScaled_pos α y hα
  have hc10R : c1R ≤ c0R := c1Coeff_le_c0Coeff_of_le_half α y hα hy0 hy_half
  have hnorm_c0 : ‖c0‖ = c0R := by
    dsimp [c0]
    rw [Complex.norm_real, Real.norm_of_nonneg hc0R_pos.le]
  have hnorm_c1 : ‖c1‖ = c1R := by
    dsimp [c1]
    rw [Complex.norm_real, Real.norm_of_nonneg hc1R_pos.le]
  have hc0_ne : c0 ≠ 0 := Complex.ofReal_ne_zero.mpr hc0R_pos.ne'
  have hdenom : c0 + c1 * zHomFwd c0 c1 (t1 - 1) ≠ 0 :=
    c0_c1_realErfScaled_denom_ne_zero α y t1 hα ht1 hy0 hy1 hne_half
  let X : ℕ → ℂ := fun v => dft1DGrid t1 r x u2 v
  let Y_ideal : ℕ → ℂ := fun k =>
    c0 * X ((((k : ℤ) - 0).emod (t1 : ℤ)).toNat) +
    c1 * X ((((k : ℤ) - 1).emod (t1 : ℤ)).toNat)
  let Y_spread : ℕ → ℂ := fun k =>
    dft2D t1 r (sincGaussianSpreadArray α t1 r x) k u2
  have h_bnd : Y_ideal 0 = c0 * X 0 + c1 * X (t1 - 1) := by
    dsimp only [Y_ideal]
    rw [emod_sub_zero_toNat t1 0 ht1, emod_zero_sub_one_toNat t1 ht1]
  have h_int : ∀ v : ℕ, v + 1 < t1 → Y_ideal (v + 1) = c0 * X (v + 1) + c1 * X v := by
    intro v hv
    dsimp only [Y_ideal]
    rw [emod_sub_zero_toNat t1 (v + 1) hv, emod_succ_sub_one_toNat t1 v hv]
  have hrec := solveBidiagonalFwd_recover_exact t1 c0 c1 ht1 hc0_ne hdenom X Y_ideal h_bnd h_int u1 hu1
  change ‖solveBidiagonalFwd t1 c0 c1 Y_spread u1 - X u1‖ ≤
    (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X)
  rw [← hrec]
  refine solveBidiagonalFwd_cyclic_error_bound t1 ht1 c0 c1 Y_ideal Y_spread
    c0R ((c1R / c0R) ^ t1) ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X)
    hc0R_gt.le (by rw [hnorm_c0]) (by rw [hnorm_c1, hnorm_c0]; exact hc10R)
    (by rw [hnorm_c1, hnorm_c0]) hratio
    (mul_nonneg (mul_nonneg (by norm_num) (zpow_nonneg (by norm_num) _)) hB)
    (fun k => theorem2_sincGaussian_dft2D_sub_passband_norm_le p_work t1 r (by omega) ht1 hr k u2 hu2 x B_X hB hx)
    u1 hu1

/-- **Composed `[MS]` Theorem 4.2 & Theorem 5.1 Backward Bidiagonal Deconvolution Bound (`r < 2 * u_2` and `u_2 < r`, `[MS]` §5.1, eq. (24))**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, `r < 2 * u2`, `u2 < r`, wrap-around ratio
`(c_0(u_2 / r) / c_1(u_2 / r))^{t_1} ≤ 0.15`, and input sequence `‖x k‖ ≤ B_X` (`k < t1 * r`),
applying `solveBidiagonalBwd` to the 2D DFT of the lattice-folded `sincGaussianSpreadArray`
recovers the exact 1D DFT mode `dft1DGrid t1 r x u2 u1` (`u1 < t1`) up to error at most
`2.36 * t_1 * (0.15 * 2^{-p_work} * B_X)`. -/
theorem solveBidiagonalBwd_sincGaussian_dft2D_error_le
    (p_work t1 r u1 u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hu2_half : r < 2 * u2) (hu2 : u2 < r)
    (hratio :
      (c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) /
        c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ))) ^ t1 ≤ (0.15 : ℝ))
    (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 ≤ B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (hu1 : u1 < t1) :
    ‖solveBidiagonalBwd t1
        (c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule p_work) t1 r x) k u2)
        u1 -
      dft1DGrid t1 r x u2 u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X) := by
  set α := alphaSchedule p_work
  set y := (u2 : ℝ) / (r : ℝ)
  set c0R := c0Coeff (realErfScaled α) y
  set c1R := c1Coeff (realErfScaled α) y
  set c0 : ℂ := (c0R : ℂ)
  set c1 : ℂ := (c1R : ℂ)
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hy_gt_half : 1 / 2 < y := by
    dsimp [y]
    rw [lt_div_iff₀ hr_pos]
    have h2u2 : (r : ℝ) < 2 * (u2 : ℝ) := by exact_mod_cast hu2_half
    linarith
  have hy_half : 1 / 2 ≤ y := hy_gt_half.le
  have hy1 : y ≤ 1 := (div_le_one hr_pos).mpr (by exact_mod_cast hu2.le)
  have hne_half : y ≠ 1 / 2 := hy_gt_half.ne'
  have hc1R_gt : (0.49999999 : ℝ) < c1R :=
    c1Coeff_alphaSchedule_gt_049999999 p_work hp y hy_half hy1
  have hc0R_pos : 0 < c0R := c0Coeff_realErfScaled_pos α y hα
  have hc1R_pos : 0 < c1R := c1Coeff_realErfScaled_pos α y hα
  have hc01R : c0R ≤ c1R := c0Coeff_le_c1Coeff_of_ge_half α y hα hy_half hy1
  have hnorm_c0 : ‖c0‖ = c0R := by
    dsimp [c0]
    rw [Complex.norm_real, Real.norm_of_nonneg hc0R_pos.le]
  have hnorm_c1 : ‖c1‖ = c1R := by
    dsimp [c1]
    rw [Complex.norm_real, Real.norm_of_nonneg hc1R_pos.le]
  have hc1_ne : c1 ≠ 0 := Complex.ofReal_ne_zero.mpr hc1R_pos.ne'
  have hdenom : c1 + c0 * zHomBwd c0 c1 (t1 - 1) ≠ 0 :=
    c0_c1_realErfScaled_bwd_denom_ne_zero α y t1 hα ht1 hy0 hy1 hne_half
  let X : ℕ → ℂ := fun v => dft1DGrid t1 r x u2 v
  let Y_ideal : ℕ → ℂ := fun k =>
    c0 * X ((((k : ℤ) - 0).emod (t1 : ℤ)).toNat) +
    c1 * X ((((k : ℤ) - 1).emod (t1 : ℤ)).toNat)
  let Y_spread : ℕ → ℂ := fun k =>
    dft2D t1 r (sincGaussianSpreadArray α t1 r x) k u2
  have h_bnd : Y_ideal 0 = c0 * X 0 + c1 * X (t1 - 1) := by
    dsimp only [Y_ideal]
    rw [emod_sub_zero_toNat t1 0 ht1, emod_zero_sub_one_toNat t1 ht1]
  have h_int : ∀ v : ℕ, v + 1 < t1 → Y_ideal (v + 1) = c0 * X (v + 1) + c1 * X v := by
    intro v hv
    dsimp only [Y_ideal]
    rw [emod_sub_zero_toNat t1 (v + 1) hv, emod_succ_sub_one_toNat t1 v hv]
  have hrec := solveBidiagonalBwd_recover_exact t1 c0 c1 ht1 hc1_ne hdenom X Y_ideal h_bnd h_int u1 hu1
  change ‖solveBidiagonalBwd t1 c0 c1 Y_spread u1 - X u1‖ ≤
    (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X)
  rw [← hrec]
  refine solveBidiagonalBwd_cyclic_error_bound t1 ht1 c0 c1 Y_ideal Y_spread
    c1R ((c0R / c1R) ^ t1) ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X)
    hc1R_gt.le (by rw [hnorm_c1]) (by rw [hnorm_c0, hnorm_c1]; exact hc01R)
    (by rw [hnorm_c0, hnorm_c1]) hratio
    (mul_nonneg (mul_nonneg (by norm_num) (zpow_nonneg (by norm_num) _)) hB)
    (fun k => theorem2_sincGaussian_dft2D_sub_passband_norm_le p_work t1 r (by omega) ht1 hr k u2 hu2 x B_X hB hx)
    u1 hu1

/-- **Unconditional Composed Forward Bidiagonal Deconvolution Bound for Balanced Splits (`2 * u_2 < r ≤ 2 * t_1`, `[MS]` §5.1)**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, `r ≤ 2 * t1`, and `2 * u2 < r`, `c1_div_c0_pow_le_015_of_balanced`
discharges `hratio` automatically in `solveBidiagonalFwd_sincGaussian_dft2D_error_le`. -/
theorem solveBidiagonalFwd_sincGaussian_dft2D_error_le_of_balanced
    (p_work t1 r u1 u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hr_le : r ≤ 2 * t1) (hu2_half : 2 * u2 < r)
    (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 ≤ B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (hu1 : u1 < t1) :
    ‖solveBidiagonalFwd t1
        (c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule p_work) t1 r x) k u2)
        u1 -
      dft1DGrid t1 r x u2 u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X) :=
  solveBidiagonalFwd_sincGaussian_dft2D_error_le p_work t1 r u1 u2 (by omega) ht1 hr hu2_half
    (c1_div_c0_pow_le_015_of_balanced p_work t1 r u2 hp ht1 hr hr_le hu2_half)
    x B_X hB hx hu1

/-- **Unconditional Composed Backward Bidiagonal Deconvolution Bound for Balanced Splits (`r < 2 * u_2`, `u_2 < r ≤ 2 * t_1`, `[MS]` §5.1)**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, `r ≤ 2 * t1`, `r < 2 * u2`, and `u2 < r`,
`c0_div_c1_pow_le_015_of_balanced` discharges `hratio` automatically in
`solveBidiagonalBwd_sincGaussian_dft2D_error_le`. -/
theorem solveBidiagonalBwd_sincGaussian_dft2D_error_le_of_balanced
    (p_work t1 r u1 u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hr_le : r ≤ 2 * t1) (hu2_half : r < 2 * u2) (hu2 : u2 < r)
    (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 ≤ B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (hu1 : u1 < t1) :
    ‖solveBidiagonalBwd t1
        (c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (c1Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule p_work) t1 r x) k u2)
        u1 -
      dft1DGrid t1 r x u2 u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X) :=
  solveBidiagonalBwd_sincGaussian_dft2D_error_le p_work t1 r u1 u2 (by omega) ht1 hr hu2_half hu2
    (c0_div_c1_pow_le_015_of_balanced p_work t1 r u2 hp ht1 hr hr_le hu2_half hu2)
    x B_X hB hx hu1

/-! ## 3. `[MS]` Theorem 5.1(3) (§5.1): Exact Nyquist Alternating-Sum Identity & Solver at `u_2 = r / 2` -/

/-- **`[MS]` Theorem 5.1 (Part 3a: Exact Nyquist Midpoint Phase Identity, `[MS]` §5.1, eq. (25))**:
At the midpoint row `j_1 = m` (where `t_1 = 2 m`, `m > 0`) and the Nyquist column `u_2 = k`
(where `r = 2 k`, `k > 0`), the 1D DFT character evaluates to:
`stdChar (((m + 2 m j_2) * k) / (4 m k)) = stdChar (1/4 + j_2 / 2) = i * (-1)^{j_2}`. -/
theorem theorem3_nyquist_midpoint_phase
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (j2 : ℕ) :
    stdChar ((((m + (2 * m) * j2 : ℕ) : ℝ) * (k : ℝ)) /
      (((2 * m) * (2 * k) : ℕ) : ℝ)) =
      Complex.I * (-1 : ℂ) ^ j2 := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have harg : ((((m + (2 * m) * j2 : ℕ) : ℝ) * (k : ℝ)) /
      (((2 * m) * (2 * k) : ℕ) : ℝ)) = (1 / 4 : ℝ) + (j2 : ℝ) / 2 := by
    push_cast
    field_simp [hm_ne, hk_ne]
    ring
  rw [harg, stdChar_add]
  have hquarter : stdChar (1 / 4 : ℝ) = Complex.I := by
    unfold stdChar
    have h1 : (((2 * Real.pi * (1 / 4 : ℝ) : ℝ) : ℂ) * Complex.I) =
        (Real.pi / 2 : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h1, Complex.exp_pi_div_two_mul_I]
  have hhalf : stdChar ((j2 : ℝ) / 2) = (-1 : ℂ) ^ j2 := by
    unfold stdChar
    have h2 : (((2 * Real.pi * ((j2 : ℝ) / 2) : ℝ) : ℂ) * Complex.I) =
        (j2 : ℕ) * (Real.pi * Complex.I) := by
      push_cast
      ring
    rw [h2, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [hquarter, hhalf]

/-- Particular solution recurrence at the Nyquist column `u_2 = r / 2` (where `c_0 = c_1`):
`Z_part(0) = 0`, `Z_part(u_1 + 1) = Y(u_1 + 1) / c_0 - Z_part(u_1)`. -/
noncomputable def zPartNyq (c0 : ℂ) (Y : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | u1 + 1 => Y (u1 + 1) / c0 - zPartNyq c0 Y u1

@[simp]
theorem zPartNyq_succ (c0 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) :
    zPartNyq c0 Y (u1 + 1) = Y (u1 + 1) / c0 - zPartNyq c0 Y u1 :=
  rfl

/-- Full Nyquist column solver (`[MS]`, Section 5.1, Theorem 5.1(3) & Section 5.2):
`Z(u_1) = Z_part(u_1) + (-1)^{u_1} * ((alt_true - ∑_{v=0}^{t_1-1} (-1)^v Z_part(v)) / t_1)`. -/
noncomputable def solveNyquist (t1 : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (alt_true : ℂ) (u1 : ℕ) : ℂ :=
  let alt_part := ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y v
  let diff := (alt_true - alt_part) / (t1 : ℂ)
  zPartNyq c0 Y u1 + (-1 : ℂ) ^ u1 * diff

/-- **`[MS]` Theorem 5.1 (Part 3b: Exact Satisfaction of Nyquist Bidiagonal Equations & Alternating Sum)**:
For `t_1 > 0` and `c_0 ≠ 0`, `solveNyquist` satisfies:
1. `c_0 Z(u_1 + 1) + c_0 Z(u_1) = Y(u_1 + 1)` for all `u_1 ∈ ℕ`, and
2. `∑_{u_1=0}^{t_1-1} (-1)^{u_1} Z(u_1) = alt_true` identically. -/
theorem theorem3_nyquist_solver_exact
    (t1 : ℕ) (ht1 : 0 < t1) (c0 : ℂ) (hc0 : c0 ≠ 0) (Y : ℕ → ℂ) (alt_true : ℂ) :
    (∀ u1 : ℕ,
      c0 * solveNyquist t1 c0 Y alt_true (u1 + 1) +
        c0 * solveNyquist t1 c0 Y alt_true u1 = Y (u1 + 1)) ∧
    (∑ u1 ∈ Finset.range t1, (-1 : ℂ) ^ u1 * solveNyquist t1 c0 Y alt_true u1 = alt_true) := by
  constructor
  · intro u1
    unfold solveNyquist
    dsimp only
    rw [zPartNyq_succ, pow_succ]
    field_simp [hc0]
    ring
  · unfold solveNyquist
    dsimp only
    simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc]
    have hsq : ∀ u1 : ℕ, (-1 : ℂ) ^ u1 * (-1 : ℂ) ^ u1 = 1 := fun u1 => by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    simp_rw [hsq, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have ht1_ne : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
    field_simp [ht1_ne]
    ring

/-- Closed-form expression for `zPartNyq c0 Y u1` (`u1 < t1`) when
`Y (u1 + 1) = c0 * X (u1 + 1) + c0 * X u1` for all `u1 + 1 < t1`:
`zPartNyq c0 Y u1 = X u1 - X 0 * (-1)^u1`. -/
theorem zPartNyq_eq_sub_neg_one_pow
    (t1 : ℕ) (c0 : ℂ) (hc0 : c0 ≠ 0) (X Y : ℕ → ℂ)
    (h_int : ∀ u1 : ℕ, u1 + 1 < t1 → Y (u1 + 1) = c0 * X (u1 + 1) + c0 * X u1)
    (u1 : ℕ) (hu1 : u1 < t1) :
    zPartNyq c0 Y u1 = X u1 - X 0 * (-1 : ℂ) ^ u1 := by
  induction u1 with
  | zero =>
    simp [zPartNyq]
  | succ u1 ih =>
    rw [zPartNyq_succ, pow_succ, h_int u1 hu1, ih (Nat.lt_of_succ_lt hu1)]
    field_simp [hc0]
    ring

/-- **`[MS]` Theorem 5.1 (Part 3c: Exact Mode Recovery of `solveNyquist`)**:
If `Y : ℕ → ℂ` satisfies `Y (u1 + 1) = c0 * X (u1 + 1) + c0 * X u1` for all `u1 + 1 < t1` and
`alt_true = ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * X v` (`t1 > 0`, `c0 ≠ 0`), then
`solveNyquist t1 c0 Y alt_true u1 = X u1` for all `u1 < t1`. -/
theorem solveNyquist_recover_exact
    (t1 : ℕ) (ht1 : 0 < t1) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (X Y : ℕ → ℂ)
    (h_int : ∀ u1 : ℕ, u1 + 1 < t1 → Y (u1 + 1) = c0 * X (u1 + 1) + c0 * X u1)
    (alt_true : ℂ)
    (h_alt : alt_true = ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * X v)
    (u1 : ℕ) (hu1 : u1 < t1) :
    solveNyquist t1 c0 Y alt_true u1 = X u1 := by
  unfold solveNyquist
  dsimp only
  have hpart : (∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y v) =
      alt_true - (t1 : ℂ) * X 0 := by
    rw [h_alt]
    have hcongr : (∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y v) =
        ∑ v ∈ Finset.range t1, ((-1 : ℂ) ^ v * X v - X 0) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [zPartNyq_eq_sub_neg_one_pow t1 c0 hc0 X Y h_int v (Finset.mem_range.mp hv)]
      have hsq : (-1 : ℂ) ^ v * (-1 : ℂ) ^ v = 1 := by
        rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
      calc (-1 : ℂ) ^ v * (X v - X 0 * (-1 : ℂ) ^ v)
          = (-1 : ℂ) ^ v * X v - X 0 * ((-1 : ℂ) ^ v * (-1 : ℂ) ^ v) := by ring
        _ = (-1 : ℂ) ^ v * X v - X 0 := by rw [hsq, mul_one]
    rw [hcongr, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hpart, zPartNyq_eq_sub_neg_one_pow t1 c0 hc0 X Y h_int u1 hu1]
  have ht1_ne : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  field_simp [ht1_ne]
  ring

/-- Alternating-sign particular difference `(-1)^w * (zPartNyq c0 Y' w - zPartNyq c0 Y w)` at the
Nyquist column (`2 * u_2 = r`). -/
noncomputable def nyqSignedDiff (c0 : ℂ) (Y Y' : ℕ → ℂ) (w : ℕ) : ℂ :=
  (-1 : ℂ) ^ w * (zPartNyq c0 Y' w - zPartNyq c0 Y w)

/-- Single-step telescoping identity for `nyqSignedDiff`:
`nyqSignedDiff c0 Y Y' (w + 1) - nyqSignedDiff c0 Y Y' w = (-1)^(w + 1) * ((Y' (w + 1) - Y (w + 1)) / c0)`. -/
theorem nyqSignedDiff_succ (c0 : ℂ) (Y Y' : ℕ → ℂ) (w : ℕ) :
    nyqSignedDiff c0 Y Y' (w + 1) - nyqSignedDiff c0 Y Y' w =
      (-1 : ℂ) ^ (w + 1) * ((Y' (w + 1) - Y (w + 1)) / c0) := by
  unfold nyqSignedDiff
  rw [zPartNyq_succ, zPartNyq_succ, pow_succ (-1 : ℂ) w]
  ring

/-- Multi-step norm bound for `nyqSignedDiff`: over `k` steps starting at `d`,
`‖nyqSignedDiff c0 Y Y' (d + k) - nyqSignedDiff c0 Y Y' d‖ ≤ k * (ε / M)`. -/
theorem norm_nyqSignedDiff_add_sub_le
    (c0 : ℂ) (Y Y' : ℕ → ℂ) (M ε : ℝ) (d k : ℕ)
    (hM_pos : 0 < M) (hc0 : M ≤ ‖c0‖) (hε : 0 ≤ ε)
    (hY : ∀ j : ℕ, ‖Y' j - Y j‖ ≤ ε) :
    ‖nyqSignedDiff c0 Y Y' (d + k) - nyqSignedDiff c0 Y Y' d‖ ≤ (k : ℝ) * (ε / M) := by
  have hc0_pos : 0 < ‖c0‖ := lt_of_lt_of_le hM_pos hc0
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hsplit :
        nyqSignedDiff c0 Y Y' (d + (k + 1)) - nyqSignedDiff c0 Y Y' d =
          (nyqSignedDiff c0 Y Y' ((d + k) + 1) - nyqSignedDiff c0 Y Y' (d + k)) +
          (nyqSignedDiff c0 Y Y' (d + k) - nyqSignedDiff c0 Y Y' d) := by
      rw [← Nat.add_assoc]
      ring
    rw [hsplit, nyqSignedDiff_succ]
    have htri := norm_add_le
      ((-1 : ℂ) ^ (d + k + 1) * ((Y' (d + k + 1) - Y (d + k + 1)) / c0))
      (nyqSignedDiff c0 Y Y' (d + k) - nyqSignedDiff c0 Y Y' d)
    have hstep :
        ‖(-1 : ℂ) ^ (d + k + 1) * ((Y' (d + k + 1) - Y (d + k + 1)) / c0)‖ ≤ ε / M := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div]
      calc ‖Y' (d + k + 1) - Y (d + k + 1)‖ / ‖c0‖
          ≤ ε / ‖c0‖ := div_le_div_of_nonneg_right (hY (d + k + 1)) hc0_pos.le
        _ ≤ ε / M := div_le_div_of_nonneg_left hε hM_pos hc0
    push_cast
    linarith

/-- Pairwise norm bound for `nyqSignedDiff` across any two indices `a, b < t1`:
`‖nyqSignedDiff c0 Y Y' a - nyqSignedDiff c0 Y Y' b‖ ≤ t1 * (ε / M)`. -/
theorem norm_nyqSignedDiff_sub_le_of_lt
    (t1 : ℕ) (c0 : ℂ) (Y Y' : ℕ → ℂ) (M ε : ℝ) (a b : ℕ)
    (ha : a < t1) (hb : b < t1)
    (hM_pos : 0 < M) (hc0 : M ≤ ‖c0‖) (hε : 0 ≤ ε)
    (hY : ∀ j : ℕ, ‖Y' j - Y j‖ ≤ ε) :
    ‖nyqSignedDiff c0 Y Y' a - nyqSignedDiff c0 Y Y' b‖ ≤ (t1 : ℝ) * (ε / M) := by
  have hεM : 0 ≤ ε / M := div_nonneg hε hM_pos.le
  rcases le_total a b with hab | hba
  · rw [norm_sub_rev]
    have hb_eq : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
    have hsub_le : ((b - a : ℕ) : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast (by omega : b - a ≤ t1)
    calc ‖nyqSignedDiff c0 Y Y' b - nyqSignedDiff c0 Y Y' a‖
        = ‖nyqSignedDiff c0 Y Y' (a + (b - a)) - nyqSignedDiff c0 Y Y' a‖ := by rw [← hb_eq]
      _ ≤ ((b - a : ℕ) : ℝ) * (ε / M) :=
          norm_nyqSignedDiff_add_sub_le c0 Y Y' M ε a (b - a) hM_pos hc0 hε hY
      _ ≤ (t1 : ℝ) * (ε / M) := mul_le_mul_of_nonneg_right hsub_le hεM
  · have ha_eq : a = b + (a - b) := (Nat.add_sub_of_le hba).symm
    have hsub_le : ((a - b : ℕ) : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast (by omega : a - b ≤ t1)
    calc ‖nyqSignedDiff c0 Y Y' a - nyqSignedDiff c0 Y Y' b‖
        = ‖nyqSignedDiff c0 Y Y' (b + (a - b)) - nyqSignedDiff c0 Y Y' b‖ := by rw [← ha_eq]
      _ ≤ ((a - b : ℕ) : ℝ) * (ε / M) :=
          norm_nyqSignedDiff_add_sub_le c0 Y Y' M ε b (a - b) hM_pos hc0 hε hY
      _ ≤ (t1 : ℝ) * (ε / M) := mul_le_mul_of_nonneg_right hsub_le hεM

/-- Exact algebraic representation of the perturbation `solveNyquist t1 c0 Y' alt' u1 - solveNyquist t1 c0 Y alt u1`
in terms of the pairwise signed differences `nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v`. -/
theorem solveNyquist_sub_eq
    (t1 : ℕ) (ht1 : 0 < t1) (c0 : ℂ) (Y Y' : ℕ → ℂ) (alt alt' : ℂ) (u1 : ℕ) :
    solveNyquist t1 c0 Y' alt' u1 - solveNyquist t1 c0 Y alt u1 =
      (-1 : ℂ) ^ u1 *
        ((alt' - alt) / (t1 : ℂ) +
          (1 / (t1 : ℂ)) * ∑ v ∈ Finset.range t1,
            (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)) := by
  unfold solveNyquist
  dsimp only
  have hsum : (∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)) =
      (t1 : ℂ) * nyqSignedDiff c0 Y Y' u1 -
        ((∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y' v) -
         (∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y v)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold nyqSignedDiff
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hsum]
  unfold nyqSignedDiff
  have hsq : (-1 : ℂ) ^ u1 * (-1 : ℂ) ^ u1 = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have ht1_ne : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ht1.ne'
  calc (zPartNyq c0 Y' u1 + (-1 : ℂ) ^ u1 * ((alt' - ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y' v) / (t1 : ℂ))) -
       (zPartNyq c0 Y u1 + (-1 : ℂ) ^ u1 * ((alt - ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y v) / (t1 : ℂ)))
      = ((-1 : ℂ) ^ u1 * (-1 : ℂ) ^ u1) * (zPartNyq c0 Y' u1 - zPartNyq c0 Y u1) +
        (-1 : ℂ) ^ u1 * ((alt' - ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y' v) / (t1 : ℂ) -
          (alt - ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y v) / (t1 : ℂ)) := by
        rw [hsq, one_mul]
        ring
    _ = (-1 : ℂ) ^ u1 *
          ((alt' - alt) / (t1 : ℂ) +
            1 / (t1 : ℂ) *
              ((t1 : ℂ) * ((-1 : ℂ) ^ u1 * (zPartNyq c0 Y' u1 - zPartNyq c0 Y u1)) -
                ((∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y' v) -
                 (∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 Y v)))) := by
        field_simp [ht1_ne]
        ring

/-- **`[MS]` Theorem 5.1 (Part 3d: Perturbation Bound for `solveNyquist`, `[MS]` §5.1)**:
For `t1 > 0`, `0.49999999 ≤ M ≤ ‖c0‖`, right-hand side perturbation `‖Y' k - Y k‖ ≤ ε` (`0 ≤ ε`),
and alternating-sum perturbation `‖alt' - alt‖ ≤ ε_alt`, every entry `u1 < t1` satisfies:
`‖solveNyquist t1 c0 Y' alt' u1 - solveNyquist t1 c0 Y alt u1‖ ≤ 2.36 * t1 * ε + ε_alt / t1`. -/
theorem solveNyquist_error_bound
    (t1 : ℕ) (ht1 : 0 < t1) (c0 : ℂ) (Y Y' : ℕ → ℂ) (alt alt' : ℂ)
    (M ε ε_alt : ℝ) (hM : (0.49999999 : ℝ) ≤ M) (hc0 : M ≤ ‖c0‖)
    (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε)
    (halt : ‖alt' - alt‖ ≤ ε_alt) (u1 : ℕ) (hu1 : u1 < t1) :
    ‖solveNyquist t1 c0 Y' alt' u1 - solveNyquist t1 c0 Y alt u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε + ε_alt / (t1 : ℝ) := by
  have hM_pos : 0 < M := by linarith
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr ht1
  rw [solveNyquist_sub_eq t1 ht1 c0 Y Y' alt alt' u1,
      norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have htri := norm_add_le ((alt' - alt) / (t1 : ℂ))
    ((1 / (t1 : ℂ)) * ∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v))
  have ht_alt : ‖(alt' - alt) / (t1 : ℂ)‖ ≤ ε_alt / (t1 : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right halt ht1_pos.le
  have hsum_norm :
      ‖∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)‖ ≤
        (t1 : ℝ) * ((t1 : ℝ) * (ε / M)) := by
    calc ‖∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)‖
        ≤ ∑ v ∈ Finset.range t1, ‖nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _v ∈ Finset.range t1, (t1 : ℝ) * (ε / M) :=
          Finset.sum_le_sum fun v hv =>
            norm_nyqSignedDiff_sub_le_of_lt t1 c0 Y Y' M ε u1 v hu1 (Finset.mem_range.mp hv)
              hM_pos hc0 hε hY
      _ = (t1 : ℝ) * ((t1 : ℝ) * (ε / M)) := by simp [Finset.sum_const, nsmul_eq_mul]
  have ht_sum :
      ‖(1 / (t1 : ℂ)) * ∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)‖ ≤
        (t1 : ℝ) * (ε / M) := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    calc (1 / (t1 : ℝ)) * ‖∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)‖
        ≤ (1 / (t1 : ℝ)) * ((t1 : ℝ) * ((t1 : ℝ) * (ε / M))) :=
          mul_le_mul_of_nonneg_left hsum_norm (div_nonneg zero_le_one ht1_pos.le)
      _ = (t1 : ℝ) * (ε / M) := by field_simp [ht1_pos.ne']
  have hM_inv : 1 / M ≤ (2.36 : ℝ) := by
    rw [div_le_iff₀ hM_pos]
    linarith
  have ht_sum' : (t1 : ℝ) * (ε / M) ≤ (2.36 : ℝ) * (t1 : ℝ) * ε := by
    have hrew : (t1 : ℝ) * (ε / M) = (1 / M) * ((t1 : ℝ) * ε) := by ring
    rw [hrew]
    calc (1 / M) * ((t1 : ℝ) * ε)
        ≤ (2.36 : ℝ) * ((t1 : ℝ) * ε) :=
          mul_le_mul_of_nonneg_right hM_inv (mul_nonneg ht1_pos.le hε)
      _ = (2.36 : ℝ) * (t1 : ℝ) * ε := by ring
  linarith

/-- Special case of `solveNyquist_error_bound` when `alt' = alt` (`ε_alt = 0`):
`‖solveNyquist t1 c0 Y' alt u1 - solveNyquist t1 c0 Y alt u1‖ ≤ 2.36 * t1 * ε`. -/
theorem solveNyquist_cyclic_error_bound
    (t1 : ℕ) (ht1 : 0 < t1) (c0 : ℂ) (Y Y' : ℕ → ℂ) (alt : ℂ)
    (M ε : ℝ) (hM : (0.49999999 : ℝ) ≤ M) (hc0 : M ≤ ‖c0‖)
    (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε) (u1 : ℕ) (hu1 : u1 < t1) :
    ‖solveNyquist t1 c0 Y' alt u1 - solveNyquist t1 c0 Y alt u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε := by
  have h := solveNyquist_error_bound t1 ht1 c0 Y Y' alt alt M ε 0 hM hc0 hε hY (by simp) u1 hu1
  simpa using h

/-- At the Nyquist column `2 * u2 = r` (`r > 0`), `(u2 : ℝ) / (r : ℝ) = 1 / 2` and therefore
`c1Coeff erfScaled ((u2 : ℝ) / (r : ℝ)) = c0Coeff erfScaled ((u2 : ℝ) / (r : ℝ))`. -/
theorem c0_eq_c1_at_nyquist (erfScaled : ℝ → ℝ) (u2 r : ℕ) (hr : 0 < r) (hu2_nyq : 2 * u2 = r) :
    c1Coeff erfScaled ((u2 : ℝ) / (r : ℝ)) = c0Coeff erfScaled ((u2 : ℝ) / (r : ℝ)) := by
  unfold c0Coeff c1Coeff
  congr 1
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have h2u2 : 2 * (u2 : ℝ) = (r : ℝ) := by exact_mod_cast hu2_nyq
  field_simp [hr_ne]
  linarith

/-- **Unconditional Composed `[MS]` Theorem 4.2 & Theorem 5.1 Nyquist Deconvolution Error Bound on `sincGaussianSpreadArray` (`2 * u_2 = r`, `[MS]` §5.1)**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, `2 * u2 = r`, and `‖x k‖ ≤ B_X` (`k < t1 * r`),
applying `solveNyquist` with exact alternating sum `alt_true` to the 2D DFT of the lattice-folded
`sincGaussianSpreadArray` recovers the exact 1D DFT mode `dft1DGrid t1 r x u2 u1` (`u1 < t1`)
up to error at most `2.36 * t_1 * (0.15 * 2^{-p_work} * B_X)`. -/
theorem solveNyquist_sincGaussian_dft2D_error_le
    (p_work t1 r u1 u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r)
    (hu2_nyq : 2 * u2 = r)
    (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 ≤ B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (alt_true : ℂ)
    (h_alt : alt_true = ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * dft1DGrid t1 r x u2 v)
    (hu1 : u1 < t1) :
    ‖solveNyquist t1
        (c0Coeff (realErfScaled (alphaSchedule p_work)) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule p_work) t1 r x) k u2)
        alt_true u1 -
      dft1DGrid t1 r x u2 u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X) := by
  set α := alphaSchedule p_work
  set y := (u2 : ℝ) / (r : ℝ)
  set c0R := c0Coeff (realErfScaled α) y
  set c1R := c1Coeff (realErfScaled α) y
  set c0 : ℂ := (c0R : ℂ)
  set c1 : ℂ := (c1R : ℂ)
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  have hu2 : u2 < r := by omega
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hy_half : y ≤ 1 / 2 := by
    dsimp [y]
    rw [div_le_iff₀ hr_pos]
    have h2u2 : 2 * (u2 : ℝ) = (r : ℝ) := by exact_mod_cast hu2_nyq
    linarith
  have hc0R_gt : (0.49999999 : ℝ) < c0R :=
    c0Coeff_alphaSchedule_gt_049999999 p_work hp y hy0 hy_half
  have hc0R_pos : 0 < c0R := c0Coeff_realErfScaled_pos α y hα
  have hnorm_c0 : ‖c0‖ = c0R := by
    dsimp [c0]
    rw [Complex.norm_real, Real.norm_of_nonneg hc0R_pos.le]
  have hc0_ne : c0 ≠ 0 := Complex.ofReal_ne_zero.mpr hc0R_pos.ne'
  have hc1_eq_c0 : c1 = c0 := by
    dsimp [c1, c0, c1R, c0R, y]
    rw [c0_eq_c1_at_nyquist (realErfScaled α) u2 r hr hu2_nyq]
  let X : ℕ → ℂ := fun v => dft1DGrid t1 r x u2 v
  let Y_ideal : ℕ → ℂ := fun k =>
    c0 * X ((((k : ℤ) - 0).emod (t1 : ℤ)).toNat) +
    c1 * X ((((k : ℤ) - 1).emod (t1 : ℤ)).toNat)
  let Y_spread : ℕ → ℂ := fun k =>
    dft2D t1 r (sincGaussianSpreadArray α t1 r x) k u2
  have h_int : ∀ v : ℕ, v + 1 < t1 → Y_ideal (v + 1) = c0 * X (v + 1) + c0 * X v := by
    intro v hv
    dsimp only [Y_ideal]
    rw [emod_sub_zero_toNat t1 (v + 1) hv, emod_succ_sub_one_toNat t1 v hv, hc1_eq_c0]
  have hrec := solveNyquist_recover_exact t1 ht1 c0 hc0_ne X Y_ideal h_int alt_true h_alt u1 hu1
  change ‖solveNyquist t1 c0 Y_spread alt_true u1 - X u1‖ ≤
    (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X)
  rw [← hrec]
  refine solveNyquist_cyclic_error_bound t1 ht1 c0 Y_ideal Y_spread alt_true
    c0R ((0.15 : ℝ) * (2 : ℝ) ^ (-(p_work : ℤ)) * B_X)
    hc0R_gt.le (by rw [hnorm_c0])
    (mul_nonneg (mul_nonneg (by norm_num) (zpow_nonneg (by norm_num) _)) hB)
    (fun k => theorem2_sincGaussian_dft2D_sub_passband_norm_le p_work t1 r (by omega) ht1 hr k u2 hu2 x B_X hB hx)
    u1 hu1

/-- **Unconditional Nyquist Perturbation Bound `< 2.36 * t_1 * ε` at `2 * u_2 = r` (`[MS]` §5.1)**:
For `8 ≤ p_work`, `0 < t1`, `0 < r`, and `2 * u2 = r`, `c0 = c0Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r)`
satisfies `0.49999999 < ‖c0‖`, so `solveNyquist` amplifies any perturbation `‖Y' k - Y k‖ ≤ ε` by at most `2.36 * t1`. -/
theorem solveNyquist_error_bound_alphaSchedule
    (p_work t1 r u2 : ℕ) (hp : 8 ≤ p_work) (ht1 : 0 < t1) (hr : 0 < r) (hnyq : 2 * u2 = r)
    (Y Y' : ℕ → ℂ) (alt_true : ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε)
    (u1 : ℕ) (hu1 : u1 < t1) :
    let α := alphaSchedule p_work
    let y := (u2 : ℝ) / (r : ℝ)
    let c0 : ℂ := (c0Coeff (realErfScaled α) y : ℂ)
    ‖solveNyquist t1 c0 Y' alt_true u1 - solveNyquist t1 c0 Y alt_true u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε := by
  dsimp only
  set α := alphaSchedule p_work
  set y := (u2 : ℝ) / (r : ℝ)
  have hα : 0 < α := alphaSchedule_pos p_work (by omega)
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy_half : y ≤ 1 / 2 := by
    dsimp [y]
    rw [div_le_iff₀ hr_pos]
    have hu2_real : 2 * (u2 : ℝ) = (r : ℝ) := by exact_mod_cast hnyq
    linarith
  have hc0_pos : 0 < c0Coeff (realErfScaled α) y := c0Coeff_realErfScaled_pos α y hα
  have hnorm_c0 : ‖(c0Coeff (realErfScaled α) y : ℂ)‖ = c0Coeff (realErfScaled α) y := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc0_pos.le]
  refine solveNyquist_cyclic_error_bound t1 ht1 (c0Coeff (realErfScaled α) y : ℂ) Y Y' alt_true
    (0.49999999 : ℝ) ε le_rfl ?_ hε hY u1 hu1
  rw [hnorm_c0]
  exact (c0Coeff_alphaSchedule_gt_049999999 p_work hp y hy0 hy_half).le

/-- For any `α > 0` and `y : ℝ`, the infinite sum of `gHatBox (realErfScaled α) (y - m)` over `m ∈ ℤ`
is at most `1`. -/
theorem tsum_gHatBox_realErfScaled_le_one (α y : ℝ) (hα : 0 < α) :
    (∑' m : ℤ, gHatBox (realErfScaled α) (y - (m : ℝ))) ≤ 1 :=
  (summable_gHatBox_realErfScaled α y hα).tsum_le_of_sum_le
    (sum_finset_gHatBox_realErfScaled_le_one α y hα)

/-- The `r`-periodic Fourier transform of the lattice-folded `sincGaussian` kernel has magnitude `≤ 1`
at every frequency `u2 : ℕ`. -/
theorem norm_sum_range_tsum_sincGaussian_le_one
    (r : ℕ) (hr : 0 < r) (α z : ℝ) (hα : 0 < α) (u2 : ℕ) :
    ‖∑ m2 ∈ Finset.range r,
      (∑' l : ℤ, (sincGaussian α ((m2 : ℝ) + (l : ℝ) * (r : ℝ) - z) : ℂ)) *
        stdChar (((m2 * u2 : ℕ) : ℝ) / (r : ℝ))‖ ≤ 1 := by
  rw [sum_range_tsum_sincGaussian_lattice_fold r hr α z hα u2,
      sincGaussian_modulated_poisson_summation α z ((u2 : ℝ) / (r : ℝ)) hα]
  set y := (u2 : ℝ) / (r : ℝ)
  have hnorm_eq : ∀ m : ℤ,
      ‖(gHatBox (realErfScaled α) (y - (m : ℝ)) : ℂ) * stdChar ((y - (m : ℝ)) * z)‖ =
        gHatBox (realErfScaled α) (y - (m : ℝ)) := by
    intro m
    rw [norm_mul, norm_stdChar, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (gHatBox_realErfScaled_pos α (y - (m : ℝ)) hα).le]
  have hsum_norm : Summable (fun m : ℤ =>
      ‖(gHatBox (realErfScaled α) (y - (m : ℝ)) : ℂ) * stdChar ((y - (m : ℝ)) * z)‖) := by
    simp_rw [hnorm_eq]
    exact summable_gHatBox_realErfScaled α y hα
  calc ‖∑' m : ℤ, (gHatBox (realErfScaled α) (y - (m : ℝ)) : ℂ) * stdChar ((y - (m : ℝ)) * z)‖
      ≤ ∑' m : ℤ, ‖(gHatBox (realErfScaled α) (y - (m : ℝ)) : ℂ) * stdChar ((y - (m : ℝ)) * z)‖ :=
        norm_tsum_le_tsum_norm hsum_norm
    _ = ∑' m : ℤ, gHatBox (realErfScaled α) (y - (m : ℝ)) := by
        congr 1 with m
        exact hnorm_eq m
    _ ≤ 1 := tsum_gHatBox_realErfScaled_le_one α y hα

/-- Discrete Fourier inversion on `Finset.range r` (`r > 0`) for any sequence `G : ℕ → ℂ` and `k2 < r`. -/
theorem finset_range_dft_inversion (r : ℕ) (hr : 0 < r) (G : ℕ → ℂ) (k2 : ℕ) (hk2 : k2 < r) :
    G k2 =
      (1 / (r : ℂ)) * ∑ u2 ∈ Finset.range r,
        (∑ m2 ∈ Finset.range r, G m2 * stdChar (((m2 * u2 : ℕ) : ℝ) / (r : ℝ))) *
          stdChar (-(((k2 : ℝ) * (u2 : ℝ)) / (r : ℝ))) := by
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hswap :
      (∑ u2 ∈ Finset.range r,
        (∑ m2 ∈ Finset.range r, G m2 * stdChar (((m2 * u2 : ℕ) : ℝ) / (r : ℝ))) *
          stdChar (-(((k2 : ℝ) * (u2 : ℝ)) / (r : ℝ)))) =
      ∑ m2 ∈ Finset.range r, G m2 *
        ∑ u2 ∈ Finset.range r,
          stdChar (-(((u2 : ℝ) * (k2 : ℝ)) / (r : ℝ))) *
            stdChar (((u2 * m2 : ℕ) : ℝ) / (r : ℝ)) := by
    trans (∑ u2 ∈ Finset.range r, ∑ m2 ∈ Finset.range r,
      G m2 * (stdChar (-(((u2 : ℝ) * (k2 : ℝ)) / (r : ℝ))) *
        stdChar (((u2 * m2 : ℕ) : ℝ) / (r : ℝ))))
    · refine Finset.sum_congr rfl fun u2 _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m2 _ => ?_
      have h1 : (k2 : ℝ) * (u2 : ℝ) = (u2 : ℝ) * (k2 : ℝ) := mul_comm _ _
      have h2 : m2 * u2 = u2 * m2 := Nat.mul_comm _ _
      rw [h1, h2]
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m2 _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  have horth :
      (∑ m2 ∈ Finset.range r, G m2 *
        ∑ u2 ∈ Finset.range r,
          stdChar (-(((u2 : ℝ) * (k2 : ℝ)) / (r : ℝ))) *
            stdChar (((u2 * m2 : ℕ) : ℝ) / (r : ℝ))) =
      ∑ m2 ∈ Finset.range r, if k2 = m2 then G m2 * (r : ℂ) else 0 := by
    refine Finset.sum_congr rfl fun m2 hm2 => ?_
    rw [stdChar_orthogonality_range r hr k2 m2 hk2 (Finset.mem_range.mp hm2)]
    split_ifs <;> ring
  rw [horth, Finset.sum_ite_eq (Finset.range r) k2, if_pos (Finset.mem_range.mpr hk2)]
  field_simp [hr_ne]

/-- Every `r`-periodically lattice-folded `sincGaussian` kernel value (`k2 < r`, `α > 0`) has magnitude
at most `1` (since it is the inverse DFT average of `r` Fourier modes each bounded in magnitude by
`∑'_{m ∈ ℤ} gHatBox(u_2 / r - m) ≤ 1`). -/
theorem norm_tsum_sincGaussian_lattice_fold_le_one
    (r : ℕ) (hr : 0 < r) (α z : ℝ) (hα : 0 < α) (k2 : ℕ) (hk2 : k2 < r) :
    ‖∑' l : ℤ, (sincGaussian α ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - z) : ℂ)‖ ≤ 1 := by
  let G : ℕ → ℂ := fun m2 => ∑' l : ℤ, (sincGaussian α ((m2 : ℝ) + (l : ℝ) * (r : ℝ) - z) : ℂ)
  change ‖G k2‖ ≤ 1
  rw [finset_range_dft_inversion r hr G k2 hk2, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hsum :
      ‖∑ u2 ∈ Finset.range r,
        (∑ m2 ∈ Finset.range r, G m2 * stdChar (((m2 * u2 : ℕ) : ℝ) / (r : ℝ))) *
          stdChar (-(((k2 : ℝ) * (u2 : ℝ)) / (r : ℝ)))‖ ≤ (r : ℝ) := by
    calc ‖∑ u2 ∈ Finset.range r,
          (∑ m2 ∈ Finset.range r, G m2 * stdChar (((m2 * u2 : ℕ) : ℝ) / (r : ℝ))) *
            stdChar (-(((k2 : ℝ) * (u2 : ℝ)) / (r : ℝ)))‖
        ≤ ∑ u2 ∈ Finset.range r,
            ‖(∑ m2 ∈ Finset.range r, G m2 * stdChar (((m2 * u2 : ℕ) : ℝ) / (r : ℝ))) *
              stdChar (-(((k2 : ℝ) * (u2 : ℝ)) / (r : ℝ)))‖ := norm_sum_le _ _
      _ = ∑ u2 ∈ Finset.range r,
            ‖∑ m2 ∈ Finset.range r, G m2 * stdChar (((m2 * u2 : ℕ) : ℝ) / (r : ℝ))‖ := by
          refine Finset.sum_congr rfl fun u2 _ => ?_
          rw [norm_mul, norm_stdChar, mul_one]
      _ ≤ ∑ _u2 ∈ Finset.range r, (1 : ℝ) :=
          Finset.sum_le_sum fun u2 _ => norm_sum_range_tsum_sincGaussian_le_one r hr α z hα u2
      _ = (r : ℝ) := by simp
  calc (1 / (r : ℝ)) *
        ‖∑ u2 ∈ Finset.range r,
          (∑ m2 ∈ Finset.range r, G m2 * stdChar (((m2 * u2 : ℕ) : ℝ) / (r : ℝ))) *
            stdChar (-(((k2 : ℝ) * (u2 : ℝ)) / (r : ℝ)))‖
      ≤ (1 / (r : ℝ)) * (r : ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := one_div_mul_cancel hr_pos.ne'

/-- **`ℓ_∞` Norm Bound for `sincGaussianSpreadArray` (`[MS]` §4.2 & §5.1)**:
For `α > 0`, `r > 0`, and any input `x : ℕ → ℂ` with `‖x k‖ ≤ M` for all `k < t1 * r`,
every entry `sincGaussianSpreadArray α t1 r x j1 k2` (`j1 < t1`, `k2 < r`) has norm at most `(r : ℝ) * M`. -/
theorem norm_sincGaussianSpreadArray_le
    (α : ℝ) (hα : 0 < α) (t1 r : ℕ) (hr : 0 < r) (x : ℕ → ℂ) (M : ℝ)
    (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r) :
    ‖sincGaussianSpreadArray α t1 r x j1 k2‖ ≤ (r : ℝ) * M := by
  unfold sincGaussianSpreadArray
  calc ‖∑ j2 ∈ Finset.range r,
        x (j1 + t1 * j2) *
          ∑' l : ℤ,
            (sincGaussian α
              ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ))) : ℂ)‖
      ≤ ∑ j2 ∈ Finset.range r,
          ‖x (j1 + t1 * j2) *
            ∑' l : ℤ,
              (sincGaussian α
                ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ))) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j2 ∈ Finset.range r, M := by
        refine Finset.sum_le_sum fun j2 hj2 => ?_
        have hj2_lt : j2 < r := Finset.mem_range.mp hj2
        have hidx : j1 + t1 * j2 < t1 * r := by
          calc j1 + t1 * j2 < t1 + t1 * j2 := Nat.add_lt_add_right hj1 _
            _ = t1 * (j2 + 1) := by ring
            _ ≤ t1 * r := Nat.mul_le_mul_left t1 hj2_lt
        rw [norm_mul]
        calc ‖x (j1 + t1 * j2)‖ *
              ‖∑' l : ℤ,
                (sincGaussian α
                  ((k2 : ℝ) + (l : ℝ) * (r : ℝ) - ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ))) : ℂ)‖
            ≤ M * 1 := mul_le_mul (hx _ hidx)
              (norm_tsum_sincGaussian_lattice_fold_le_one r hr α
                ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) hα k2 hk2)
              (norm_nonneg _) ((norm_nonneg _).trans (hx _ hidx))
          _ = M := mul_one M
    _ = (r : ℝ) * M := by simp [Finset.sum_const, nsmul_eq_mul]

/-! ## 4. `[MS]` Lemma 6.5 (§6.3): Purely Additive Precision Schedule & Four-Source Error Closure -/

/-- Working precision at depth `ℓ` (`[MS]` Lemma 6.5, §6.3, eq. (34)): `p_work = p + K + 6`. -/
def pWork (p K : ℕ) : ℕ := p + K + 6

/-- Child recursive precision at depth `ℓ + 1` (`[MS]` Lemma 6.5, §6.3, eq. (34)):
`p_child = p_work + K + 6 = p + 2 K + 12`. -/
def pChild (p K : ℕ) : ℕ := pWork p K + K + 6

/-- The precision schedule is purely additive with slope `γ = 1`: `p_child = p + 2 K + 12`. -/
theorem pChild_eq_additive (p K : ℕ) : pChild p K = p + 2 * K + 12 := by
  unfold pChild pWork
  omega

/-- Numerical verification of the four-source error constants (`[MS]`, Section 6.3, Lemma 6.5):
1. Term (A) at `K ≥ 2`: `0.36 * 2^{-7} < 0.003`.
2. Terms (B)+(C)+(D) at `K ≥ 2`: `2.36 * 2^{-11} < 0.037`.
3. Total budget: `0.003 + 0.037 + 0.354 = 0.394 < 1`. -/
theorem lemma2_numerical_constants :
    (0.36 : ℝ) * (2 : ℝ) ^ (-7 : ℤ) < (0.003 : ℝ) ∧
    (2.36 : ℝ) * (2 : ℝ) ^ (-11 : ℤ) < (0.037 : ℝ) ∧
    (0.003 : ℝ) + (0.037 : ℝ) + (0.354 : ℝ) = (0.394 : ℝ) ∧
    (0.394 : ℝ) < (1 : ℝ) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **`[MS]` Lemma 6.5 (Part 2–3: Derivation of Terms (B)+(C)+(D) Bound `< 0.037 * 2^{-p} * M`, `[MS]` §6.3, Lemma 6.5)**:
At recursion depth `ℓ` with `2 ≤ K`, `0 < M`, `t1 * W_eff ≤ 2 ^ K`, and
`(t1 : ℝ) * (log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) ≤ (15 / 2 : ℝ) * (2 : ℝ) ^ K`,
the combined error from:
- (B1) Spatial window truncation tail `< 0.4 * 2^{-p_child} * M` (`lemma2_sincGaussian_spatial_tail_bound`),
- (B2) Pre-folded filter tap quantization `(1 / 2) * W_eff * 2^{-p_child} * M`,
- (B3) Step 1–2 overlap-add & twist rounding + `[MS]` Lemma 3.5 Synthetic FFT rounding
  `(k1 * complexQuantizeMaxErr p_child + 4 * 2^{-p_child}) * M ≤ (0.18 * K + 4) * 2^{-p_child} * M`
  (`lemma1_synthetic_fft_rounding_bound`),
- (C) Child DFT error `((2 / π) * log α + 1.62) * 2^{-p_child} * M`, and
- (D) Step 3 internal recurrence rounding `1.38 * 2^{-p_child} * M`,
after amplification by the cyclic bidiagonal factor `2.36 * t1`
(`solveBidiagonalFwd_cyclic_error_bound` / `solveBidiagonalBwd_cyclic_error_bound`), satisfies strictly:
`2.36 * t1 * ((1 / 2) * W_eff + log_alpha_term + 0.18 * K + 7) * 2^{-pChild p K} * M < 0.037 * 2^{-p} * M`. -/
theorem lemma2_termBCD_error_bound
    (p K t1 W_eff : ℕ) (log_alpha_term M : ℝ)
    (hK : 2 ≤ K) (hM : 0 < M)
    (hW : t1 * W_eff ≤ 2 ^ K)
    (h_sub : (t1 : ℝ) * (log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) ≤ (15 / 2 : ℝ) * (2 : ℝ) ^ K) :
    (2.36 : ℝ) * (t1 : ℝ) *
      ((1 / 2 : ℝ) * (W_eff : ℝ) + log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) *
      (2 : ℝ) ^ (-(pChild p K : ℤ)) * M <
      (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hW_real : (t1 : ℝ) * (W_eff : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast hW
  have h_bracket :
      (t1 : ℝ) * ((1 / 2 : ℝ) * (W_eff : ℝ) + log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) ≤
        8 * (2 : ℝ) ^ K := by
    have h_expand :
        (t1 : ℝ) * ((1 / 2 : ℝ) * (W_eff : ℝ) + log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) =
          (1 / 2 : ℝ) * ((t1 : ℝ) * (W_eff : ℝ)) +
            (t1 : ℝ) * (log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) := by ring
    linarith
  have hzpow_eq :
      8 * (2 : ℝ) ^ K * (2 : ℝ) ^ (-(pChild p K : ℤ)) =
        (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 9)) := by
    rw [pChild_eq_additive p K]
    have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℤ) := by norm_num
    rw [h8, ← zpow_natCast (2 : ℝ) K, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  have hzpow_le :
      (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 9)) ≤
        (2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 9))
        ≤ (2 : ℝ) ^ ((-11 : ℤ) + (-(p : ℤ))) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = (2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) :=
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (-11 : ℤ) (-(p : ℤ))
  have hchild_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild p K : ℤ)) := zpow_pos (by norm_num) _
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hnum := lemma2_numerical_constants.2.1
  have h1 :
      (2.36 : ℝ) * (t1 : ℝ) *
        ((1 / 2 : ℝ) * (W_eff : ℝ) + log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) *
        (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤
      (2.36 : ℝ) * ((2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ))) := by
    calc (2.36 : ℝ) * (t1 : ℝ) *
          ((1 / 2 : ℝ) * (W_eff : ℝ) + log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) *
          (2 : ℝ) ^ (-(pChild p K : ℤ))
        = (2.36 : ℝ) * (((t1 : ℝ) *
            ((1 / 2 : ℝ) * (W_eff : ℝ) + log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7)) *
            (2 : ℝ) ^ (-(pChild p K : ℤ))) := by ring
      _ ≤ (2.36 : ℝ) * (8 * (2 : ℝ) ^ K * (2 : ℝ) ^ (-(pChild p K : ℤ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right h_bracket hchild_pos.le
      _ = (2.36 : ℝ) * (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 9)) := by rw [hzpow_eq]
      _ ≤ (2.36 : ℝ) * ((2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ))) :=
          mul_le_mul_of_nonneg_left hzpow_le (by norm_num)
  have h2 :
      (2.36 : ℝ) * ((2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ))) <
        (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc (2.36 : ℝ) * ((2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)))
        = ((2.36 : ℝ) * (2 : ℝ) ^ (-11 : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) := by ring
      _ < (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) :=
          mul_lt_mul_of_pos_right hnum hpow_pos
  exact mul_lt_mul_of_pos_right (h1.trans_lt h2) hM

/-- **`[MS]` Lemma 6.5 (Part 3: Four-Source Inductive Error Closure at Depth `ℓ`, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
Given input norm bound `M = max(1, ‖x‖_∞) > 0`, if:
- (A) Stopband Poisson alias error is `≤ 0.003 * 2^{-p} * M`,
- (B+C+D) Spatial tail + Step 1–2 rounding + Child DFT + Step 3 recurrence rounding error is
  `≤ 0.037 * 2^{-p} * M`, and
- Final output quantization error at `p + 2` fractional bits is `≤ complexQuantizeMaxErr p * M`,
then the total output error `err_total` satisfies strictly:
`err_total < 0.394 * 2^{-p} * M < 2^{-p} * M`. -/
theorem lemma2_inductive_error_closure
    (p : ℕ) (M err_A err_BCD err_quant : ℝ) (hM : 0 < M)
    (hA : err_A ≤ (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M)
    (hBCD : err_BCD ≤ (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M)
    (hQ : err_quant ≤ complexQuantizeMaxErr p * M) :
    err_A + err_BCD + err_quant < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hQ_lt : complexQuantizeMaxErr p * M < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
    mul_lt_mul_of_pos_right (complexQuantizeMaxErr_lt p) hM
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M :=
    mul_pos (zpow_pos (by norm_num) _) hM
  have h1 : err_A + err_BCD + err_quant < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    linarith
  refine ⟨h1, ?_⟩
  linarith

/-- **`[MS]` Lemma 6.5 (Part 3b: End-to-End Inductive Error Closure Composing Individual Sub-Errors via
`lemma2_sincGaussian_spatial_tail_bound`, `lemma1_synthetic_fft_rounding_bound`, and
`lemma2_termBCD_error_bound` into `lemma2_inductive_error_closure`, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
At recursion depth `ℓ` with `2 ≤ K`, `0 < M`, `2 * k1 ≤ K`, `0 < α`, `δ ∈ [0, 1]`, `8 ≤ m1`,
window rules `pChild p K * log 2 ≤ π m1^2 / α^2` and `1 / 2 ≤ 2 π m1 / α^2`,
`t1 * W_eff ≤ 2 ^ K`, and `(t1 : ℝ) * (log_alpha_term + 0.18 * K + 7) ≤ (15 / 2) * 2 ^ K`,
composing:
- `err_B1` bounded by the two-sided spatial truncation tail
  `((∑' k, |sincGaussian α (m1 + 1 + k - δ)|) + (∑' k, |sincGaussian α (-(m1 + 1 + k) - δ)|)) * M`
  (discharged by `lemma2_sincGaussian_spatial_tail_bound` to `< 0.4 * 2^{-pChild p K} * M`),
- `err_B2` (filter tap quantization + overlap-add & twist rounding)
  `≤ ((1 / 2) * W_eff + 5.22) * 2^{-pChild p K} * M`,
- `err_B3` (Synthetic FFT butterfly rounding across `k1` stages)
  `≤ k1 * complexQuantizeMaxErr (pChild p K) * M`
  (discharged by `lemma1_synthetic_fft_rounding_bound` to `≤ 0.18 * K * 2^{-pChild p K} * M`),
- `err_C` (child recursive `FastDFT` error at precision `pChild p K`)
  `≤ log_alpha_term * 2^{-pChild p K} * M`, and
- `err_D` (Step 3 internal recurrence rounding) `≤ 1.38 * 2^{-pChild p K} * M`,
amplified by `2.36 * t1` (`err_BCD ≤ 2.36 * t1 * (err_B1 + err_B2 + err_B3 + err_C + err_D)`),
actively applies `lemma2_termBCD_error_bound` to discharge `hBCD : err_BCD < 0.037 * 2^{-p} * M`,
and then applies `lemma2_inductive_error_closure` to conclude
`err_A + err_BCD + err_quant < 0.394 * 2^{-p} * M < 2^{-p} * M`. -/
theorem lemma2_inductive_error_closure_from_components
    (p K t1 k1 m1 W_eff : ℕ)
    (α δ log_alpha_term M err_A err_B1 err_B2 err_B3 err_C err_D err_BCD err_quant : ℝ)
    (hK : 2 ≤ K) (hM : 0 < M) (hk1 : 2 * k1 ≤ K)
    (hα : 0 < α) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hm1 : 8 ≤ m1)
    (h_win : (pChild p K : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2)
    (h_step : (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2)
    (hW : t1 * W_eff ≤ 2 ^ K)
    (h_sub : (t1 : ℝ) * (log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) ≤ (15 / 2 : ℝ) * (2 : ℝ) ^ K)
    (hA : err_A ≤ (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M)
    (hB1 : err_B1 ≤
      ((∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) +
        (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|)) * M)
    (hB2 : err_B2 ≤ ((1 / 2 : ℝ) * (W_eff : ℝ) + (5.22 : ℝ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hB3 : err_B3 ≤ (k1 : ℝ) * complexQuantizeMaxErr (pChild p K) * M)
    (hC : err_C ≤ log_alpha_term * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hD : err_D ≤ (1.38 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hBCD_amp : err_BCD ≤ (2.36 : ℝ) * (t1 : ℝ) * (err_B1 + err_B2 + err_B3 + err_C + err_D))
    (hQ : err_quant ≤ complexQuantizeMaxErr p * M) :
    err_BCD < (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hB1_lt : err_B1 < (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    have htail := (lemma2_sincGaussian_spatial_tail_bound α δ m1 (pChild p K)
      hα hδ0 hδ1 hm1 h_win h_step).2
    exact hB1.trans_lt (mul_lt_mul_of_pos_right htail hM)
  have hB3_le : err_B3 ≤ (0.18 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    have hfft := mul_le_mul_of_nonneg_right
      (lemma1_synthetic_fft_rounding_bound K k1 (pChild p K) hk1) hM.le
    exact hB3.trans hfft
  have hsum_le :
      err_B1 + err_B2 + err_B3 + err_C + err_D ≤
        ((1 / 2 : ℝ) * (W_eff : ℝ) + log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) *
          (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    linarith
  have h236_t1_nonneg : (0 : ℝ) ≤ (2.36 : ℝ) * (t1 : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg t1)
  have hBCD_le :
      err_BCD ≤
        (2.36 : ℝ) * (t1 : ℝ) *
          ((1 / 2 : ℝ) * (W_eff : ℝ) + log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) *
          (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    have hmul := mul_le_mul_of_nonneg_left hsum_le h236_t1_nonneg
    linarith
  have hBCD_lt : err_BCD < (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
    hBCD_le.trans_lt (lemma2_termBCD_error_bound p K t1 W_eff log_alpha_term M hK hM hW h_sub)
  have hclosure := lemma2_inductive_error_closure p M err_A err_BCD err_quant hM hA hBCD_lt.le hQ
  exact ⟨hBCD_lt, hclosure.1, hclosure.2⟩

/-! ## 5. `[MS]` Lemma 6.1 (§6.1) & Lemma 6.5 (§6.3): Finite-Window Sinc-Gaussian Spread Array & Spatial Truncation Tail Closure (Term B1) -/

/-- Single tap term `x(j_1 + t_1 * ((k_2 - m) mod r)) * sincGaussian α (m - j_1 / t_1)` at offset `m : ℤ`. -/
noncomputable def sincGaussianSpreadTerm
    (α : ℝ) (t1 r : ℕ) (x : ℕ → ℂ) (j1 k2 : ℕ) (m : ℤ) : ℂ :=
  x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat) *
    (sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ)) : ℂ)

/-- **Finite-Window Sinc-Gaussian Spread Array (`windowedSincGaussianSpreadArray`, `[MS]` §4.2 & §6.1, Lemma 6.1)**:
Computes the 2D spatial array `(j_1, k_2) ↦ Y_{j_1}^{(W)}(k_2)` by summing only over the finite
window `m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ)` of `W = 2 * m_1 + 1` taps (with zero infinite `tsum`),
folding each tap `(k_2 - m) mod r` into `[0, r)`. -/
noncomputable def windowedSincGaussianSpreadArray
    (α : ℝ) (m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 k2 : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
    sincGaussianSpreadTerm α t1 r x j1 k2 m

/-- Helper: for `0 < r` and any `z : ℤ`, `(z % (r : ℤ)).toNat < r`. -/
theorem emod_toNat_lt_of_pos {r : ℕ} (hr : 0 < r) (z : ℤ) : (z % (r : ℤ)).toNat < r := by
  have hlt : z % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos z (by omega)
  have hnonneg : 0 ≤ z % (r : ℤ) := Int.emod_nonneg z (by omega)
  omega

/-- For any `α > 0` and shift `δ : ℝ`, `m ↦ |sincGaussian α ((m : ℝ) - δ)|` is summable over `ℤ`. -/
theorem summable_abs_sincGaussian_sub (α δ : ℝ) (hα : 0 < α) :
    Summable (fun m : ℤ => |sincGaussian α ((m : ℝ) - δ)|) := by
  have h := summable_norm_sincGaussian_modulated α δ 0 hα
  have h_eq :
      (fun k : ℤ => ‖(sincGaussian α (δ - (k : ℝ)) : ℂ) * stdChar (0 * (k : ℝ))‖) =
      (fun m : ℤ => |sincGaussian α ((m : ℝ) - δ)|) := by
    ext m
    rw [zero_mul, stdChar_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hneg : δ - (m : ℝ) = -((m : ℝ) - δ) := by ring
    rw [hneg, sincGaussian_even]
  rwa [h_eq] at h

/-- Unconditional summability of `sincGaussianSpreadTerm α t1 r x j1 k2` over `ℤ` for `α > 0` and `r > 0`. -/
theorem summable_sincGaussianSpreadTerm
    (α : ℝ) (hα : 0 < α) (t1 r : ℕ) (hr : 0 < r) (x : ℕ → ℂ) (j1 k2 : ℕ) :
    Summable (sincGaussianSpreadTerm α t1 r x j1 k2) := by
  set B : ℝ := ∑ i ∈ Finset.range r, ‖x (j1 + t1 * i)‖
  have h_maj : Summable (fun m : ℤ => B * |sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))|) :=
    (summable_abs_sincGaussian_sub α ((j1 : ℝ) / (t1 : ℝ)) hα).mul_left B
  have h_le : ∀ m : ℤ,
      ‖sincGaussianSpreadTerm α t1 r x j1 k2 m‖ ≤
        B * |sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))| := by
    intro m
    unfold sincGaussianSpreadTerm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hmem : (((k2 : ℤ) - m) % (r : ℤ)).toNat ∈ Finset.range r :=
      Finset.mem_range.mpr (emod_toNat_lt_of_pos hr ((k2 : ℤ) - m))
    exact Finset.single_le_sum (fun i _ => norm_nonneg (x (j1 + t1 * i))) hmem
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_le h_maj).of_norm

/-- **Exact Lattice Unfolding of `sincGaussianSpreadArray` into a Single `ℤ`-Series (`sincGaussianSpreadArray_eq_tsum_int`)**:
For `α > 0` and `r > 0`, the `r`-periodically folded `sincGaussianSpreadArray α t1 r x j1 k2`
equals the single `ℤ`-indexed series `∑' m : ℤ, sincGaussianSpreadTerm α t1 r x j1 k2 m`. -/
theorem sincGaussianSpreadArray_eq_tsum_int
    (α : ℝ) (hα : 0 < α) (t1 r : ℕ) (hr : 0 < r) (x : ℕ → ℂ) (j1 k2 : ℕ) :
    sincGaussianSpreadArray α t1 r x j1 k2 =
      ∑' m : ℤ, sincGaussianSpreadTerm α t1 r x j1 k2 m := by
  let F := sincGaussianSpreadTerm α t1 r x j1 k2
  have hF : Summable F := summable_sincGaussianSpreadTerm α hα t1 r hr x j1 k2
  let e1 : ℤ ≃ ℤ := Equiv.subLeft (k2 : ℤ)
  let G : ℤ → ℂ := fun k => F ((k2 : ℤ) - k)
  have hG_eq : G = F ∘ e1 := rfl
  have hG : Summable G := by
    rw [hG_eq]
    exact e1.summable_iff.mpr hF
  have htsum_e1 : (∑' k : ℤ, G k) = ∑' m : ℤ, F m := e1.tsum_eq F
  rw [← htsum_e1, ← sum_range_tsum_lattice_fold r hr G hG]
  unfold sincGaussianSpreadArray
  refine Finset.sum_congr rfl fun j2 hj2 => ?_
  have hj2_lt : j2 < r := Finset.mem_range.mp hj2
  rw [← tsum_mul_left, ← (Equiv.neg ℤ).tsum_eq (fun l : ℤ => G ((j2 : ℤ) + l * (r : ℤ)))]
  refine tsum_congr fun l => ?_
  dsimp only [G, F, sincGaussianSpreadTerm, Equiv.neg_apply]
  have h_sub : (k2 : ℤ) - ((k2 : ℤ) - ((j2 : ℤ) + (-l) * (r : ℤ))) = (j2 : ℤ) + (-l) * (r : ℤ) := by
    ring
  have h_mod : (((j2 : ℤ) + (-l) * (r : ℤ)) % (r : ℤ)).toNat = j2 := by
    rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have h_arg : (((k2 : ℤ) - ((j2 : ℤ) + (-l) * (r : ℤ)) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ) =
      (k2 : ℝ) + (l : ℝ) * (r : ℝ) - ((j2 : ℝ) + (j1 : ℝ) / (t1 : ℝ)) := by
    push_cast
    ring
  rw [Equiv.neg_apply, h_sub, h_mod, h_arg]

/-- Splitting a finite symmetric sum over `Finset.Icc (-(m1 : ℤ)) (m1 : ℤ)` into non-negative
indices `0 .. m1` and negative indices `-1 .. -m1`. -/
theorem sum_Icc_neg_eq_sum_range_add_sum_range {E : Type*} [AddCommMonoid E]
    (f : ℤ → E) (m1 : ℕ) :
    (∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), f m) =
      (∑ n ∈ Finset.range (m1 + 1), f (n : ℤ)) +
        (∑ n ∈ Finset.range m1, f (-((n : ℤ) + 1))) := by
  induction m1 with
  | zero =>
    simp
  | succ m1 ih =>
    have h_right :
        Finset.Icc (-((m1 + 1 : ℕ) : ℤ)) ((m1 + 1 : ℕ) : ℤ) =
          insert ((m1 + 1 : ℕ) : ℤ) (Finset.Icc (-((m1 + 1 : ℕ) : ℤ)) (m1 : ℤ)) := by
      have h1 : ((m1 + 1 : ℕ) : ℤ) = (m1 : ℤ) + 1 := by omega
      rw [h1, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega)]
    have h_left :
        Finset.Icc (-((m1 + 1 : ℕ) : ℤ)) (m1 : ℤ) =
          insert (-((m1 + 1 : ℕ) : ℤ)) (Finset.Icc (-(m1 : ℤ)) (m1 : ℤ)) := by
      have h2 : (-((m1 + 1 : ℕ) : ℤ)) + 1 = -(m1 : ℤ) := by omega
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega), h2]
    have h_not_mem_right : ((m1 + 1 : ℕ) : ℤ) ∉ Finset.Icc (-((m1 + 1 : ℕ) : ℤ)) (m1 : ℤ) := by
      rw [Finset.mem_Icc]; omega
    have h_not_mem_left : (-((m1 + 1 : ℕ) : ℤ)) ∉ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ) := by
      rw [Finset.mem_Icc]; omega
    rw [h_right, Finset.sum_insert h_not_mem_right,
        h_left, Finset.sum_insert h_not_mem_left,
        ih, Finset.sum_range_succ (fun n => f (n : ℤ)) (m1 + 1),
        Finset.sum_range_succ (fun n => f (-((n : ℤ) + 1))) m1]
    have h_neg : (-((m1 + 1 : ℕ) : ℤ)) = -((m1 : ℤ) + 1) := by omega
    rw [h_neg]
    abel

/-- Splitting a summable `ℤ`-series `∑' m : ℤ, f m` into the finite window
`∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), f m` plus the positive and negative `ℕ`-tails. -/
theorem tsum_int_eq_sum_Icc_add_tails
    (f : ℤ → ℂ) (hf : Summable f) (m1 : ℕ) :
    (∑' m : ℤ, f m) =
      (∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), f m) +
        (∑' k : ℕ, f ((m1 : ℤ) + 1 + (k : ℤ))) +
        (∑' k : ℕ, f (-((m1 : ℤ) + 1 + (k : ℤ)))) := by
  have hf1 : Summable (fun n : ℕ => f (n : ℤ)) :=
    hf.comp_injective (fun a b h => by omega)
  have hf2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (fun a b h => by omega)
  rw [tsum_of_nat_of_neg_add_one hf1 hf2,
      ← hf1.sum_add_tsum_nat_add (m1 + 1),
      ← hf2.sum_add_tsum_nat_add m1,
      sum_Icc_neg_eq_sum_range_add_sum_range f m1]
  have h1 : (∑' k : ℕ, f ((k + (m1 + 1) : ℕ) : ℤ)) =
      ∑' k : ℕ, f ((m1 : ℤ) + 1 + (k : ℤ)) := by
    refine tsum_congr fun k => ?_
    congr 1
    omega
  have h2 : (∑' k : ℕ, f (-((k + m1 : ℕ) + 1 : ℤ))) =
      ∑' k : ℕ, f (-((m1 : ℤ) + 1 + (k : ℤ))) := by
    refine tsum_congr fun k => ?_
    congr 1
    omega
  rw [h1, h2]
  ring

/-- **Spatial Truncation Error Bound by Two-Sided Kernel Tails (`norm_windowedSincGaussianSpreadArray_sub_le_tails`)**:
For `α > 0`, `1 ≤ m1`, `0 < t1`, `0 < r`, `j1 < t1`, and `∀ k < t1 * r, ‖x k‖ ≤ M` (`0 ≤ M`),
the error between the finite-window spread `windowedSincGaussianSpreadArray α m1 t1 r x j1 k2`
and the infinite-lattice spread `sincGaussianSpreadArray α t1 r x j1 k2` is bounded by `M` times
the two-sided spatial truncation tail of `sincGaussian α`. -/
theorem norm_windowedSincGaussianSpreadArray_sub_le_tails
    (α : ℝ) (hα : 0 < α) (m1 t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hm1 : 1 ≤ m1)
    (x : ℕ → ℂ) (M : ℝ) (_hM : 0 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) :
    ‖windowedSincGaussianSpreadArray α m1 t1 r x j1 k2 -
      sincGaussianSpreadArray α t1 r x j1 k2‖ ≤
      ((∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - (j1 : ℝ) / (t1 : ℝ))|) +
        (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - (j1 : ℝ) / (t1 : ℝ))|)) * M := by
  let F := sincGaussianSpreadTerm α t1 r x j1 k2
  have hF : Summable F := summable_sincGaussianSpreadTerm α hα t1 r hr x j1 k2
  rw [sincGaussianSpreadArray_eq_tsum_int α hα t1 r hr x j1 k2,
      tsum_int_eq_sum_Icc_add_tails F hF m1]
  unfold windowedSincGaussianSpreadArray
  have h_sub :
      (∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), F m) -
        ((∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), F m) +
          (∑' k : ℕ, F ((m1 : ℤ) + 1 + (k : ℤ))) +
          (∑' k : ℕ, F (-((m1 : ℤ) + 1 + (k : ℤ))))) =
      -((∑' k : ℕ, F ((m1 : ℤ) + 1 + (k : ℤ))) +
        (∑' k : ℕ, F (-((m1 : ℤ) + 1 + (k : ℤ))))) := by ring
  rw [h_sub, norm_neg]
  set δ : ℝ := (j1 : ℝ) / (t1 : ℝ)
  have hδ0 : 0 ≤ δ := div_nonneg (Nat.cast_nonneg j1) (Nat.cast_nonneg t1)
  have hδ1 : δ ≤ 1 := (div_le_one (Nat.cast_pos.mpr ht1)).mpr (by exact_mod_cast hj1.le)
  have h_tails := tsum_abs_sincGaussian_tails_le α δ m1 hα hδ0 hδ1 hm1
  have h_idx_bound : ∀ m : ℤ, ‖x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat)‖ ≤ M := by
    intro m
    have hmod_lt : (((k2 : ℤ) - m) % (r : ℤ)).toNat < r := emod_toNat_lt_of_pos hr ((k2 : ℤ) - m)
    have hidx : j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat < t1 * r := by
      calc j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat
          < t1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat := Nat.add_lt_add_right hj1 _
        _ = t1 * ((((k2 : ℤ) - m) % (r : ℤ)).toNat + 1) := by ring
        _ ≤ t1 * r := Nat.mul_le_mul_left t1 hmod_lt
    exact hx _ hidx
  have h_pos_le : ∀ k : ℕ,
      ‖F ((m1 : ℤ) + 1 + (k : ℤ))‖ ≤ |sincGaussian α ((m1 + 1 + k : ℝ) - δ)| * M := by
    intro k
    dsimp [F, sincGaussianSpreadTerm, δ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    have hcast : (((m1 : ℤ) + 1 + (k : ℤ) : ℤ) : ℝ) = (m1 + 1 + k : ℝ) := by push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_left (h_idx_bound _) (abs_nonneg _)
  have h_neg_le : ∀ k : ℕ,
      ‖F (-((m1 : ℤ) + 1 + (k : ℤ)))‖ ≤ |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)| * M := by
    intro k
    dsimp [F, sincGaussianSpreadTerm, δ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    have hcast : ((-((m1 : ℤ) + 1 + (k : ℤ)) : ℤ) : ℝ) = -((m1 + 1 + k : ℝ)) := by push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_left (h_idx_bound _) (abs_nonneg _)
  have h_sum_pos_M : Summable (fun k : ℕ => |sincGaussian α ((m1 + 1 + k : ℝ) - δ)| * M) :=
    h_tails.1.mul_right M
  have h_sum_neg_M : Summable (fun k : ℕ => |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)| * M) :=
    h_tails.2.1.mul_right M
  have h_sum_F_pos : Summable (fun k : ℕ => ‖F ((m1 : ℤ) + 1 + (k : ℤ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_pos_le h_sum_pos_M
  have h_sum_F_neg : Summable (fun k : ℕ => ‖F (-((m1 : ℤ) + 1 + (k : ℤ)))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_neg_le h_sum_neg_M
  have h1 : ‖∑' k : ℕ, F ((m1 : ℤ) + 1 + (k : ℤ))‖ ≤
      (∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) * M := by
    calc ‖∑' k : ℕ, F ((m1 : ℤ) + 1 + (k : ℤ))‖
        ≤ ∑' k : ℕ, ‖F ((m1 : ℤ) + 1 + (k : ℤ))‖ := norm_tsum_le_tsum_norm h_sum_F_pos
      _ ≤ ∑' k : ℕ, (|sincGaussian α ((m1 + 1 + k : ℝ) - δ)| * M) :=
          h_sum_F_pos.tsum_le_tsum h_pos_le h_sum_pos_M
      _ = (∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) * M := tsum_mul_right
  have h2 : ‖∑' k : ℕ, F (-((m1 : ℤ) + 1 + (k : ℤ)))‖ ≤
      (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) * M := by
    calc ‖∑' k : ℕ, F (-((m1 : ℤ) + 1 + (k : ℤ)))‖
        ≤ ∑' k : ℕ, ‖F (-((m1 : ℤ) + 1 + (k : ℤ)))‖ := norm_tsum_le_tsum_norm h_sum_F_neg
      _ ≤ ∑' k : ℕ, (|sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)| * M) :=
          h_sum_F_neg.tsum_le_tsum h_neg_le h_sum_neg_M
      _ = (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|) * M := tsum_mul_right
  have htri := norm_add_le
    (∑' k : ℕ, F ((m1 : ℤ) + 1 + (k : ℤ)))
    (∑' k : ℕ, F (-((m1 : ℤ) + 1 + (k : ℤ))))
  linarith

/-- **`[MS]` Lemma 6.1 (Concrete Spatial Window Truncation Bound `< 0.4 * 2^{-pChild p K} * M` for `windowedSincGaussianSpreadArray`, `[MS]` §6.1, Lemma 6.1 & §6.3, Term B1)**:
At `α = alphaSchedule (pWork p K)` and window half-width `m1 = 2 * pChild p K`,
`lemma2_sincGaussian_spatial_tail_bound` proves that for any `0 < t1`, `0 < r`, `j1 < t1`, `k2 : ℕ`,
and input `‖x k‖ ≤ M` (`0 < M`), the finite-window spread array `windowedSincGaussianSpreadArray`
differs from `sincGaussianSpreadArray` by strictly less than `0.4 * 2^{-pChild p K} * M`. -/
theorem norm_windowedSincGaussianSpreadArray_sub_lt
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM : 0 < M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) :
    ‖windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2‖ <
      (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  set p_work := pWork p K
  set p_child := pChild p K
  set α := alphaSchedule p_work
  set m1 := 2 * p_child
  have hp_work_pos : 0 < p_work := by unfold p_work pWork; omega
  have hp_child_ge12 : 12 ≤ p_child := by unfold p_child pChild pWork; omega
  have hm1_ge8 : 8 ≤ m1 := by omega
  have hα : 0 < α := alphaSchedule_pos p_work hp_work_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi_gt : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_lt : Real.log 2 < (1 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hrad_pos : 0 < (p_work : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos (Nat.cast_pos.mpr hp_work_pos) hlog2_pos) hpi
  have hpi_alpha_sq : Real.pi * α ^ 2 = 4 * (p_work : ℝ) * Real.log 2 := by
    dsimp [α, alphaSchedule]
    calc Real.pi * (2 * Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi)) ^ 2
        = Real.pi * (4 * (Real.sqrt ((p_work : ℝ) * Real.log 2 / Real.pi)) ^ 2) := by ring
      _ = Real.pi * (4 * ((p_work : ℝ) * Real.log 2 / Real.pi)) := by rw [Real.sq_sqrt hrad_pos.le]
      _ = 4 * (p_work : ℝ) * Real.log 2 := by field_simp [hpi.ne']
  have hp_le : (p_work : ℝ) ≤ (p_child : ℝ) := by
    exact_mod_cast (by unfold p_work p_child pChild; omega : p_work ≤ p_child)
  have hm1_cast : (m1 : ℝ) = 2 * (p_child : ℝ) := by
    dsimp [m1]
    push_cast
    ring
  have hα_sq_le : α ^ 2 ≤ 4 * (p_child : ℝ) := by
    have h1 : Real.pi * α ^ 2 ≤ Real.pi * (4 * (p_child : ℝ)) := by
      rw [hpi_alpha_sq]
      nlinarith
    exact le_of_mul_le_mul_left h1 hpi
  have h_win : (p_child : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hα), hm1_cast]
    have h_log_alpha : Real.log 2 * α ^ 2 ≤ 4 * (p_child : ℝ) := by
      nlinarith [sq_nonneg α]
    have h1 : (p_child : ℝ) * Real.log 2 * α ^ 2 ≤ (p_child : ℝ) * (4 * (p_child : ℝ)) := by
      calc (p_child : ℝ) * Real.log 2 * α ^ 2
          = (p_child : ℝ) * (Real.log 2 * α ^ 2) := by ring
        _ ≤ (p_child : ℝ) * (4 * (p_child : ℝ)) :=
            mul_le_mul_of_nonneg_left h_log_alpha (Nat.cast_nonneg p_child)
    have h2 : (p_child : ℝ) * (4 * (p_child : ℝ)) ≤ Real.pi * (2 * (p_child : ℝ)) ^ 2 := by
      calc (p_child : ℝ) * (4 * (p_child : ℝ))
          = 1 * (2 * (p_child : ℝ)) ^ 2 := by ring
        _ ≤ Real.pi * (2 * (p_child : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    exact h1.trans h2
  have h_step : (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hα), hm1_cast]
    have hp_nonneg : (0 : ℝ) ≤ (p_child : ℝ) := Nat.cast_nonneg p_child
    nlinarith
  set δ : ℝ := (j1 : ℝ) / (t1 : ℝ)
  have hδ0 : 0 ≤ δ := div_nonneg (Nat.cast_nonneg j1) (Nat.cast_nonneg t1)
  have hδ1 : δ ≤ 1 := (div_le_one (Nat.cast_pos.mpr ht1)).mpr (by exact_mod_cast hj1.le)
  have h_le_tails := norm_windowedSincGaussianSpreadArray_sub_le_tails
    α hα m1 t1 r ht1 hr (by omega) x M hM.le hx j1 k2 hj1
  have h_tail_lt := (lemma2_sincGaussian_spatial_tail_bound
    α δ m1 p_child hα hδ0 hδ1 hm1_ge8 h_win h_step).2
  exact h_le_tails.trans_lt (mul_lt_mul_of_pos_right h_tail_lt hM)

/-- **`ℓ_∞` Norm Bound for `windowedSincGaussianSpreadArray` (`≤ (r + 1) * M`, `[MS]` §4.2 & §5.1)**:
For any `p, K : ℕ`, `0 < t1`, `0 < r`, and `∀ k < t1 * r, ‖x k‖ ≤ M` (`0 < M`), every entry
`windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2`
(`j1 < t1`, `k2 < r`) has norm at most `((r : ℝ) + 1) * M`. -/
theorem norm_windowedSincGaussianSpreadArray_le
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM : 0 < M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r) :
    ‖windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2‖ ≤
      ((r : ℝ) + 1) * M := by
  set α := alphaSchedule (pWork p K)
  set m1 := 2 * pChild p K
  have hα : 0 < α := alphaSchedule_pos (pWork p K) (by unfold pWork; omega)
  have h_diff := (norm_windowedSincGaussianSpreadArray_sub_lt p K t1 r ht1 hr x M hM hx j1 k2 hj1).le
  have h_inf := norm_sincGaussianSpreadArray_le α hα t1 r hr x M hx j1 k2 hj1 hk2
  have hzpow_le : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have h_diff_le_M : (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M ≤ M := by
    nlinarith
  have htri :
      ‖windowedSincGaussianSpreadArray α m1 t1 r x j1 k2‖ ≤
        ‖windowedSincGaussianSpreadArray α m1 t1 r x j1 k2 -
          sincGaussianSpreadArray α t1 r x j1 k2‖ +
        ‖sincGaussianSpreadArray α t1 r x j1 k2‖ := by
    have hsplit : windowedSincGaussianSpreadArray α m1 t1 r x j1 k2 =
        (windowedSincGaussianSpreadArray α m1 t1 r x j1 k2 -
          sincGaussianSpreadArray α t1 r x j1 k2) +
        sincGaussianSpreadArray α t1 r x j1 k2 := by ring
    conv_lhs => rw [hsplit]
    exact norm_add_le _ _
  linarith

/-- Linearity of `dft2D` under subtraction. -/
theorem dft2D_sub (t1 r : ℕ) (U V : ℕ → ℕ → ℂ) (u1 u2 : ℕ) :
    dft2D t1 r (fun j1 k2 => U j1 k2 - V j1 k2) u1 u2 =
      dft2D t1 r U u1 u2 - dft2D t1 r V u1 u2 := by
  unfold dft2D
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- `ℓ_∞` contractivity of the normalized 2D DFT (`dft2D_norm_le`, `[MS]` §3.5):
if `‖U j1 k2‖ ≤ B` for all `j1 < t1` and `k2 < r` (`t1, r > 0`), then `‖dft2D t1 r U u1 u2‖ ≤ B`. -/
theorem dft2D_norm_le (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (U : ℕ → ℕ → ℂ) (B : ℝ) (hU : ∀ j1 < t1, ∀ k2 < r, ‖U j1 k2‖ ≤ B)
    (u1 u2 : ℕ) :
    ‖dft2D t1 r U u1 u2‖ ≤ B := by
  unfold dft2D
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have htr_pos : (0 : ℝ) < ((t1 * r : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ht1 hr
  have hsum :
      ‖∑ j1 ∈ Finset.range t1, ∑ k2 ∈ Finset.range r,
        U j1 k2 * stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
          stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))‖ ≤
        ((t1 * r : ℕ) : ℝ) * B := by
    calc ‖∑ j1 ∈ Finset.range t1, ∑ k2 ∈ Finset.range r,
          U j1 k2 * stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
            stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))‖
        ≤ ∑ j1 ∈ Finset.range t1,
            ‖∑ k2 ∈ Finset.range r,
              U j1 k2 * stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
                stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ j1 ∈ Finset.range t1, ∑ k2 ∈ Finset.range r,
            ‖U j1 k2 * stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
              stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))‖ :=
          Finset.sum_le_sum fun j1 _ => norm_sum_le _ _
      _ ≤ ∑ _j1 ∈ Finset.range t1, ∑ _k2 ∈ Finset.range r, B := by
          refine Finset.sum_le_sum fun j1 hj1 => Finset.sum_le_sum fun k2 hk2 => ?_
          rw [norm_mul, norm_mul, norm_stdChar, norm_stdChar, mul_one, mul_one]
          exact hU j1 (Finset.mem_range.mp hj1) k2 (Finset.mem_range.mp hk2)
      _ = ((t1 * r : ℕ) : ℝ) * B := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  calc (1 / ((t1 * r : ℕ) : ℝ)) *
        ‖∑ j1 ∈ Finset.range t1, ∑ k2 ∈ Finset.range r,
          U j1 k2 * stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
            stdChar (((k2 * u2 : ℕ) : ℝ) / (r : ℝ))‖
      ≤ (1 / ((t1 * r : ℕ) : ℝ)) * (((t1 * r : ℕ) : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B := by field_simp [htr_pos.ne']

/-- **Term B1 in 2D Frequency Domain (`norm_dft2D_windowedSincGaussianSpreadArray_sub_le`, `[MS]` §6.1, Lemma 6.1)**:
By `ℓ_∞` contractivity of `dft2D` (`dft2D_norm_le`) and `norm_windowedSincGaussianSpreadArray_sub_lt`
(which applies `lemma2_sincGaussian_spatial_tail_bound`), the 2D DFT of the finite-window spread
`windowedSincGaussianSpreadArray` differs from the 2D DFT of `sincGaussianSpreadArray` at every
mode `(u1, u2)` by at most `0.4 * 2^{-pChild p K} * M`. -/
theorem norm_dft2D_windowedSincGaussianSpreadArray_sub_le
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM : 0 < M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u1 u2 : ℕ) :
    ‖dft2D t1 r
        (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x) u1 u2 -
      dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) u1 u2‖ ≤
      (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  rw [← dft2D_sub]
  refine dft2D_norm_le t1 r ht1 hr _ _ (fun j1 hj1 k2 _ => ?_) u1 u2
  exact (norm_windowedSincGaussianSpreadArray_sub_lt p K t1 r ht1 hr x M hM hx j1 k2 hj1).le

/-- **Tighter Spatial Window Half-Width `m_1 = pChild p K` (`norm_windowedSincGaussianSpreadArray_sub_lt_tight`, `[MS]` §6.1, Lemma 6.1)**:
Because `π^2 > 9 > 4 (log 2)^2`, even the halved window half-width `m_1 = pChild p K`
(`W = 2 p_child + 1` taps) satisfies `π m_1^2 / α^2 ≥ p_child * log 2` and `2 π m_1 / α^2 ≥ 1/2`,
yielding the identical `< 0.4 * 2^{-pChild p K} * M` spatial truncation bound. -/
theorem norm_windowedSincGaussianSpreadArray_sub_lt_tight
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM : 0 < M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) :
    ‖windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (pChild p K) t1 r x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2‖ <
      (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  set p_work := pWork p K
  set p_child := pChild p K
  set α := alphaSchedule p_work
  set m1 := p_child
  have hp_work_pos : 0 < p_work := by unfold p_work pWork; omega
  have hp_child_ge12 : 12 ≤ p_child := by unfold p_child pChild pWork; omega
  have hm1_ge8 : 8 ≤ m1 := by omega
  have hα : 0 < α := alphaSchedule_pos p_work hp_work_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi_gt : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_lt : Real.log 2 < (0.7 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hpi_alpha_sq : Real.pi * α ^ 2 = 4 * (p_work : ℝ) * Real.log 2 :=
    pi_mul_alphaSchedule_sq p_work hp_work_pos
  have hp_le : (p_work : ℝ) ≤ (p_child : ℝ) := by
    exact_mod_cast (by unfold p_work p_child pChild; omega : p_work ≤ p_child)
  have hp_work_nonneg : (0 : ℝ) ≤ (p_work : ℝ) := Nat.cast_nonneg p_work
  have hp_child_nonneg : (0 : ℝ) ≤ (p_child : ℝ) := Nat.cast_nonneg p_child
  have h_win : (p_child : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hα)]
    have h1 : Real.pi * ((p_child : ℝ) * Real.log 2 * α ^ 2) =
        ((4 : ℝ) * (Real.log 2) ^ 2) * ((p_child : ℝ) * (p_work : ℝ)) := by
      calc Real.pi * ((p_child : ℝ) * Real.log 2 * α ^ 2)
          = (p_child : ℝ) * Real.log 2 * (Real.pi * α ^ 2) := by ring
        _ = (p_child : ℝ) * Real.log 2 * (4 * (p_work : ℝ) * Real.log 2) := by rw [hpi_alpha_sq]
        _ = ((4 : ℝ) * (Real.log 2) ^ 2) * ((p_child : ℝ) * (p_work : ℝ)) := by ring
    have hlog_sq : (4 : ℝ) * (Real.log 2) ^ 2 ≤ Real.pi * Real.pi := by nlinarith
    have hp_prod : (p_child : ℝ) * (p_work : ℝ) ≤ (p_child : ℝ) ^ 2 := by nlinarith
    have h2 : ((4 : ℝ) * (Real.log 2) ^ 2) * ((p_child : ℝ) * (p_work : ℝ)) ≤
        Real.pi * (Real.pi * (m1 : ℝ) ^ 2) := by
      dsimp [m1]
      calc ((4 : ℝ) * (Real.log 2) ^ 2) * ((p_child : ℝ) * (p_work : ℝ))
          ≤ (Real.pi * Real.pi) * (p_child : ℝ) ^ 2 :=
            mul_le_mul hlog_sq hp_prod (by positivity) (by positivity)
        _ = Real.pi * (Real.pi * (p_child : ℝ) ^ 2) := by ring
    exact le_of_mul_le_mul_left (h1.trans_le h2) hpi
  have hα_sq_le : α ^ 2 ≤ 4 * (p_child : ℝ) := by
    have h1 : Real.pi * α ^ 2 ≤ Real.pi * (4 * (p_child : ℝ)) := by
      rw [hpi_alpha_sq]
      nlinarith
    exact le_of_mul_le_mul_left h1 hpi
  have h_step : (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hα)]
    dsimp [m1]
    nlinarith
  set δ : ℝ := (j1 : ℝ) / (t1 : ℝ)
  have hδ0 : 0 ≤ δ := div_nonneg (Nat.cast_nonneg j1) (Nat.cast_nonneg t1)
  have hδ1 : δ ≤ 1 := (div_le_one (Nat.cast_pos.mpr ht1)).mpr (by exact_mod_cast hj1.le)
  have h_le_tails := norm_windowedSincGaussianSpreadArray_sub_le_tails
    α hα m1 t1 r ht1 hr (by omega) x M hM.le hx j1 k2 hj1
  have h_tail_lt := (lemma2_sincGaussian_spatial_tail_bound
    α δ m1 p_child hα hδ0 hδ1 hm1_ge8 h_win h_step).2
  exact h_le_tails.trans_lt (mul_lt_mul_of_pos_right h_tail_lt hM)

/-- **2D Frequency Domain Error Bound for Tighter Half-Width `m_1 = pChild p K` (`norm_dft2D_windowedSincGaussianSpreadArray_sub_le_tight`)**: -/
theorem norm_dft2D_windowedSincGaussianSpreadArray_sub_le_tight
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM : 0 < M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u1 u2 : ℕ) :
    ‖dft2D t1 r
        (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (pChild p K) t1 r x) u1 u2 -
      dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) u1 u2‖ ≤
      (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  rw [← dft2D_sub]
  refine dft2D_norm_le t1 r ht1 hr _ _ (fun j1 hj1 k2 _ => ?_) u1 u2
  exact (norm_windowedSincGaussianSpreadArray_sub_lt_tight p K t1 r ht1 hr x M hM hx j1 k2 hj1).le

/-- **Window-Size `ℓ_∞` Norm Bound for `windowedSincGaussianSpreadArray` (`≤ (2 m_1 + 1) * M`, `[MS]` §4.2 & §5.1)**:
Because `windowedSincGaussianSpreadArray α m1 t1 r x j1 k2` sums over `Finset.Icc (-m1) m1` of
cardinality `2 * m1 + 1` and each tap has `|sincGaussian α t| ≤ 1`, its norm is at most `(2 * m1 + 1) * M`
(giving `min((r + 1) * M, (2 * m1 + 1) * M)` when combined with `norm_windowedSincGaussianSpreadArray_le`). -/
theorem norm_windowedSincGaussianSpreadArray_le_window
    (α : ℝ) (m1 t1 r : ℕ) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) :
    ‖windowedSincGaussianSpreadArray α m1 t1 r x j1 k2‖ ≤ (2 * (m1 : ℝ) + 1) * M := by
  unfold windowedSincGaussianSpreadArray
  calc ‖∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), sincGaussianSpreadTerm α t1 r x j1 k2 m‖
      ≤ ∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), ‖sincGaussianSpreadTerm α t1 r x j1 k2 m‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), M := by
        refine Finset.sum_le_sum fun m _ => ?_
        unfold sincGaussianSpreadTerm
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hmod_lt : (((k2 : ℤ) - m) % (r : ℤ)).toNat < r := emod_toNat_lt_of_pos hr ((k2 : ℤ) - m)
        have hidx : j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat < t1 * r := by
          calc j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat
              < t1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat := Nat.add_lt_add_right hj1 _
            _ = t1 * ((((k2 : ℤ) - m) % (r : ℤ)).toNat + 1) := by ring
            _ ≤ t1 * r := Nat.mul_le_mul_left t1 hmod_lt
        have hx_le : ‖x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat)‖ ≤ M := hx _ hidx
        have hsinc_le : |sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤ 1 := by
          unfold sincGaussian
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hs : |normSinc ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤ 1 := abs_realSinc_le_one _
          have he : Real.exp (-(Real.pi / α ^ 2) * ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ)) ^ 2) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            have h1 : 0 ≤ Real.pi / α ^ 2 := div_nonneg Real.pi_pos.le (sq_nonneg α)
            have h2 : 0 ≤ ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ)) ^ 2 := sq_nonneg _
            nlinarith
          calc |normSinc ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))| *
                Real.exp (-(Real.pi / α ^ 2) * ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ)) ^ 2)
              ≤ 1 * 1 := mul_le_mul hs he (Real.exp_pos _).le zero_le_one
            _ = 1 := mul_one 1
        calc ‖x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat)‖ *
              |sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))|
            ≤ M * 1 := mul_le_mul hx_le hsinc_le (abs_nonneg _) ((norm_nonneg _).trans hx_le)
          _ = M := mul_one M
    _ = (2 * (m1 : ℝ) + 1) * M := by
        rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
        congr 1
        have hcard : ((m1 : ℤ) + 1 - -(m1 : ℤ)).toNat = 2 * m1 + 1 := by omega
        rw [hcard]
        push_cast
        ring

/-! ## 6. `[MS]` Section 5.2 (Lemma 5.2): Step-by-Step Rounded Bidiagonal and Nyquist Solvers (Term D) -/

/-- **Quantized Forward Homogeneous Powers (`zHomFwdQuantized`, `[MS]` §5.2, Lemma 5.2, Term D)**:
Computes the homogeneous geometric powers `(-c_1 / c_0)^{u_1}` via the step-rounded recurrence
`zHom(0) = 1`, `zHom(u_1 + 1) = complexQuantize q ((-c_1 / c_0) * zHom(u_1))`. -/
noncomputable def zHomFwdQuantized (q : ℕ) (c0 c1 : ℂ) : ℕ → ℂ
  | 0 => 1
  | u1 + 1 => complexQuantize q ((-c1 / c0) * zHomFwdQuantized q c0 c1 u1)

/-- **Quantized Backward Homogeneous Powers (`zHomBwdQuantized`, `[MS]` §5.2, Lemma 5.2, Term D)**:
Computes the backward homogeneous geometric powers `(-c_0 / c_1)^d` via the step-rounded recurrence
`zHomBwdQuantized q c0 c1 = zHomFwdQuantized q c1 c0`. -/
noncomputable def zHomBwdQuantized (q : ℕ) (c0 c1 : ℂ) : ℕ → ℂ :=
  zHomFwdQuantized q c1 c0

/-- **Quantized Forward Bidiagonal Particular Sweep (`zPartFwdQuantized`, `[MS]` §5.2, Lemma 5.2, Term D)**:
Executes the forward particular recurrence `Z_part(0) = 0`,
`Z_part(u_1 + 1) = complexQuantize q (Y(u_1 + 1) / c_0 + (-c_1 / c_0) * Z_part(u_1))`,
rounding each recurrence step to `q + 2` fractional bits via `complexQuantize q`. -/
noncomputable def zPartFwdQuantized (q : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | u1 + 1 => complexQuantize q (Y (u1 + 1) / c0 + (-c1 / c0) * zPartFwdQuantized q c0 c1 Y u1)

/-- **Quantized Forward Cyclic Bidiagonal Solver (`solveBidiagonalFwdQuantized`, `[MS]` §5.2, Lemma 5.2, Term D)**:
Computes `Z(u_1)` via the step-rounded sweep `zPartFwdQuantized q c0 c1 Y` and step-rounded
homogeneous powers `zHomFwdQuantized q c0 c1`, rounds the cyclic boundary value `Z_0` via
`complexQuantize q`, and rounds the combined output via `complexQuantize q`. -/
noncomputable def solveBidiagonalFwdQuantized (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) : ℂ :=
  let Z0 := complexQuantize q
    ((Y 0 - c1 * zPartFwdQuantized q c0 c1 Y (t1 - 1)) /
      (c0 + c1 * zHomFwdQuantized q c0 c1 (t1 - 1)))
  complexQuantize q (zPartFwdQuantized q c0 c1 Y u1 + Z0 * zHomFwdQuantized q c0 c1 u1)

/-- **Quantized Backward Bidiagonal Particular Sweep (`zPartBwdQuantized`, `[MS]` §5.2, Lemma 5.2, Term D)**:
Executes the backward particular recurrence `zPartBwd(0) = 0`,
`zPartBwd(d + 1) = complexQuantize q (Y(t_1 - 1 - d) / c_1 + (-c_0 / c_1) * zPartBwd(d))`,
rounding each recurrence step to `q + 2` fractional bits via `complexQuantize q`. -/
noncomputable def zPartBwdQuantized (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | d + 1 => complexQuantize q (Y (t1 - 1 - d) / c1 + (-c0 / c1) * zPartBwdQuantized q t1 c0 c1 Y d)

/-- **Quantized Backward Cyclic Bidiagonal Solver (`solveBidiagonalBwdQuantized`, `[MS]` §5.2, Lemma 5.2, Term D)**:
Computes `Z(u_1)` via the step-rounded backward sweep `zPartBwdQuantized q t1 c0 c1 Y` and
step-rounded backward homogeneous powers `zHomBwdQuantized q c0 c1`, rounds `Z_last` via
`complexQuantize q`, and rounds the combined output via `complexQuantize q`. -/
noncomputable def solveBidiagonalBwdQuantized (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) : ℂ :=
  let d := t1 - 1 - u1
  let Z_last := complexQuantize q
    ((Y 0 - c0 * zPartBwdQuantized q t1 c0 c1 Y (t1 - 1)) /
      (c1 + c0 * zHomBwdQuantized q c0 c1 (t1 - 1)))
  complexQuantize q (zPartBwdQuantized q t1 c0 c1 Y d + Z_last * zHomBwdQuantized q c0 c1 d)

/-- **Quantized Nyquist Particular Sweep (`zPartNyqQuantized`, `[MS]` §5.2, Lemma 5.2, Term D)**:
Executes the Nyquist particular recurrence `Z_part(0) = 0`,
`Z_part(u_1 + 1) = complexQuantize q (Y(u_1 + 1) / c_0 - Z_part(u_1))`,
rounding each recurrence step to `q + 2` fractional bits via `complexQuantize q`. -/
noncomputable def zPartNyqQuantized (q : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | u1 + 1 => complexQuantize q (Y (u1 + 1) / c0 - zPartNyqQuantized q c0 Y u1)

/-- **Quantized Nyquist Column Solver (`solveNyquistQuantized`, `[MS]` §5.2, Lemma 5.2, Term D)**:
Computes `Z(u_1)` via the step-rounded Nyquist sweep `zPartNyqQuantized q c0 Y`, rounds the
alternating-sum correction `diff` via `complexQuantize q`, and rounds the combined output via
`complexQuantize q`. -/
noncomputable def solveNyquistQuantized (q t1 : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (alt_q : ℂ) (u1 : ℕ) : ℂ :=
  let alt_part := ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyqQuantized q c0 Y v
  let diff := complexQuantize q ((alt_q - alt_part) / (t1 : ℂ))
  complexQuantize q (zPartNyqQuantized q c0 Y u1 + (-1 : ℂ) ^ u1 * diff)

/-- Step-by-step error bound for `zHomFwdQuantized`: when `0 < ‖c0‖` and `‖c1‖ ≤ ‖c0‖`,
`‖zHomFwdQuantized q c0 c1 u1 - zHomFwd c0 c1 u1‖ ≤ u1 * complexQuantizeMaxErr q`. -/
theorem norm_zHomFwdQuantized_sub_le
    (q : ℕ) (c0 c1 : ℂ) (hc0_pos : 0 < ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖) (u1 : ℕ) :
    ‖zHomFwdQuantized q c0 c1 u1 - zHomFwd c0 c1 u1‖ ≤
      (u1 : ℝ) * complexQuantizeMaxErr q := by
  induction u1 with
  | zero =>
    simp [zHomFwdQuantized, zHomFwd]
  | succ u1 ih =>
    dsimp only [zHomFwdQuantized]
    unfold zHomFwd at ih ⊢
    rw [pow_succ']
    set step_unq := (-c1 / c0) * zHomFwdQuantized q c0 c1 u1
    have hsplit :
        complexQuantize q step_unq - (-c1 / c0) * (-c1 / c0) ^ u1 =
          (complexQuantize q step_unq - step_unq) +
            (-c1 / c0) * (zHomFwdQuantized q c0 c1 u1 - (-c1 / c0) ^ u1) := by
      dsimp only [step_unq]
      ring
    rw [hsplit]
    have h1 : ‖complexQuantize q step_unq - step_unq‖ ≤ complexQuantizeMaxErr q :=
      norm_complexQuantize_sub_le q step_unq
    have hratio_le1 : ‖-c1 / c0‖ ≤ 1 := by
      rw [norm_div, norm_neg]
      exact (div_le_one hc0_pos).mpr hc10
    have h2 :
        ‖(-c1 / c0) * (zHomFwdQuantized q c0 c1 u1 - (-c1 / c0) ^ u1)‖ ≤
          (u1 : ℝ) * complexQuantizeMaxErr q := by
      rw [norm_mul]
      calc ‖-c1 / c0‖ * ‖zHomFwdQuantized q c0 c1 u1 - (-c1 / c0) ^ u1‖
          ≤ 1 * ((u1 : ℝ) * complexQuantizeMaxErr q) :=
            mul_le_mul hratio_le1 ih (norm_nonneg _) zero_le_one
        _ = (u1 : ℝ) * complexQuantizeMaxErr q := one_mul _
    have htri := norm_add_le (complexQuantize q step_unq - step_unq)
      ((-c1 / c0) * (zHomFwdQuantized q c0 c1 u1 - (-c1 / c0) ^ u1))
    push_cast
    linarith

/-- Norm bound for `zHomFwdQuantized`: when `0 < ‖c0‖` and `‖c1‖ ≤ ‖c0‖`,
`‖zHomFwdQuantized q c0 c1 u1‖ ≤ 1 + u1 * complexQuantizeMaxErr q`. -/
theorem norm_zHomFwdQuantized_le
    (q : ℕ) (c0 c1 : ℂ) (hc0_pos : 0 < ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖) (u1 : ℕ) :
    ‖zHomFwdQuantized q c0 c1 u1‖ ≤ 1 + (u1 : ℝ) * complexQuantizeMaxErr q := by
  have hsub := norm_zHomFwdQuantized_sub_le q c0 c1 hc0_pos hc10 u1
  have hhom : ‖zHomFwd c0 c1 u1‖ ≤ 1 := by
    unfold zHomFwd
    rw [norm_pow, norm_div, norm_neg]
    exact pow_le_one₀ (div_nonneg (norm_nonneg _) hc0_pos.le) ((div_le_one hc0_pos).mpr hc10)
  have htri := norm_add_le (zHomFwdQuantized q c0 c1 u1 - zHomFwd c0 c1 u1) (zHomFwd c0 c1 u1)
  rw [sub_add_cancel] at htri
  linarith

/-- Evaluation of `solveBidiagonalFwd` at index `0` equals the boundary quotient `Z0`. -/
theorem solveBidiagonalFwd_zero (t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) :
    (Y 0 - c1 * zPartFwd c0 c1 Y (t1 - 1)) / (c0 + c1 * zHomFwd c0 c1 (t1 - 1)) =
      solveBidiagonalFwd t1 c0 c1 Y 0 := by
  unfold solveBidiagonalFwd
  dsimp only
  have hz0_part : zPartFwd c0 c1 Y 0 = 0 := rfl
  have hz0_hom : zHomFwd c0 c1 0 = 1 := rfl
  rw [hz0_part, hz0_hom]
  ring

/-- Backward-error effective right-hand side `zPartFwdEffRHS` for `zPartFwdQuantized`:
satisfies `zPartFwdQuantized q c0 c1 Y u1 = zPartFwd c0 c1 (zPartFwdEffRHS q c0 c1 Y) u1` identically
whenever `c0 ≠ 0`. -/
noncomputable def zPartFwdEffRHS (q : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : ℕ → ℂ
  | 0 => Y 0
  | u1 + 1 => c0 * zPartFwdQuantized q c0 c1 Y (u1 + 1) + c1 * zPartFwdQuantized q c0 c1 Y u1

/-- Exact backward-error representation of `zPartFwdQuantized` as an exact `zPartFwd` sweep on
`zPartFwdEffRHS`. -/
theorem zPartFwdQuantized_eq_zPartFwd_effRHS
    (q : ℕ) (c0 c1 : ℂ) (hc0 : c0 ≠ 0) (Y : ℕ → ℂ) (u1 : ℕ) :
    zPartFwdQuantized q c0 c1 Y u1 = zPartFwd c0 c1 (zPartFwdEffRHS q c0 c1 Y) u1 := by
  induction u1 with
  | zero => rfl
  | succ u1 ih =>
    rw [zPartFwd_succ, ← ih]
    dsimp only [zPartFwdEffRHS]
    field_simp [hc0]
    ring

/-- Pointwise backward-error bound for `zPartFwdEffRHS`: when `c0 ≠ 0` and `‖c0‖ ≤ 1`,
every entry `k` satisfies `‖zPartFwdEffRHS q c0 c1 Y k - Y k‖ ≤ complexQuantizeMaxErr q`. -/
theorem norm_zPartFwdEffRHS_sub_le
    (q : ℕ) (c0 c1 : ℂ) (hc0 : c0 ≠ 0) (hc0_le : ‖c0‖ ≤ 1) (Y : ℕ → ℂ) (k : ℕ) :
    ‖zPartFwdEffRHS q c0 c1 Y k - Y k‖ ≤ complexQuantizeMaxErr q := by
  cases k with
  | zero =>
    simp only [zPartFwdEffRHS, sub_self, norm_zero]
    unfold complexQuantizeMaxErr
    positivity
  | succ u1 =>
    dsimp only [zPartFwdEffRHS, zPartFwdQuantized]
    set step_unq := Y (u1 + 1) / c0 + (-c1 / c0) * zPartFwdQuantized q c0 c1 Y u1
    have hident :
        c0 * complexQuantize q step_unq + c1 * zPartFwdQuantized q c0 c1 Y u1 - Y (u1 + 1) =
          c0 * (complexQuantize q step_unq - step_unq) := by
      dsimp only [step_unq]
      field_simp [hc0]
      ring
    rw [hident, norm_mul]
    calc ‖c0‖ * ‖complexQuantize q step_unq - step_unq‖
        ≤ 1 * complexQuantizeMaxErr q :=
          mul_le_mul hc0_le (norm_complexQuantize_sub_le q step_unq) (norm_nonneg _) zero_le_one
      _ = complexQuantizeMaxErr q := one_mul _

/-- Difference between `solveBidiagonalFwdQuantized` (including step-rounded `zHomFwdQuantized`
powers) and the exact `solveBidiagonalFwd` on `zPartFwdEffRHS`. -/
theorem norm_solveBidiagonalFwdQuantized_sub_effRHS_le
    (q t1 : ℕ) (ht1 : 0 < t1) (c0 c1 : ℂ)
    (hc0_ge : (0.4999 : ℝ) ≤ ‖c0‖) (hc0_le : ‖c0‖ ≤ 1)
    (hc10 : ‖c1‖ ≤ ‖c0‖) (hratio : (‖c1‖ / ‖c0‖) ^ t1 ≤ (0.1501 : ℝ))
    (ht1_err : (t1 : ℝ) * complexQuantizeMaxErr q ≤ (0.001 : ℝ))
    (Y : ℕ → ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    ‖solveBidiagonalFwdQuantized q t1 c0 c1 Y u1 -
        solveBidiagonalFwd t1 c0 c1 (zPartFwdEffRHS q c0 c1 Y) u1‖ ≤
      (2.001 : ℝ) * complexQuantizeMaxErr q +
        4 * ((t1 : ℝ) * complexQuantizeMaxErr q) *
          ‖solveBidiagonalFwd t1 c0 c1 (zPartFwdEffRHS q c0 c1 Y) 0‖ := by
  have hc0_pos : 0 < ‖c0‖ := by linarith
  have hc0 : c0 ≠ 0 := norm_pos_iff.mp hc0_pos
  have hc1_le1 : ‖c1‖ ≤ 1 := hc10.trans hc0_le
  have hq_nonneg : 0 ≤ complexQuantizeMaxErr q := by
    unfold complexQuantizeMaxErr
    positivity
  have ht1_err_nonneg : 0 ≤ (t1 : ℝ) * complexQuantizeMaxErr q :=
    mul_nonneg (Nat.cast_nonneg t1) hq_nonneg
  unfold solveBidiagonalFwdQuantized solveBidiagonalFwd
  dsimp only
  rw [zPartFwdQuantized_eq_zPartFwd_effRHS q c0 c1 hc0 Y (t1 - 1),
      zPartFwdQuantized_eq_zPartFwd_effRHS q c0 c1 hc0 Y u1]
  set Y_eff := zPartFwdEffRHS q c0 c1 Y
  have hY0 : Y_eff 0 = Y 0 := rfl
  rw [hY0]
  set N := Y 0 - c1 * zPartFwd c0 c1 Y_eff (t1 - 1)
  set D := c0 + c1 * zHomFwd c0 c1 (t1 - 1)
  set D_q := c0 + c1 * zHomFwdQuantized q c0 c1 (t1 - 1)
  set Z0_exact := N / D
  set Z0_unq := N / D_q
  set Z0 := complexQuantize q Z0_unq
  have hZ0_exact_eq : Z0_exact = solveBidiagonalFwd t1 c0 c1 Y_eff 0 := by
    dsimp only [Z0_exact, N, D]
    rw [← hY0]
    exact solveBidiagonalFwd_zero t1 c0 c1 Y_eff
  have htail_eq : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ = ‖c0‖ * (‖c1‖ / ‖c0‖) ^ t1 := by
    unfold zHomFwd
    rw [norm_mul, norm_pow, norm_div, norm_neg]
    have ht1_eq : t1 = (t1 - 1) + 1 := by omega
    conv_rhs => rw [ht1_eq, pow_succ]
    have hc0_ne : ‖c0‖ ≠ 0 := hc0_pos.ne'
    field_simp [hc0_ne]
  have htail_le : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ ≤ ‖c0‖ * (0.1501 : ℝ) := by
    rw [htail_eq]
    exact mul_le_mul_of_nonneg_left hratio hc0_pos.le
  have hD_ge : (0.424 : ℝ) ≤ ‖D‖ := by
    have htri := norm_sub_le D (c1 * zHomFwd c0 c1 (t1 - 1))
    have hsub : D - c1 * zHomFwd c0 c1 (t1 - 1) = c0 := by
      dsimp only [D]
      ring
    rw [hsub] at htri
    nlinarith
  have ht1_sub_le : ((t1 - 1 : ℕ) : ℝ) ≤ (t1 : ℝ) := by
    exact_mod_cast Nat.sub_le t1 1
  have hhom_t1 :
      ‖zHomFwd c0 c1 (t1 - 1) - zHomFwdQuantized q c0 c1 (t1 - 1)‖ ≤
        (t1 : ℝ) * complexQuantizeMaxErr q := by
    rw [norm_sub_rev]
    exact (norm_zHomFwdQuantized_sub_le q c0 c1 hc0_pos hc10 (t1 - 1)).trans
      (mul_le_mul_of_nonneg_right ht1_sub_le hq_nonneg)
  have hD_diff : ‖D - D_q‖ ≤ (t1 : ℝ) * complexQuantizeMaxErr q := by
    have heq : D - D_q = c1 * (zHomFwd c0 c1 (t1 - 1) - zHomFwdQuantized q c0 c1 (t1 - 1)) := by
      dsimp only [D, D_q]
      ring
    rw [heq, norm_mul]
    calc ‖c1‖ * ‖zHomFwd c0 c1 (t1 - 1) - zHomFwdQuantized q c0 c1 (t1 - 1)‖
        ≤ 1 * ((t1 : ℝ) * complexQuantizeMaxErr q) :=
          mul_le_mul hc1_le1 hhom_t1 (norm_nonneg _) zero_le_one
      _ = (t1 : ℝ) * complexQuantizeMaxErr q := one_mul _
  have hDq_ge : (0.4 : ℝ) ≤ ‖D_q‖ := by
    have htri := norm_add_le D_q (D - D_q)
    have hadd : D_q + (D - D_q) = D := by ring
    rw [hadd] at htri
    linarith
  have hD_pos : 0 < ‖D‖ := by linarith
  have hDq_pos : 0 < ‖D_q‖ := by linarith
  have hD_ne : D ≠ 0 := norm_pos_iff.mp hD_pos
  have hDq_ne : D_q ≠ 0 := norm_pos_iff.mp hDq_pos
  have hZ0_diff_eq : Z0_unq - Z0_exact = Z0_exact * ((D - D_q) / D_q) := by
    dsimp only [Z0_unq, Z0_exact]
    field_simp [hD_ne, hDq_ne]
  have hdiv_Dq : ‖(D - D_q) / D_q‖ ≤ (2.5 : ℝ) * ((t1 : ℝ) * complexQuantizeMaxErr q) := by
    rw [norm_div, div_le_iff₀ hDq_pos]
    nlinarith
  have hZ0_unq_err :
      ‖Z0_unq - Z0_exact‖ ≤
        (2.5 : ℝ) * ((t1 : ℝ) * complexQuantizeMaxErr q) * ‖Z0_exact‖ := by
    rw [hZ0_diff_eq, norm_mul]
    calc ‖Z0_exact‖ * ‖(D - D_q) / D_q‖
        ≤ ‖Z0_exact‖ * ((2.5 : ℝ) * ((t1 : ℝ) * complexQuantizeMaxErr q)) :=
          mul_le_mul_of_nonneg_left hdiv_Dq (norm_nonneg _)
      _ = (2.5 : ℝ) * ((t1 : ℝ) * complexQuantizeMaxErr q) * ‖Z0_exact‖ := by ring
  have hZ0_err :
      ‖Z0 - Z0_exact‖ ≤
        complexQuantizeMaxErr q +
          (2.5 : ℝ) * ((t1 : ℝ) * complexQuantizeMaxErr q) * ‖Z0_exact‖ := by
    have hsplit : Z0 - Z0_exact = (Z0 - Z0_unq) + (Z0_unq - Z0_exact) := by ring
    rw [hsplit]
    have htri := norm_add_le (Z0 - Z0_unq) (Z0_unq - Z0_exact)
    have hq := norm_complexQuantize_sub_le q Z0_unq
    linarith
  have hu1_le : (u1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast hu1.le
  have hhom_u1_err :
      ‖zHomFwdQuantized q c0 c1 u1 - zHomFwd c0 c1 u1‖ ≤
        (t1 : ℝ) * complexQuantizeMaxErr q :=
    (norm_zHomFwdQuantized_sub_le q c0 c1 hc0_pos hc10 u1).trans
      (mul_le_mul_of_nonneg_right hu1_le hq_nonneg)
  have hhom_u1_norm : ‖zHomFwdQuantized q c0 c1 u1‖ ≤ (1.001 : ℝ) := by
    have h1 := norm_zHomFwdQuantized_le q c0 c1 hc0_pos hc10 u1
    have h2 : (u1 : ℝ) * complexQuantizeMaxErr q ≤ (t1 : ℝ) * complexQuantizeMaxErr q :=
      mul_le_mul_of_nonneg_right hu1_le hq_nonneg
    linarith
  set w_unq := zPartFwd c0 c1 Y_eff u1 + Z0 * zHomFwdQuantized q c0 c1 u1
  have hw_split :
      complexQuantize q w_unq -
        (zPartFwd c0 c1 Y_eff u1 + Z0_exact * zHomFwd c0 c1 u1) =
      (complexQuantize q w_unq - w_unq) +
        ((Z0 - Z0_exact) * zHomFwdQuantized q c0 c1 u1 +
          Z0_exact * (zHomFwdQuantized q c0 c1 u1 - zHomFwd c0 c1 u1)) := by
    dsimp only [w_unq]
    ring
  rw [hw_split]
  have hw_q : ‖complexQuantize q w_unq - w_unq‖ ≤ complexQuantizeMaxErr q :=
    norm_complexQuantize_sub_le q w_unq
  have hterm1 :
      ‖(Z0 - Z0_exact) * zHomFwdQuantized q c0 c1 u1‖ ≤
        (1.001 : ℝ) *
          (complexQuantizeMaxErr q +
            (2.5 : ℝ) * ((t1 : ℝ) * complexQuantizeMaxErr q) * ‖Z0_exact‖) := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul hhom_u1_norm hZ0_err (norm_nonneg _) (by positivity)
  have hterm2 :
      ‖Z0_exact * (zHomFwdQuantized q c0 c1 u1 - zHomFwd c0 c1 u1)‖ ≤
        ((t1 : ℝ) * complexQuantizeMaxErr q) * ‖Z0_exact‖ := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hhom_u1_err (norm_nonneg _)
  have htri1 := norm_add_le (complexQuantize q w_unq - w_unq)
    ((Z0 - Z0_exact) * zHomFwdQuantized q c0 c1 u1 +
      Z0_exact * (zHomFwdQuantized q c0 c1 u1 - zHomFwd c0 c1 u1))
  have htri2 := norm_add_le
    ((Z0 - Z0_exact) * zHomFwdQuantized q c0 c1 u1)
    (Z0_exact * (zHomFwdQuantized q c0 c1 u1 - zHomFwd c0 c1 u1))
  have hZ0_nonneg : 0 ≤ ‖Z0_exact‖ := norm_nonneg _
  have hZ0_rhs : zPartFwd c0 c1 Y_eff 0 + Z0_exact * zHomFwd c0 c1 0 = Z0_exact := by
    have hz0_part : zPartFwd c0 c1 Y_eff 0 = 0 := rfl
    have hz0_hom : zHomFwd c0 c1 0 = 1 := rfl
    rw [hz0_part, hz0_hom]
    ring
  rw [hZ0_rhs]
  nlinarith

/-- Reversal equivalence for `zPartBwdQuantized`: equals `zPartFwdQuantized` with `(c0, c1)` swapped
and right-hand side `bwdRevRHS t1 Y`. -/
theorem zPartBwdQuantized_eq_zPartFwdQuantized_rev
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (d : ℕ) :
    zPartBwdQuantized q t1 c0 c1 Y d = zPartFwdQuantized q c1 c0 (bwdRevRHS t1 Y) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [zPartBwdQuantized, zPartFwdQuantized]
    rw [ih]
    unfold bwdRevRHS
    rw [if_neg (Nat.succ_ne_zero d)]
    have hsub : t1 - 1 - d = t1 - (d + 1) := by omega
    rw [hsub]

/-- Reversal equivalence for `solveBidiagonalBwdQuantized`: equals `solveBidiagonalFwdQuantized`
with `(c0, c1)` swapped and right-hand side `bwdRevRHS t1 Y` at `t1 - 1 - u1`. -/
theorem solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) :
    solveBidiagonalBwdQuantized q t1 c0 c1 Y u1 =
      solveBidiagonalFwdQuantized q t1 c1 c0 (bwdRevRHS t1 Y) (t1 - 1 - u1) := by
  unfold solveBidiagonalBwdQuantized solveBidiagonalFwdQuantized zHomBwdQuantized
  dsimp only
  rw [zPartBwdQuantized_eq_zPartFwdQuantized_rev q t1 c0 c1 Y (t1 - 1 - u1),
      zPartBwdQuantized_eq_zPartFwdQuantized_rev q t1 c0 c1 Y (t1 - 1)]
  rfl

/-- Backward-error effective right-hand side `zPartNyqEffRHS` for `zPartNyqQuantized`:
satisfies `zPartNyqQuantized q c0 Y u1 = zPartNyq c0 (zPartNyqEffRHS q c0 Y) u1` identically
whenever `c0 ≠ 0`. -/
noncomputable def zPartNyqEffRHS (q : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) : ℕ → ℂ
  | 0 => Y 0
  | u1 + 1 => c0 * (zPartNyqQuantized q c0 Y (u1 + 1) + zPartNyqQuantized q c0 Y u1)

/-- Exact backward-error representation of `zPartNyqQuantized` as an exact `zPartNyq` sweep on
`zPartNyqEffRHS`. -/
theorem zPartNyqQuantized_eq_zPartNyq_effRHS
    (q : ℕ) (c0 : ℂ) (hc0 : c0 ≠ 0) (Y : ℕ → ℂ) (u1 : ℕ) :
    zPartNyqQuantized q c0 Y u1 = zPartNyq c0 (zPartNyqEffRHS q c0 Y) u1 := by
  induction u1 with
  | zero => rfl
  | succ u1 ih =>
    rw [zPartNyq_succ, ← ih]
    dsimp only [zPartNyqEffRHS]
    field_simp [hc0]
    ring

/-- Pointwise backward-error bound for `zPartNyqEffRHS`: when `c0 ≠ 0` and `‖c0‖ ≤ 1`,
every entry `k` satisfies `‖zPartNyqEffRHS q c0 Y k - Y k‖ ≤ complexQuantizeMaxErr q`. -/
theorem norm_zPartNyqEffRHS_sub_le
    (q : ℕ) (c0 : ℂ) (hc0 : c0 ≠ 0) (hc0_le : ‖c0‖ ≤ 1) (Y : ℕ → ℂ) (k : ℕ) :
    ‖zPartNyqEffRHS q c0 Y k - Y k‖ ≤ complexQuantizeMaxErr q := by
  cases k with
  | zero =>
    simp only [zPartNyqEffRHS, sub_self, norm_zero]
    unfold complexQuantizeMaxErr
    positivity
  | succ u1 =>
    dsimp only [zPartNyqEffRHS, zPartNyqQuantized]
    set step_unq := Y (u1 + 1) / c0 - zPartNyqQuantized q c0 Y u1
    have hident :
        c0 * (complexQuantize q step_unq + zPartNyqQuantized q c0 Y u1) - Y (u1 + 1) =
          c0 * (complexQuantize q step_unq - step_unq) := by
      dsimp only [step_unq]
      field_simp [hc0]
      ring
    rw [hident, norm_mul]
    calc ‖c0‖ * ‖complexQuantize q step_unq - step_unq‖
        ≤ 1 * complexQuantizeMaxErr q :=
          mul_le_mul hc0_le (norm_complexQuantize_sub_le q step_unq) (norm_nonneg _) zero_le_one
      _ = complexQuantizeMaxErr q := one_mul _

/-- Difference between `solveNyquistQuantized` and the exact `solveNyquist` on `zPartNyqEffRHS`
is at most `2 * complexQuantizeMaxErr q` when `c0 ≠ 0`. -/
theorem norm_solveNyquistQuantized_sub_effRHS_le
    (q t1 : ℕ) (c0 : ℂ) (hc0 : c0 ≠ 0) (Y : ℕ → ℂ) (alt_q : ℂ) (u1 : ℕ) :
    ‖solveNyquistQuantized q t1 c0 Y alt_q u1 -
        solveNyquist t1 c0 (zPartNyqEffRHS q c0 Y) alt_q u1‖ ≤
      2 * complexQuantizeMaxErr q := by
  unfold solveNyquistQuantized solveNyquist
  dsimp only
  have hsum :
      (∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyqQuantized q c0 Y v) =
      ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 (zPartNyqEffRHS q c0 Y) v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [zPartNyqQuantized_eq_zPartNyq_effRHS q c0 hc0 Y v]
  rw [hsum, zPartNyqQuantized_eq_zPartNyq_effRHS q c0 hc0 Y u1]
  set diff_unq := (alt_q - ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyq c0 (zPartNyqEffRHS q c0 Y) v) / (t1 : ℂ)
  set w_unq := zPartNyq c0 (zPartNyqEffRHS q c0 Y) u1 + (-1 : ℂ) ^ u1 * complexQuantize q diff_unq
  have hsplit :
      complexQuantize q w_unq -
        (zPartNyq c0 (zPartNyqEffRHS q c0 Y) u1 + (-1 : ℂ) ^ u1 * diff_unq) =
      (complexQuantize q w_unq - w_unq) +
        (-1 : ℂ) ^ u1 * (complexQuantize q diff_unq - diff_unq) := by
    dsimp only [w_unq]
    ring
  rw [hsplit]
  have h1 : ‖complexQuantize q w_unq - w_unq‖ ≤ complexQuantizeMaxErr q :=
    norm_complexQuantize_sub_le q w_unq
  have h2 : ‖(-1 : ℂ) ^ u1 * (complexQuantize q diff_unq - diff_unq)‖ ≤ complexQuantizeMaxErr q := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact norm_complexQuantize_sub_le q diff_unq
  have htri := norm_add_le (complexQuantize q w_unq - w_unq)
    ((-1 : ℂ) ^ u1 * (complexQuantize q diff_unq - diff_unq))
  linarith

/-- Cyclic forward bidiagonal perturbation bound under quantized conditioning parameters
(`0.4999 ≤ M ≤ ‖c0‖`, `‖c1‖ ≤ ‖c0‖`, `(‖c1‖ / ‖c0‖) ^ t1 ≤ ratio_t1 ≤ 0.1501`). -/
theorem solveBidiagonalFwd_cyclic_error_bound_relaxed
    (t1 : ℕ) (ht1 : 0 < t1) (c0 c1 : ℂ) (Y Y' : ℕ → ℂ) (M ratio_t1 ε : ℝ)
    (hM : (0.4999 : ℝ) ≤ M) (hc0 : M ≤ ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖)
    (hratio : (‖c1‖ / ‖c0‖) ^ t1 ≤ ratio_t1) (hratio_le : ratio_t1 ≤ (0.1501 : ℝ))
    (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε) (u1 : ℕ) (hu1 : u1 < t1) :
    ‖solveBidiagonalFwd t1 c0 c1 Y' u1 - solveBidiagonalFwd t1 c0 c1 Y u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε := by
  have hM_pos : 0 < M := by linarith
  have hc0_pos : 0 < ‖c0‖ := lt_of_lt_of_le hM_pos hc0
  have hdenom_cond : (0.424 : ℝ) < M * (1 - ratio_t1) := by nlinarith
  have hpos_cond : (0 : ℝ) < M * (1 - ratio_t1) := by linarith
  have hinv_cond : 1 / (M * (1 - ratio_t1)) < (2.36 : ℝ) := by
    rw [div_lt_iff₀ hpos_cond]
    nlinarith
  have h1m_pos : 0 ≤ 1 - ratio_t1 := by linarith
  have htail_eq : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ = ‖c0‖ * (‖c1‖ / ‖c0‖) ^ t1 := by
    unfold zHomFwd
    rw [norm_mul, norm_pow, norm_div, norm_neg]
    have ht1_eq : t1 = (t1 - 1) + 1 := by omega
    conv_rhs => rw [ht1_eq, pow_succ]
    field_simp [hc0_pos.ne']
  have htail_le : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ ≤ ‖c0‖ * ratio_t1 := by
    rw [htail_eq]
    exact mul_le_mul_of_nonneg_left hratio hc0_pos.le
  have hdenom_ge_c0 : ‖c0‖ * (1 - ratio_t1) ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ := by
    have htri : ‖c0‖ ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ + ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ := by
      have hsub : c0 = (c0 + c1 * zHomFwd c0 c1 (t1 - 1)) - c1 * zHomFwd c0 c1 (t1 - 1) := by ring
      conv_lhs => rw [hsub]
      exact norm_sub_le _ _
    linarith
  have hdenom_ge_M : M * (1 - ratio_t1) ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ :=
    (mul_le_mul_of_nonneg_right hc0 h1m_pos).trans hdenom_ge_c0
  have hdenom_pos : 0 < ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ := by linarith
  have hdenom_ne : c0 + c1 * zHomFwd c0 c1 (t1 - 1) ≠ 0 := norm_pos_iff.mp hdenom_pos
  rw [solveBidiagonalFwd_sub]
  have hprod_le := norm_denom_mul_solveBidiagonalFwd_le t1 c0 c1 hc0_pos hc10 hdenom_ne
    (fun k => Y' k - Y k) ε hε hY u1 hu1
  rw [norm_mul] at hprod_le
  have hdiv_le : ‖solveBidiagonalFwd t1 c0 c1 (fun k => Y' k - Y k) u1‖ ≤
      ((t1 : ℝ) * ε) / (M * (1 - ratio_t1)) := by
    have h1 : ‖solveBidiagonalFwd t1 c0 c1 (fun k => Y' k - Y k) u1‖ ≤
        ((t1 : ℝ) * ε) / ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ :=
      (le_div_iff₀' hdenom_pos).mpr hprod_le
    exact h1.trans (div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg t1) hε) hpos_cond hdenom_ge_M)
  have hrew : ((t1 : ℝ) * ε) / (M * (1 - ratio_t1)) =
      (1 / (M * (1 - ratio_t1))) * ((t1 : ℝ) * ε) := by ring
  rw [hrew] at hdiv_le
  calc ‖solveBidiagonalFwd t1 c0 c1 (fun k => Y' k - Y k) u1‖
      ≤ (1 / (M * (1 - ratio_t1))) * ((t1 : ℝ) * ε) := hdiv_le
    _ ≤ (2.36 : ℝ) * ((t1 : ℝ) * ε) :=
        mul_le_mul_of_nonneg_right hinv_cond.le (mul_nonneg (Nat.cast_nonneg t1) hε)
    _ = (2.36 : ℝ) * (t1 : ℝ) * ε := by ring

/-- Nyquist column perturbation bound under quantized conditioning parameter `0.4999 ≤ M ≤ ‖c0‖`. -/
theorem solveNyquist_error_bound_relaxed
    (t1 : ℕ) (ht1 : 0 < t1) (c0 : ℂ) (Y Y' : ℕ → ℂ) (alt alt' : ℂ)
    (M ε ε_alt : ℝ) (hM : (0.4999 : ℝ) ≤ M) (hc0 : M ≤ ‖c0‖)
    (hε : 0 ≤ ε) (hY : ∀ k : ℕ, ‖Y' k - Y k‖ ≤ ε)
    (halt : ‖alt' - alt‖ ≤ ε_alt) (u1 : ℕ) (hu1 : u1 < t1) :
    ‖solveNyquist t1 c0 Y' alt' u1 - solveNyquist t1 c0 Y alt u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε + ε_alt / (t1 : ℝ) := by
  have hM_pos : 0 < M := by linarith
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr ht1
  rw [solveNyquist_sub_eq t1 ht1 c0 Y Y' alt alt' u1,
      norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have htri := norm_add_le ((alt' - alt) / (t1 : ℂ))
    ((1 / (t1 : ℂ)) * ∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v))
  have ht_alt : ‖(alt' - alt) / (t1 : ℂ)‖ ≤ ε_alt / (t1 : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right halt ht1_pos.le
  have hsum_norm :
      ‖∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)‖ ≤
        (t1 : ℝ) * ((t1 : ℝ) * (ε / M)) := by
    calc ‖∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)‖
        ≤ ∑ v ∈ Finset.range t1, ‖nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _v ∈ Finset.range t1, (t1 : ℝ) * (ε / M) :=
          Finset.sum_le_sum fun v hv =>
            norm_nyqSignedDiff_sub_le_of_lt t1 c0 Y Y' M ε u1 v hu1 (Finset.mem_range.mp hv)
              hM_pos hc0 hε hY
      _ = (t1 : ℝ) * ((t1 : ℝ) * (ε / M)) := by simp [Finset.sum_const, nsmul_eq_mul]
  have ht_sum :
      ‖(1 / (t1 : ℂ)) * ∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)‖ ≤
        (t1 : ℝ) * (ε / M) := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    calc (1 / (t1 : ℝ)) * ‖∑ v ∈ Finset.range t1, (nyqSignedDiff c0 Y Y' u1 - nyqSignedDiff c0 Y Y' v)‖
        ≤ (1 / (t1 : ℝ)) * ((t1 : ℝ) * ((t1 : ℝ) * (ε / M))) :=
          mul_le_mul_of_nonneg_left hsum_norm (div_nonneg zero_le_one ht1_pos.le)
      _ = (t1 : ℝ) * (ε / M) := by field_simp [ht1_pos.ne']
  have hM_inv : 1 / M ≤ (2.36 : ℝ) := by
    rw [div_le_iff₀ hM_pos]
    linarith
  have ht_sum' : (t1 : ℝ) * (ε / M) ≤ (2.36 : ℝ) * (t1 : ℝ) * ε := by
    have hrew : (t1 : ℝ) * (ε / M) = (1 / M) * ((t1 : ℝ) * ε) := by ring
    rw [hrew]
    calc (1 / M) * ((t1 : ℝ) * ε)
        ≤ (2.36 : ℝ) * ((t1 : ℝ) * ε) :=
          mul_le_mul_of_nonneg_right hM_inv (mul_nonneg ht1_pos.le hε)
      _ = (2.36 : ℝ) * (t1 : ℝ) * ε := by ring
  linarith

/-- Non-vanishing of the cyclic bidiagonal denominator when `0 < M ≤ ‖c0‖`, `(‖c1‖ / ‖c0‖)^t1 ≤ ratio_t1`,
and `0.424 < M * (1 - ratio_t1)`. -/
theorem denom_ne_zero_of_relaxed
    (t1 : ℕ) (c0 c1 : ℂ) (M ratio_t1 : ℝ)
    (hM : (0.4999 : ℝ) ≤ M) (hc0 : M ≤ ‖c0‖)
    (hratio : (‖c1‖ / ‖c0‖) ^ t1 ≤ ratio_t1) (hratio_le : ratio_t1 ≤ (0.1501 : ℝ)) :
    c0 + c1 * zHomFwd c0 c1 (t1 - 1) ≠ 0 := by
  rcases Nat.eq_zero_or_pos t1 with rfl | ht1
  · simp only [pow_zero] at hratio
    linarith
  have hM_pos : 0 < M := by linarith
  have hc0_pos : 0 < ‖c0‖ := lt_of_lt_of_le hM_pos hc0
  have h1m_pos : 0 ≤ 1 - ratio_t1 := by linarith
  have htail_eq : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ = ‖c0‖ * (‖c1‖ / ‖c0‖) ^ t1 := by
    unfold zHomFwd
    rw [norm_mul, norm_pow, norm_div, norm_neg]
    have ht1_eq : t1 = (t1 - 1) + 1 := by omega
    conv_rhs => rw [ht1_eq, pow_succ]
    field_simp [hc0_pos.ne']
  have htail_le : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ ≤ ‖c0‖ * ratio_t1 := by
    rw [htail_eq]
    exact mul_le_mul_of_nonneg_left hratio hc0_pos.le
  have hdenom_ge_c0 : ‖c0‖ * (1 - ratio_t1) ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ := by
    have htri : ‖c0‖ ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ + ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ := by
      have hsub : c0 = (c0 + c1 * zHomFwd c0 c1 (t1 - 1)) - c1 * zHomFwd c0 c1 (t1 - 1) := by ring
      conv_lhs => rw [hsub]
      exact norm_sub_le _ _
    linarith
  have hdenom_ge_M : M * (1 - ratio_t1) ≤ ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ :=
    (mul_le_mul_of_nonneg_right hc0 h1m_pos).trans hdenom_ge_c0
  have hdenom_pos : 0 < ‖c0 + c1 * zHomFwd c0 c1 (t1 - 1)‖ := by nlinarith
  exact norm_pos_iff.mp hdenom_pos

/-- **`[MS]` Lemma 5.2 (Combined Step-Rounded Forward Bidiagonal Solver Error Bound, §5.2, eq. (26), Term D)**:
Composes the step-by-step recurrence rounding of `zPartFwdQuantized`, the step-by-step homogeneous
power rounding of `zHomFwdQuantized`, the boundary quotient rounding `Z0`, and the final combine
rounding in `solveBidiagonalFwdQuantized` against the exact `solveBidiagonalFwd` on `Y`. -/
theorem theorem3_step_rounded_fwd_total_error_le
    (q t1 : ℕ) (ht1 : 0 < t1) (c0 c1 : ℂ)
    (hc0_ge : (0.4999 : ℝ) ≤ ‖c0‖) (hc0_le : ‖c0‖ ≤ 1)
    (hc10 : ‖c1‖ ≤ ‖c0‖) (hratio : (‖c1‖ / ‖c0‖) ^ t1 ≤ (0.1501 : ℝ))
    (ht1_err : (t1 : ℝ) * complexQuantizeMaxErr q ≤ (0.001 : ℝ))
    (Y : ℕ → ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    ‖solveBidiagonalFwdQuantized q t1 c0 c1 Y u1 - solveBidiagonalFwd t1 c0 c1 Y u1‖ ≤
      (2.001 : ℝ) * complexQuantizeMaxErr q +
        4 * ((t1 : ℝ) * complexQuantizeMaxErr q) *
          ‖solveBidiagonalFwd t1 c0 c1 (zPartFwdEffRHS q c0 c1 Y) 0‖ +
        (2.36 : ℝ) * (t1 : ℝ) * complexQuantizeMaxErr q := by
  have hc0_pos : 0 < ‖c0‖ := by linarith
  have hc0 : c0 ≠ 0 := norm_pos_iff.mp hc0_pos
  have hq_nonneg : 0 ≤ complexQuantizeMaxErr q := by unfold complexQuantizeMaxErr; positivity
  have h1 := norm_solveBidiagonalFwdQuantized_sub_effRHS_le q t1 ht1 c0 c1
    hc0_ge hc0_le hc10 hratio ht1_err Y u1 hu1
  have h2 := solveBidiagonalFwd_cyclic_error_bound_relaxed t1 ht1 c0 c1 Y
    (zPartFwdEffRHS q c0 c1 Y) (0.4999 : ℝ) (0.1501 : ℝ) (complexQuantizeMaxErr q)
    le_rfl hc0_ge hc10 hratio le_rfl hq_nonneg
    (fun k => norm_zPartFwdEffRHS_sub_le q c0 c1 hc0 hc0_le Y k) u1 hu1
  have hsplit :
      solveBidiagonalFwdQuantized q t1 c0 c1 Y u1 - solveBidiagonalFwd t1 c0 c1 Y u1 =
        (solveBidiagonalFwdQuantized q t1 c0 c1 Y u1 -
          solveBidiagonalFwd t1 c0 c1 (zPartFwdEffRHS q c0 c1 Y) u1) +
        (solveBidiagonalFwd t1 c0 c1 (zPartFwdEffRHS q c0 c1 Y) u1 -
          solveBidiagonalFwd t1 c0 c1 Y u1) := by ring
  rw [hsplit]
  have htri := norm_add_le
    (solveBidiagonalFwdQuantized q t1 c0 c1 Y u1 -
      solveBidiagonalFwd t1 c0 c1 (zPartFwdEffRHS q c0 c1 Y) u1)
    (solveBidiagonalFwd t1 c0 c1 (zPartFwdEffRHS q c0 c1 Y) u1 -
      solveBidiagonalFwd t1 c0 c1 Y u1)
  linarith

/-- **Unconditional Spatial Window Rules (`h_win`, `h_step`) at `m_1 = 2 * pChild p K` (`[MS]` §6.1, Lemma 6.1)**:
For all `p, K : ℕ`, at `α = alphaSchedule (pWork p K)` and `m1 = 2 * pChild p K`,
`8 ≤ m1`, `(pChild p K : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2`, and
`(1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2`. -/
theorem lemma2_spatial_window_rules_two_mul_pChild (p K : ℕ) :
    let α := alphaSchedule (pWork p K)
    let m1 := 2 * pChild p K
    0 < α ∧ 8 ≤ m1 ∧
      (pChild p K : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2 ∧
      (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2 := by
  dsimp only
  set p_work := pWork p K
  set p_child := pChild p K
  set α := alphaSchedule p_work
  set m1 := 2 * p_child
  have hp_work_pos : 0 < p_work := by unfold p_work pWork; omega
  have hp_child_ge12 : 12 ≤ p_child := by unfold p_child pChild pWork; omega
  have hm1_ge8 : 8 ≤ m1 := by omega
  have hα : 0 < α := alphaSchedule_pos p_work hp_work_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi_gt : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_lt : Real.log 2 < (1 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hpi_alpha_sq : Real.pi * α ^ 2 = 4 * (p_work : ℝ) * Real.log 2 :=
    pi_mul_alphaSchedule_sq p_work hp_work_pos
  have hp_le : (p_work : ℝ) ≤ (p_child : ℝ) := by
    exact_mod_cast (by unfold p_work p_child pChild; omega : p_work ≤ p_child)
  have hm1_cast : (m1 : ℝ) = 2 * (p_child : ℝ) := by
    dsimp [m1]
    push_cast
    ring
  have hα_sq_le : α ^ 2 ≤ 4 * (p_child : ℝ) := by
    have h1 : Real.pi * α ^ 2 ≤ Real.pi * (4 * (p_child : ℝ)) := by
      rw [hpi_alpha_sq]
      nlinarith
    exact le_of_mul_le_mul_left h1 hpi
  have h_win : (p_child : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hα), hm1_cast]
    have h_log_alpha : Real.log 2 * α ^ 2 ≤ 4 * (p_child : ℝ) := by
      nlinarith [sq_nonneg α]
    have h1 : (p_child : ℝ) * Real.log 2 * α ^ 2 ≤ (p_child : ℝ) * (4 * (p_child : ℝ)) := by
      calc (p_child : ℝ) * Real.log 2 * α ^ 2
          = (p_child : ℝ) * (Real.log 2 * α ^ 2) := by ring
        _ ≤ (p_child : ℝ) * (4 * (p_child : ℝ)) :=
            mul_le_mul_of_nonneg_left h_log_alpha (Nat.cast_nonneg p_child)
    have h2 : (p_child : ℝ) * (4 * (p_child : ℝ)) ≤ Real.pi * (2 * (p_child : ℝ)) ^ 2 := by
      calc (p_child : ℝ) * (4 * (p_child : ℝ))
          = 1 * (2 * (p_child : ℝ)) ^ 2 := by ring
        _ ≤ Real.pi * (2 * (p_child : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    exact h1.trans h2
  have h_step : (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hα), hm1_cast]
    have hp_nonneg : (0 : ℝ) ≤ (p_child : ℝ) := Nat.cast_nonneg p_child
    nlinarith
  exact ⟨hα, hm1_ge8, h_win, h_step⟩

/-- **Unconditional Spatial Window Rules (`h_win`, `h_step`) at Tighter Half-Width `m_1 = pChild p K` (`[MS]` §6.1, Lemma 6.1)**:
For all `p, K : ℕ`, at `α = alphaSchedule (pWork p K)` and `m1 = pChild p K`,
`8 ≤ m1`, `(pChild p K : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2`, and
`(1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2`. -/
theorem lemma2_spatial_window_rules_pChild (p K : ℕ) :
    let α := alphaSchedule (pWork p K)
    let m1 := pChild p K
    0 < α ∧ 8 ≤ m1 ∧
      (pChild p K : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2 ∧
      (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2 := by
  dsimp only
  set p_work := pWork p K
  set p_child := pChild p K
  set α := alphaSchedule p_work
  set m1 := p_child
  have hp_work_pos : 0 < p_work := by unfold p_work pWork; omega
  have hp_child_ge12 : 12 ≤ p_child := by unfold p_child pChild pWork; omega
  have hm1_ge8 : 8 ≤ m1 := by omega
  have hα : 0 < α := alphaSchedule_pos p_work hp_work_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi_gt : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_lt : Real.log 2 < (0.7 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hpi_alpha_sq : Real.pi * α ^ 2 = 4 * (p_work : ℝ) * Real.log 2 :=
    pi_mul_alphaSchedule_sq p_work hp_work_pos
  have hp_le : (p_work : ℝ) ≤ (p_child : ℝ) := by
    exact_mod_cast (by unfold p_work p_child pChild; omega : p_work ≤ p_child)
  have hp_work_nonneg : (0 : ℝ) ≤ (p_work : ℝ) := Nat.cast_nonneg p_work
  have hp_child_nonneg : (0 : ℝ) ≤ (p_child : ℝ) := Nat.cast_nonneg p_child
  have h_win : (p_child : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hα)]
    have h1 : Real.pi * ((p_child : ℝ) * Real.log 2 * α ^ 2) =
        ((4 : ℝ) * (Real.log 2) ^ 2) * ((p_child : ℝ) * (p_work : ℝ)) := by
      calc Real.pi * ((p_child : ℝ) * Real.log 2 * α ^ 2)
          = (p_child : ℝ) * Real.log 2 * (Real.pi * α ^ 2) := by ring
        _ = (p_child : ℝ) * Real.log 2 * (4 * (p_work : ℝ) * Real.log 2) := by rw [hpi_alpha_sq]
        _ = ((4 : ℝ) * (Real.log 2) ^ 2) * ((p_child : ℝ) * (p_work : ℝ)) := by ring
    have hlog_sq : (4 : ℝ) * (Real.log 2) ^ 2 ≤ Real.pi * Real.pi := by nlinarith
    have hp_prod : (p_child : ℝ) * (p_work : ℝ) ≤ (p_child : ℝ) ^ 2 := by nlinarith
    have h2 : ((4 : ℝ) * (Real.log 2) ^ 2) * ((p_child : ℝ) * (p_work : ℝ)) ≤
        Real.pi * (Real.pi * (m1 : ℝ) ^ 2) := by
      dsimp [m1]
      calc ((4 : ℝ) * (Real.log 2) ^ 2) * ((p_child : ℝ) * (p_work : ℝ))
          ≤ (Real.pi * Real.pi) * (p_child : ℝ) ^ 2 :=
            mul_le_mul hlog_sq hp_prod (by positivity) (by positivity)
        _ = Real.pi * (Real.pi * (p_child : ℝ) ^ 2) := by ring
    exact le_of_mul_le_mul_left (h1.trans_le h2) hpi
  have hα_sq_le : α ^ 2 ≤ 4 * (p_child : ℝ) := by
    have h1 : Real.pi * α ^ 2 ≤ Real.pi * (4 * (p_child : ℝ)) := by
      rw [hpi_alpha_sq]
      nlinarith
    exact le_of_mul_le_mul_left h1 hpi
  have h_step : (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hα)]
    dsimp [m1]
    nlinarith
  exact ⟨hα, hm1_ge8, h_win, h_step⟩

/-- **Direct Child-DFT Error Amplification Bound (`2.36 * t_1 * 2^{-p_child} * r * M < 0.037 * 2^{-p} * M`, `[MS]` §6.3, Lemma 6.5)**:
For `2 ≤ K`, `0 < M`, and `t1 * r = 2 ^ K`, since `pChild p K = p + 2 * K + 12`,
`(t1 * r) * 2^{-pChild p K} = 2^{-(p + K + 12)} ≤ 2^{-11} * 2^{-p}`,
and therefore `2.36 * t1 * (2^{-pChild p K} * (r * M)) < 0.037 * 2^{-p} * M`. -/
theorem lemma2_child_amplification_error_bound
    (p K t1 r : ℕ) (M : ℝ) (hK : 2 ≤ K) (hM : 0 < M) (hsize : t1 * r = 2 ^ K) :
    (2.36 : ℝ) * (t1 : ℝ) * ((2 : ℝ) ^ (-(pChild p K : ℤ)) * ((r : ℝ) * M)) <
      (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hsize_real : (t1 : ℝ) * (r : ℝ) = (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast hsize
  have hzpow_eq :
      (t1 : ℝ) * (r : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) =
        (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 12)) := by
    rw [hsize_real, pChild_eq_additive p K, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  have hzpow_le :
      (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 12)) ≤
        (2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 12))
        ≤ (2 : ℝ) ^ ((-11 : ℤ) + (-(p : ℤ))) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = (2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) :=
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (-11 : ℤ) (-(p : ℤ))
  have h1 :
      (2.36 : ℝ) * (t1 : ℝ) * ((2 : ℝ) ^ (-(pChild p K : ℤ)) * ((r : ℝ) * M)) =
        ((2.36 : ℝ) * ((t1 : ℝ) * (r : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)))) * M := by ring
  have h2 :
      (2.36 : ℝ) * ((t1 : ℝ) * (r : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ))) <
        (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [hzpow_eq]
    calc (2.36 : ℝ) * (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 12))
        ≤ (2.36 : ℝ) * ((2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ))) :=
          mul_le_mul_of_nonneg_left hzpow_le (by norm_num)
      _ = ((2.36 : ℝ) * (2 : ℝ) ^ (-11 : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) := by ring
      _ < (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) :=
          mul_lt_mul_of_pos_right lemma2_numerical_constants.2.1 (zpow_pos (by norm_num) _)
  rw [h1]
  exact mul_lt_mul_of_pos_right h2 hM

/-- **Direct Windowed B1 + B2 + B3 + Child-DFT + Solver Error Amplification Bound (`2.36 * t_1 * (0.63 * 2^{-p_child} * M + 2^{-p_child} * ((r + 1) * M)) < 0.036 * 2^{-p} * M`, `[MS]` §6.1, Lemma 6.1 & §6.3, Lemma 6.5)**:
For `2 ≤ K`, `0 < r`, `0 < M`, and `t1 * r = 2 ^ K`, since `t1 ≤ 2 ^ K` and `pChild p K = p + 2 * K + 12`,
`t1 * (r + 1.63) ≤ 2.63 * 2 ^ K ≤ 8 * 2 ^ K = 2 ^ (K + 3)`, so
`t1 * (r + 1.63) * 2^{-pChild p K} ≤ 2^{-(p + K + 9)} ≤ 2^{-11} * 2^{-p}`,
and since `2.36 * 2^{-11} < 0.0012 < 0.036`,
`2.36 * t1 * ((0.6 * 2^{-pChild p K} * M + 2^{-pChild p K} * ((r + 1) * M)) + 0.03 * 2^{-pChild p K} * M) < 0.036 * 2^{-p} * M`. -/
theorem lemma2_windowed_child_and_solver_amplification_error_bound
    (p K t1 r : ℕ) (M : ℝ) (hK : 2 ≤ K) (hr : 0 < r) (hM : 0 < M) (hsize : t1 * r = 2 ^ K) :
    (2.36 : ℝ) * (t1 : ℝ) *
      (((0.6 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M +
        (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) +
        (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) <
      (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have ht1_le : (t1 : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    have hnat : t1 ≤ 2 ^ K := by
      rw [← hsize]
      exact Nat.le_mul_of_pos_right t1 hr
    exact_mod_cast hnat
  have hsize_real : (t1 : ℝ) * (r : ℝ) = (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast hsize
  have htr_le : (t1 : ℝ) * ((r : ℝ) + 1.63) ≤ (2 : ℝ) ^ ((K : ℤ) + 3) := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (K : ℤ) := zpow_pos (by norm_num) _
    have hpow_add : (2 : ℝ) ^ ((K : ℤ) + 3) = 8 * (2 : ℝ) ^ (K : ℤ) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring
    nlinarith
  have hzpow_eq :
      (2 : ℝ) ^ ((K : ℤ) + 3) * (2 : ℝ) ^ (-(pChild p K : ℤ)) =
        (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 9)) := by
    rw [pChild_eq_additive p K, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  have hzpow_le :
      (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 9)) ≤
        (2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 9))
        ≤ (2 : ℝ) ^ ((-11 : ℤ) + (-(p : ℤ))) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = (2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) :=
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (-11 : ℤ) (-(p : ℤ))
  have h1 :
      (2.36 : ℝ) * (t1 : ℝ) *
        (((0.6 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M +
          (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) +
          (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) =
      ((2.36 : ℝ) * (((t1 : ℝ) * ((r : ℝ) + 1.63)) * (2 : ℝ) ^ (-(pChild p K : ℤ)))) * M := by
    ring
  have h2 :
      (2.36 : ℝ) * (((t1 : ℝ) * ((r : ℝ) + 1.63)) * (2 : ℝ) ^ (-(pChild p K : ℤ))) <
        (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    have hle1 :
        ((t1 : ℝ) * ((r : ℝ) + 1.63)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤
          (2 : ℝ) ^ ((K : ℤ) + 3) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
      mul_le_mul_of_nonneg_right htr_le (by positivity)
    calc (2.36 : ℝ) * (((t1 : ℝ) * ((r : ℝ) + 1.63)) * (2 : ℝ) ^ (-(pChild p K : ℤ)))
        ≤ (2.36 : ℝ) * ((2 : ℝ) ^ ((K : ℤ) + 3) * (2 : ℝ) ^ (-(pChild p K : ℤ))) :=
          mul_le_mul_of_nonneg_left hle1 (by norm_num)
      _ = (2.36 : ℝ) * (2 : ℝ) ^ (-(p : ℤ) - ((K : ℤ) + 9)) := by rw [hzpow_eq]
      _ ≤ (2.36 : ℝ) * ((2 : ℝ) ^ (-11 : ℤ) * (2 : ℝ) ^ (-(p : ℤ))) :=
          mul_le_mul_of_nonneg_left hzpow_le (by norm_num)
      _ = ((2.36 : ℝ) * (2 : ℝ) ^ (-11 : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) := by ring
      _ < (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) :=
          mul_lt_mul_of_pos_right (by norm_num) (zpow_pos (by norm_num) _)
  rw [h1]
  exact mul_lt_mul_of_pos_right h2 hM

/-- **Direct Windowed B1 + B2 + B3 + Child-DFT Error Amplification Bound (`2.36 * t_1 * (0.6 * 2^{-p_child} * M + 2^{-p_child} * ((r + 1) * M)) < 0.036 * 2^{-p} * M`, `[MS]` §6.1, Lemma 6.1 & §6.3, Lemma 6.5)**: -/
theorem lemma2_windowed_child_amplification_error_bound
    (p K t1 r : ℕ) (M : ℝ) (hK : 2 ≤ K) (hr : 0 < r) (hM : 0 < M) (hsize : t1 * r = 2 ^ K) :
    (2.36 : ℝ) * (t1 : ℝ) *
      ((0.6 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M +
        (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) <
      (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have h := lemma2_windowed_child_and_solver_amplification_error_bound p K t1 r M hK hr hM hsize
  have hpos : 0 ≤ (2.36 : ℝ) * (t1 : ℝ) * ((0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) := by
    positivity
  linarith

/-- **`[MS]` Lemma 6.5 (Unconditional Concrete Precision-Schedule Closure for All `p ≥ 8`, `K ≥ 2`, `t1 * r = 2 ^ K` — Zero `hW` or `h_sub` Hypotheses, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
Because the pre-folded overlap-add filter and `r`-periodic spatial array have effective width
`W_eff = effectiveFilterWidth m1 r ≤ r` and `‖U_win(j1, k2)‖ ≤ (r + 1) * M` regardless of how large
`m1 = 2 * pChild p K` (or `m1 = pChild p K`) is relative to `r`, the four error sources (Term A,
Term B1 spatial truncation tail, Terms B2/B3/D rounding, and Term C child-DFT error) close
unconditionally for **all** `p ≥ 8`, `K ≥ 2`, `0 < r`, `t1 * r = 2 ^ K` with **zero `hW` or `h_sub`
hypotheses**:
`err_BCD < 0.036 * 2^{-p} * M`, `err_A + err_BCD + err_quant < 0.394 * 2^{-p} * M`, and
`err_A + err_BCD + err_quant < 2^{-p} * M`. -/
theorem lemma2_precision_schedule_closure
    (p K t1 r m1 : ℕ)
    (δ M err_A err_B1 err_B2 err_B3 err_C err_D err_BCD err_quant : ℝ)
    (hK : 2 ≤ K) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (hM : 0 < M) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hm1 : m1 = 2 * pChild p K ∨ m1 = pChild p K)
    (hA : err_A ≤ (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M)
    (hB1 : err_B1 ≤
      ((∑' k : ℕ, |sincGaussian (alphaSchedule (pWork p K)) ((m1 + 1 + k : ℝ) - δ)|) +
        (∑' k : ℕ, |sincGaussian (alphaSchedule (pWork p K)) (-((m1 + 1 + k : ℝ)) - δ)|)) * M)
    (hB2 : err_B2 ≤ (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hB3 : err_B3 ≤ (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hC : err_C ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M))
    (hD : err_D ≤ (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hBCD_amp : err_BCD ≤ (2.36 : ℝ) * (t1 : ℝ) * (err_B1 + err_B2 + err_B3 + err_C + err_D))
    (hQ : err_quant ≤ complexQuantizeMaxErr p * M) :
    err_BCD < (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hrules :
      0 < alphaSchedule (pWork p K) ∧ 8 ≤ m1 ∧
        (pChild p K : ℝ) * Real.log 2 ≤
          Real.pi * (m1 : ℝ) ^ 2 / (alphaSchedule (pWork p K)) ^ 2 ∧
        (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / (alphaSchedule (pWork p K)) ^ 2 := by
    rcases hm1 with rfl | rfl
    · exact lemma2_spatial_window_rules_two_mul_pChild p K
    · exact lemma2_spatial_window_rules_pChild p K
  rcases hrules with ⟨hα, hm1_ge8, h_win, h_step⟩
  have hB1_lt : err_B1 < (0.4 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    have htail := (lemma2_sincGaussian_spatial_tail_bound
      (alphaSchedule (pWork p K)) δ m1 (pChild p K) hα hδ0 hδ1 hm1_ge8 h_win h_step).2
    exact hB1.trans_lt (mul_lt_mul_of_pos_right htail hM)
  have hsum_le :
      err_B1 + err_B2 + err_B3 + err_C + err_D ≤
        ((0.6 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M +
          (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) +
          (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    linarith
  have h236_t1_nonneg : (0 : ℝ) ≤ (2.36 : ℝ) * (t1 : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg t1)
  have hBCD_lt : err_BCD < (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hmul := mul_le_mul_of_nonneg_left hsum_le h236_t1_nonneg
    have hamp := lemma2_windowed_child_and_solver_amplification_error_bound
      p K t1 r M hK hr hM hsize
    linarith
  have hBCD_le_037 : err_BCD ≤ (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M :=
      mul_pos (zpow_pos (by norm_num) _) hM
    linarith
  have hclosure := lemma2_inductive_error_closure p M err_A err_BCD err_quant hM hA hBCD_le_037 hQ
  exact ⟨hBCD_lt, hclosure.1, hclosure.2⟩

/-- **Unconditional Concrete Windowed-Spread Closure (`lemma2_windowed_sincGaussian_concrete_closure`, `[MS]` §6.1, Lemma 6.1 & §6.3, Lemma 6.5)**:
Instantiates Term B1 directly as the actual 2D DFT spatial-truncation error
`‖dft2D t1 r (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x) u1 u2 - dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) u1 u2‖`
(discharged unconditionally via `norm_dft2D_windowedSincGaussianSpreadArray_sub_le` with **zero `hB1` hypothesis**). -/
theorem lemma2_windowed_sincGaussian_concrete_closure
    (p K t1 r u1 u2 : ℕ) (x : ℕ → ℂ)
    (M err_A err_B2 err_B3 err_C err_D err_BCD err_quant : ℝ)
    (hK : 2 ≤ K) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (hM : 0 < M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (hA : err_A ≤ (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M)
    (hB2 : err_B2 ≤ (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hB3 : err_B3 ≤ (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hC : err_C ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M))
    (hD : err_D ≤ (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hBCD_amp : err_BCD ≤ (2.36 : ℝ) * (t1 : ℝ) *
      (‖dft2D t1 r
          (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x) u1 u2 -
        dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) u1 u2‖ +
        err_B2 + err_B3 + err_C + err_D))
    (hQ : err_quant ≤ complexQuantizeMaxErr p * M) :
    err_BCD < (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hB1_le := norm_dft2D_windowedSincGaussianSpreadArray_sub_le p K t1 r ht1 hr x M hM hx u1 u2
  have hsum_le :
      ‖dft2D t1 r
          (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x) u1 u2 -
        dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) u1 u2‖ +
        err_B2 + err_B3 + err_C + err_D ≤
        ((0.6 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M +
          (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) +
          (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    linarith
  have h236_t1_nonneg : (0 : ℝ) ≤ (2.36 : ℝ) * (t1 : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg t1)
  have hBCD_lt : err_BCD < (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hmul := mul_le_mul_of_nonneg_left hsum_le h236_t1_nonneg
    have hamp := lemma2_windowed_child_and_solver_amplification_error_bound
      p K t1 r M hK hr hM hsize
    linarith
  have hBCD_le_037 : err_BCD ≤ (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M :=
      mul_pos (zpow_pos (by norm_num) _) hM
    linarith
  have hclosure := lemma2_inductive_error_closure p M err_A err_BCD err_quant hM hA hBCD_le_037 hQ
  exact ⟨hBCD_lt, hclosure.1, hclosure.2⟩

end IntMul
