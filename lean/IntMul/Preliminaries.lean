import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# [MS] Section 3: Preliminaries, Computation Model, Fixed-Point Arithmetic, Normalized DFTs, and Lemma 3.5

This module is part of our independent formalization of `[MS]` Section 3
(companion manuscript `[MS]`, *Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*):

1. **Fixed-Point Complex Arithmetic (`[MS]` §3.2, Definition 3.1, eq. (4))**:
   - Grid spacing `2^{-(p+2)}` for precision parameter `p`.
   - Real quantization error bound `≤ 0.125 * 2^{-p}`.
   - Complex quantization error bound `(√2 / 4) * 2^{-p} < 0.354 * 2^{-p}`.
2. **Normalized 1D and 2D Discrete Fourier Transforms & 2-Call Real Convolution (`[MS]` §3.5, eqs. (9)–(11), Lemma 3.4)**:
   - Standard additive-to-multiplicative character `e(x) = exp(2π i x)`.
   - Normalized 1D DFT `dft1D` and proof of `ℓ_∞` contractivity `‖F_R x‖_∞ ≤ ‖x‖_∞`.
   - Normalized 2D DFT `dft2D`.
   - 2-Call Real Convolution algebraic identity: packing `z = a + i b` satisfies
     `(a + i b)^2 = (a^2 - b^2) + 2 i a b` and recovers `a ⊛ b` via
     `-(R^2 / 2) * Im(F_R(conj((F_R(a + i b))^2)))`.
3. **Polynomial Transform (`Synthetic FFT`) over `R_r = ℂ[y]/(y^r + 1)` and `[MS]` Lemma 3.5 (§3.5, eqs. (12)–(13))**:
   - Negacyclic monomial multiplication `y^s` in `ℂ[y]/(y^r + 1)` via cyclic shift + sign negation.
   - Synthetic FFT `G_{t_1}` (`syntheticDFT`) over `R_r`.
   - **`[MS]` Lemma 3.5**: Butterfly error non-amplification `|(a' ± b')/2 - (a ± b)/2| ≤ max(|a'-a|, |b'-b|)`
     and multi-stage rounding bound `k_1 * (√2 / 4) * 2^{-p} ≤ 0.18 * K * 2^{-p}` for `k_1 ≤ K / 2`.
-/

namespace IntMul

open scoped BigOperators
open Complex Real

/-! ## 1. Fixed-Point Real and Complex Quantization Bounds (`[MS]` §3.2, Definition 3.1) -/

/-- Worst-case real quantization error when rounding to `p + 2` fractional bits:
`(1/2) * 2^{-(p+2)}`. -/
noncomputable def realQuantizeMaxErr (p : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (2 : ℝ) ^ (-(p + 2 : ℤ))

/-- Worst-case complex (`ℓ_2`) quantization error at `p + 2` fractional bits (`(√2 / 4) * 2^{-p}`
for 1-ulp coordinate bound, and `(√2 / 8) * 2^{-p}` for nearest-integer `1/2`-ulp rounding). -/
noncomputable def complexQuantizeMaxErr (p : ℕ) : ℝ :=
  Real.sqrt 2 * (2 : ℝ) ^ (-(p + 2 : ℤ))

noncomputable def complexNearestQuantizeMaxErr (p : ℕ) : ℝ :=
  (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(p + 2 : ℤ))

/-- Helper: `2^{-(p + 2 : ℤ)} = (1 / 4) * 2^{-(p : ℤ)}`. -/
theorem two_zpow_neg_add_two (p : ℕ) :
    (2 : ℝ) ^ (-(p + 2 : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have h1 : (-(p + 2 : ℤ)) = (-2 : ℤ) + (-(p : ℤ)) := by omega
  rw [h1, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h2 : (2 : ℝ) ^ (-2 : ℤ) = (1 / 4 : ℝ) := by norm_num
  rw [h2]

/-- Real quantization to `p + 2` fractional bits has error `(1/8) * 2^{-p} = 0.125 * 2^{-p}`. -/
theorem realQuantizeMaxErr_eq (p : ℕ) :
    realQuantizeMaxErr p = (0.125 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  unfold realQuantizeMaxErr
  rw [two_zpow_neg_add_two]
  ring

/-- Complex quantization to `p + 2` fractional bits has error `(√2 / 4) * 2^{-p}`. -/
theorem complexQuantizeMaxErr_eq (p : ℕ) :
    complexQuantizeMaxErr p = (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) := by
  unfold complexQuantizeMaxErr
  rw [two_zpow_neg_add_two]
  ring

/-- Nearest-grid complex quantization to `p + 2` fractional bits has error `(√2 / 8) * 2^{-p} ≤ complexQuantizeMaxErr p`. -/
theorem complexNearestQuantizeMaxErr_eq (p : ℕ) :
    complexNearestQuantizeMaxErr p = (Real.sqrt 2 / 8) * (2 : ℝ) ^ (-(p : ℤ)) := by
  unfold complexNearestQuantizeMaxErr
  rw [two_zpow_neg_add_two]
  ring

/-- Rational upper bound on `√2`: `√2 < 1.416` (since `1.416^2 = 2.005056 > 2`). -/
theorem sqrt_two_lt_1416 : Real.sqrt 2 < (1.416 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- Complex quantization error at `p + 2` fractional bits is strictly bounded by `0.354 * 2^{-p}`. -/
theorem complexQuantizeMaxErr_lt (p : ℕ) :
    complexQuantizeMaxErr p < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  rw [complexQuantizeMaxErr_eq]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hsqrt : Real.sqrt 2 / 4 < (0.354 : ℝ) := by linarith [sqrt_two_lt_1416]
  exact mul_lt_mul_of_pos_right hsqrt hpow

/-- If both real and imaginary rounding errors are at most `δ ≥ 0`, the complex Euclidean error
is at most `√2 * δ`. -/
theorem complex_rounding_norm_le (e_re e_im δ : ℝ) (hδ : 0 ≤ δ)
    (hre : |e_re| ≤ δ) (him : |e_im| ≤ δ) :
    Real.sqrt (e_re ^ 2 + e_im ^ 2) ≤ Real.sqrt 2 * δ := by
  have hre2 : e_re ^ 2 ≤ δ ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hδ])
  have him2 : e_im ^ 2 ≤ δ ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hδ])
  have hsum : e_re ^ 2 + e_im ^ 2 ≤ (Real.sqrt 2 * δ) ^ 2 := by
    calc e_re ^ 2 + e_im ^ 2 ≤ δ ^ 2 + δ ^ 2 := add_le_add hre2 him2
      _ = 2 * δ ^ 2 := by ring
      _ = (Real.sqrt 2) ^ 2 * δ ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
      _ = (Real.sqrt 2 * δ) ^ 2 := by ring
  have hpos : 0 ≤ Real.sqrt 2 * δ := mul_nonneg (Real.sqrt_nonneg 2) hδ
  exact (Real.sqrt_le_sqrt hsum).trans_eq (Real.sqrt_sq hpos)

/-! ## 2. Standard Exponential Character `e(x) = exp(2π i x)` and Normalized 1D/2D DFTs (`[MS]` §3.5) -/

/-- The standard unit-circle character `e(x) = exp(2π i x) = exp((2π x) * I)`. -/
noncomputable def stdChar (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

@[simp]
theorem stdChar_zero : stdChar 0 = 1 := by
  simp [stdChar]

theorem stdChar_add (x y : ℝ) : stdChar (x + y) = stdChar x * stdChar y := by
  unfold stdChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdChar_sub (x y : ℝ) : stdChar (x - y) = stdChar x * stdChar (-y) := by
  rw [sub_eq_add_neg, stdChar_add]

theorem stdChar_neg (x : ℝ) : stdChar (-x) = (stdChar x)⁻¹ := by
  unfold stdChar
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem norm_stdChar (x : ℝ) : ‖stdChar x‖ = 1 := by
  unfold stdChar
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

theorem stdChar_int (k : ℤ) : stdChar (k : ℝ) = 1 := by
  unfold stdChar
  have h : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem stdChar_add_int (x : ℝ) (k : ℤ) : stdChar (x + (k : ℝ)) = stdChar x := by
  rw [stdChar_add, stdChar_int, mul_one]

/-- Normalized 1D Discrete Fourier Transform (`[MS]` §3.5):
`(F_R x)_u = (1 / R) * ∑_{j=0}^{R-1} x_j * exp(2π i j u / R)`. -/
noncomputable def dft1D (R : ℕ) (x : ℕ → ℂ) (u : ℕ) : ℂ :=
  (1 / (R : ℂ)) * ∑ j ∈ Finset.range R, x j * stdChar (((j * u : ℕ) : ℝ) / (R : ℝ))

/-- Normalized 2D Discrete Fourier Transform (`[MS]` §3.5):
`(F_{t_1, r} U)_{u_1, u_2} = (1 / (t_1 r)) * ∑_{j_1=0}^{t_1-1} ∑_{j_2=0}^{r-1}
  U_{j_1, j_2} exp(2π i j_1 u_1 / t_1) exp(2π i j_2 u_2 / r)`. -/
noncomputable def dft2D (t1 r : ℕ) (U : ℕ → ℕ → ℂ) (u1 u2 : ℕ) : ℂ :=
  (1 / ((t1 * r : ℕ) : ℂ)) *
    ∑ j1 ∈ Finset.range t1, ∑ j2 ∈ Finset.range r,
      U j1 j2 * stdChar (((j1 * u1 : ℕ) : ℝ) / (t1 : ℝ)) *
        stdChar (((j2 * u2 : ℕ) : ℝ) / (r : ℝ))

/-- `ℓ_∞` contractivity of the normalized 1D DFT (`[MS]` §3.5):
If `‖x j‖ ≤ M` for all `j < R` (with `R > 0`), then `‖(F_R x)_u‖ ≤ M`. -/
theorem dft1D_norm_le (R : ℕ) (hR : 0 < R) (x : ℕ → ℂ) (M : ℝ)
    (hx : ∀ j ∈ Finset.range R, ‖x j‖ ≤ M) (u : ℕ) :
    ‖dft1D R x u‖ ≤ M := by
  unfold dft1D
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr hR
  have hsum : ‖∑ j ∈ Finset.range R, x j * stdChar (((j * u : ℕ) : ℝ) / (R : ℝ))‖ ≤
      (R : ℝ) * M := by
    calc ‖∑ j ∈ Finset.range R, x j * stdChar (((j * u : ℕ) : ℝ) / (R : ℝ))‖
        ≤ ∑ j ∈ Finset.range R, ‖x j * stdChar (((j * u : ℕ) : ℝ) / (R : ℝ))‖ :=
          norm_sum_le _ _
      _ = ∑ j ∈ Finset.range R, ‖x j‖ := by
           refine Finset.sum_congr rfl fun j _ => ?_
           rw [norm_mul, norm_stdChar, mul_one]
      _ ≤ ∑ _j ∈ Finset.range R, M := Finset.sum_le_sum hx
      _ = (R : ℝ) * M := by simp [Finset.sum_const, nsmul_eq_mul]
  calc (1 / (R : ℝ)) * ‖∑ j ∈ Finset.range R, x j * stdChar (((j * u : ℕ) : ℝ) / (R : ℝ))‖
      ≤ (1 / (R : ℝ)) * ((R : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = M := by field_simp [hR_pos.ne']

/-- Linearity of `dft1D` for complex packing `z = a + i b`. -/
theorem dft1D_complex_pack (R : ℕ) (a b : ℕ → ℂ) (u : ℕ) :
    dft1D R (fun j => a j + Complex.I * b j) u =
      dft1D R a u + Complex.I * dft1D R b u := by
  unfold dft1D
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- Algebraic identity underlying the 2-call real convolution (`[MS]` §3.5):
`(FA + i FB)^2 = (FA^2 - FB^2) + 2 i FA FB`. -/
theorem two_call_square_identity (FA FB : ℂ) :
    (FA + Complex.I * FB) ^ 2 = (FA ^ 2 - FB ^ 2) + 2 * Complex.I * (FA * FB) := by
  calc (FA + Complex.I * FB) ^ 2
      = FA ^ 2 + 2 * Complex.I * (FA * FB) + Complex.I ^ 2 * FB ^ 2 := by ring
    _ = (FA ^ 2 - FB ^ 2) + 2 * Complex.I * (FA * FB) := by
      rw [Complex.I_sq]
      ring

/-- Extracting the real convolution product from the imaginary part of the conjugate-inverse
transform in `[MS]` §3.5 (Lemma 3.4, eq. (10)): if the unnormalized conjugate-DFT of `conj((F_R(a + i b))^2)` equals
`conj(((a ⊛ a - b ⊛ b) + 2 i (a ⊛ b)) / R^2)`, then scaling the imaginary part by `-R^2 / 2`
recovers `a ⊛ b` exactly. -/
theorem two_call_real_conv_recovery (R : ℝ) (hR : R ≠ 0) (conv_diff conv_ab : ℝ) :
    -(R ^ 2 / 2) *
      (((conv_diff / R ^ 2 : ℝ) : ℂ) - Complex.I * ((2 * conv_ab / R ^ 2 : ℝ) : ℂ)).im =
      conv_ab := by
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, zero_mul,
    Complex.I_im, Complex.ofReal_re, one_mul, zero_add, zero_sub]
  field_simp [hR]

/-! ## 3. Polynomial Transform (`Synthetic FFT`) over `R_r = ℂ[y]/(y^r + 1)` and `[MS]` Lemma 3.5 (§3.5) -/

/-- Negacyclic monomial multiplication by `y^s` in `R_r = ℂ[y]/(y^r + 1)` (`[MS]` §3.5):
Given `B : ℕ → ℂ` representing `∑_{k_2=0}^{r-1} B_{k_2} y^{k_2}`, the `k_2`-th coefficient
of `y^s B(y) mod (y^r + 1)` is obtained by a cyclic shift with sign flip on wrap-around.
This requires **zero complex multiplications**. -/
def negacyclicShift (r s : ℕ) (B : ℕ → ℂ) (k2 : ℕ) : ℂ :=
  let src := (k2 + 2 * r - s % (2 * r)) % (2 * r)
  if src < r then B src else -B (src - r)

/-- One radix-2 Synthetic FFT butterfly step `(A(y) ± y^s B(y)) / 2 mod (y^r + 1)` (`[MS]` §3.5, Lemma 3.5). -/
noncomputable def syntheticButterflyAdd (r s : ℕ) (A B : ℕ → ℂ) (k2 : ℕ) : ℂ :=
  (A k2 + negacyclicShift r s B k2) / 2

noncomputable def syntheticButterflySub (r s : ℕ) (A B : ℕ → ℂ) (k2 : ℕ) : ℂ :=
  (A k2 - negacyclicShift r s B k2) / 2

/-- Single-step negacyclic shift `B(y) ↦ y B(y) mod (y^r + 1)` over `ℂ`:
coefficient `0` receives `-B(r - 1)` and coefficient `k_2 + 1` receives `B(k_2)`. -/
def negacyclicShiftStep (r : ℕ) (B : ℕ → ℂ) (k2 : ℕ) : ℂ :=
  if k2 = 0 then -B (r - 1) else B (k2 - 1)

/-- `s`-step iterated negacyclic shift `B(y) ↦ y^s B(y) mod (y^r + 1)` over `ℂ`,
computed by `s` applications of `negacyclicShiftStep r` (zero multiplications). -/
def negacyclicShiftIter (r s : ℕ) (B : ℕ → ℂ) : ℕ → ℂ :=
  (negacyclicShiftStep r)^[s] B

/-- Evaluating `negacyclicShiftStep r B` at any `ξ : ℂ` with `ξ^r = -1` multiplies the
polynomial evaluation `∑_{k_2 < r} B(k_2) ξ^{k_2}` by `ξ`. -/
theorem negacyclicShiftStep_eval (r : ℕ) (hr : 0 < r) (B : ℕ → ℂ) (ξ : ℂ) (hξ : ξ ^ r = -1) :
    (∑ k2 ∈ Finset.range r, negacyclicShiftStep r B k2 * ξ ^ k2) =
      ξ * ∑ k2 ∈ Finset.range r, B k2 * ξ ^ k2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [Finset.sum_range_succ' (fun k2 => negacyclicShiftStep (m + 1) B k2 * ξ ^ k2)]
  simp only [negacyclicShiftStep, ↓reduceIte, Nat.add_sub_cancel, Nat.add_eq_zero,
    one_ne_zero, and_false, pow_zero, mul_one]
  rw [Finset.sum_range_succ (fun k2 => B k2 * ξ ^ k2), mul_add, Finset.mul_sum]
  have hsum : ∑ k ∈ Finset.range m, B k * ξ ^ (k + 1) =
      ∑ x ∈ Finset.range m, ξ * (B x * ξ ^ x) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ']
    ring
  have hlast : -B m = ξ * (B m * ξ ^ m) := by
    calc -B m = B m * (-1) := by ring
      _ = B m * ξ ^ (m + 1) := by rw [← hξ]
      _ = ξ * (B m * ξ ^ m) := by rw [pow_succ']; ring
  rw [hsum, hlast]

/-- **Negacyclic Shift Evaluation Homomorphism**:
For any `r > 0`, shift `s ∈ ℕ`, and `ξ ∈ ℂ` satisfying `ξ^r = -1`, evaluating the `s`-step
addition/sign-flip shift `negacyclicShiftIter r s B` at `ξ` equals `ξ^s` times the evaluation of `B`. -/
theorem negacyclicShiftIter_eval (r s : ℕ) (hr : 0 < r) (B : ℕ → ℂ) (ξ : ℂ) (hξ : ξ ^ r = -1) :
    (∑ k2 ∈ Finset.range r, negacyclicShiftIter r s B k2 * ξ ^ k2) =
      ξ ^ s * ∑ k2 ∈ Finset.range r, B k2 * ξ ^ k2 := by
  induction s generalizing B with
  | zero =>
    simp [negacyclicShiftIter]
  | succ s ih =>
    simp only [negacyclicShiftIter, Function.iterate_succ_apply'] at ih ⊢
    rw [negacyclicShiftStep_eval r hr _ ξ hξ, ih, pow_succ']
    ring

/-- 1D Synthetic FFT `G_{t_1}` over `R_r = ℂ[y]/(y^r + 1)` (`[MS]` §3.5):
`(G_{t_1} P)_{v_1}(y) = (1 / t_1) ∑_{j_1=0}^{t_1-1} P_{j_1}(y) y^{2 c_1 j_1 v_1} mod (y^r + 1)`. -/
noncomputable def syntheticDFT (t1 r : ℕ) (P : ℕ → ℕ → ℂ) (v1 k2 : ℕ) : ℂ :=
  (1 / (t1 : ℂ)) * ∑ j1 ∈ Finset.range t1,
    negacyclicShiftIter r (2 * (r / t1) * j1 * v1) (P j1) k2

/-- **`[MS]` Lemma 3.5 (Part 1: Non-amplification of previous-stage errors in a radix-2 butterfly, §3.5)**:
If inputs `a', b'` have errors `‖a' - a‖ ≤ ε_in` and `‖b' - b‖ ≤ ε_in`, then the exact
butterfly average `(a' ± b') / 2` has error at most `ε_in`. -/
theorem butterfly_error_non_amplification (a a' b b' : ℂ) (ε_in : ℝ)
    (ha : ‖a' - a‖ ≤ ε_in) (hb : ‖b' - b‖ ≤ ε_in) :
    ‖(a' + b') / 2 - (a + b) / 2‖ ≤ ε_in ∧
    ‖(a' - b') / 2 - (a - b) / 2‖ ≤ ε_in := by
  constructor
  · have h1 : (a' + b') / 2 - (a + b) / 2 = ((a' - a) + (b' - b)) / 2 := by ring
    rw [h1, norm_div, RCLike.norm_ofNat]
    have h2 : ‖(a' - a) + (b' - b)‖ ≤ ε_in + ε_in := (norm_add_le _ _).trans (add_le_add ha hb)
    linarith
  · have h1 : (a' - b') / 2 - (a - b) / 2 = ((a' - a) - (b' - b)) / 2 := by ring
    rw [h1, norm_div, RCLike.norm_ofNat]
    have h2 : ‖(a' - a) - (b' - b)‖ ≤ ε_in + ε_in := (norm_sub_le _ _).trans (add_le_add ha hb)
    linarith

/-- **`[MS]` Lemma 3.5 (Part 2: Per-stage rounding accumulation across `k_1 = ⌊K / 2⌋` stages, §3.5)**:
At precision `q = p + 2`, each of the `k_1 ≤ K / 2` stages of `G_{t_1}` adds at most
`complexQuantizeMaxErr p = (√2 / 4) * 2^{-p}` error, so the total `ℓ_∞` rounding error across all
`k_1` stages is at most `(k_1 : ℝ) * complexQuantizeMaxErr p ≤ 0.18 * K * 2^{-p}`. -/
theorem lemma1_synthetic_fft_rounding_bound (K k1 p : ℕ) (hk1 : 2 * k1 ≤ K) :
    (k1 : ℝ) * complexQuantizeMaxErr p ≤ (0.18 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  rw [complexQuantizeMaxErr_eq]
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(p : ℤ)) := zpow_nonneg (by norm_num) _
  have hk1_real : (k1 : ℝ) ≤ (K : ℝ) / 2 := by
    have : (2 : ℝ) * (k1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk1
    linarith
  have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hcoeff : (k1 : ℝ) * (Real.sqrt 2 / 4) ≤ (0.18 : ℝ) * (K : ℝ) := by
    calc (k1 : ℝ) * (Real.sqrt 2 / 4)
        ≤ ((K : ℝ) / 2) * (Real.sqrt 2 / 4) :=
          mul_le_mul_of_nonneg_right hk1_real (by positivity)
      _ = (Real.sqrt 2 / 8) * (K : ℝ) := by ring
      _ ≤ (0.18 : ℝ) * (K : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hK_nonneg
          linarith [sqrt_two_lt_1416]
  calc (k1 : ℝ) * ((Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)))
      = ((k1 : ℝ) * (Real.sqrt 2 / 4)) * (2 : ℝ) ^ (-(p : ℤ)) := by ring
    _ ≤ ((0.18 : ℝ) * (K : ℝ)) * (2 : ℝ) ^ (-(p : ℤ)) :=
        mul_le_mul_of_nonneg_right hcoeff hpow

/-- Nearest-grid complex quantization error at `p + 2` fractional bits is strictly bounded by
`(√2 / 8) * 2^{-p} < 0.177 * 2^{-p}` (`[MS]` §3.2, Definition 3.1, eq. (4)). -/
theorem complexNearestQuantizeMaxErr_lt (p : ℕ) :
    complexNearestQuantizeMaxErr p < (0.177 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  rw [complexNearestQuantizeMaxErr_eq]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hsqrt : Real.sqrt 2 / 8 < (0.177 : ℝ) := by linarith [sqrt_two_lt_1416]
  exact mul_lt_mul_of_pos_right hsqrt hpow

/-- **`[MS]` Lemma 3.5 (Nearest-Grid Multi-Stage Rounding Bound, §3.5, eq. (13))**:
Under nearest-grid rounding (`complexNearestQuantizeMaxErr p = (√2 / 8) * 2^{-p}`), `k_1 ≤ K / 2`
stages accumulate at most `(k_1 : ℝ) * complexNearestQuantizeMaxErr p ≤ 0.09 * K * 2^{-p}`. -/
theorem lemma1_synthetic_fft_nearest_rounding_bound (K k1 p : ℕ) (hk1 : 2 * k1 ≤ K) :
    (k1 : ℝ) * complexNearestQuantizeMaxErr p ≤ (0.09 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  rw [complexNearestQuantizeMaxErr_eq]
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(p : ℤ)) := zpow_nonneg (by norm_num) _
  have hk1_real : (k1 : ℝ) ≤ (K : ℝ) / 2 := by
    have : (2 : ℝ) * (k1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk1
    linarith
  have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hcoeff : (k1 : ℝ) * (Real.sqrt 2 / 8) ≤ (0.09 : ℝ) * (K : ℝ) := by
    calc (k1 : ℝ) * (Real.sqrt 2 / 8)
        ≤ ((K : ℝ) / 2) * (Real.sqrt 2 / 8) :=
          mul_le_mul_of_nonneg_right hk1_real (by positivity)
      _ = (Real.sqrt 2 / 16) * (K : ℝ) := by ring
      _ ≤ (0.09 : ℝ) * (K : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hK_nonneg
          linarith [sqrt_two_lt_1416]
  calc (k1 : ℝ) * ((Real.sqrt 2 / 8) * (2 : ℝ) ^ (-(p : ℤ)))
      = ((k1 : ℝ) * (Real.sqrt 2 / 8)) * (2 : ℝ) ^ (-(p : ℤ)) := by ring
    _ ≤ ((0.09 : ℝ) * (K : ℝ)) * (2 : ℝ) ^ (-(p : ℤ)) :=
        mul_le_mul_of_nonneg_right hcoeff hpow

/-- Concrete nearest-grid fixed-point real quantization operator at `q = p + 2` fractional bits (`[MS]` §3.2, Definition 3.1, eq. (4)):
rounds `x` to the nearest integer multiple of `2^{-(p + 2)}`. -/
noncomputable def realQuantize (p : ℕ) (x : ℝ) : ℝ :=
  (⌊x * (2 : ℝ) ^ (p + 2) + (1 / 2 : ℝ)⌋ : ℝ) * (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ))

/-- Concrete nearest-grid fixed-point complex quantization operator at `q = p + 2` fractional bits (`[MS]` §3.2, Definition 3.1, eq. (4)):
quantizes the real and imaginary parts independently via `realQuantize p`. -/
noncomputable def complexQuantize (p : ℕ) (z : ℂ) : ℂ :=
  ⟨realQuantize p z.re, realQuantize p z.im⟩

/-- **Concrete Real Quantization Error Bound (`[MS]` §3.2, Definition 3.1, eq. (4))**:
For any precision parameter `p : ℕ` and any `x : ℝ`, rounding `x` to the nearest multiple of
`2^{-(p+2)}` via `realQuantize p x` has absolute error at most
`realQuantizeMaxErr p = (1 / 2) * 2^{-(p + 2)}`. -/
theorem abs_realQuantize_sub_le (p : ℕ) (x : ℝ) :
    |realQuantize p x - x| ≤ realQuantizeMaxErr p := by
  unfold realQuantize realQuantizeMaxErr
  set scale : ℝ := (2 : ℝ) ^ (p + 2)
  set inv_scale : ℝ := (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ))
  have h_inv_pos : 0 < inv_scale := zpow_pos (by norm_num) _
  have h_mul : scale * inv_scale = 1 := by
    dsimp [scale, inv_scale]
    rw [← zpow_natCast (2 : ℝ) (p + 2), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast
    rw [add_neg_cancel, zpow_zero]
  have h_diff : (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) * inv_scale - x =
      ((⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) - x * scale) * inv_scale := by
    calc (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) * inv_scale - x
        = (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) * inv_scale - x * (scale * inv_scale) := by
          rw [h_mul, mul_one]
      _ = ((⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) - x * scale) * inv_scale := by ring
  rw [h_diff, abs_mul, abs_of_pos h_inv_pos]
  have h_floor_le : (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) ≤ x * scale + (1 / 2 : ℝ) :=
    Int.floor_le (x * scale + (1 / 2 : ℝ))
  have h_lt_floor : x * scale + (1 / 2 : ℝ) - 1 < (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) :=
    Int.sub_one_lt_floor (x * scale + (1 / 2 : ℝ))
  have h_abs_u : |(⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) - x * scale| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_mul_of_nonneg_right h_abs_u h_inv_pos.le

/-- **Concrete Nearest-Grid Complex Quantization Error Bound (`[MS]` §3.2, Definition 3.1, eq. (4))**:
For any precision parameter `p : ℕ` and any `z : ℂ`, `complexQuantize p z` satisfies
`‖complexQuantize p z - z‖ ≤ complexNearestQuantizeMaxErr p = (√2 / 2) * 2^{-(p+2)}`. -/
theorem norm_complexQuantize_sub_le_nearest (p : ℕ) (z : ℂ) :
    ‖complexQuantize p z - z‖ ≤ complexNearestQuantizeMaxErr p := by
  have hnorm : ‖complexQuantize p z - z‖ =
      Real.sqrt ((complexQuantize p z - z).re ^ 2 + (complexQuantize p z - z).im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    ring_nf
  have hre : (complexQuantize p z - z).re = realQuantize p z.re - z.re := rfl
  have him : (complexQuantize p z - z).im = realQuantize p z.im - z.im := rfl
  rw [hnorm, hre, him]
  have hδ : 0 ≤ realQuantizeMaxErr p := by
    unfold realQuantizeMaxErr
    positivity
  have hbound := complex_rounding_norm_le
    (realQuantize p z.re - z.re)
    (realQuantize p z.im - z.im)
    (realQuantizeMaxErr p) hδ
    (abs_realQuantize_sub_le p z.re)
    (abs_realQuantize_sub_le p z.im)
  have heq : Real.sqrt 2 * realQuantizeMaxErr p = complexNearestQuantizeMaxErr p := by
    unfold realQuantizeMaxErr complexNearestQuantizeMaxErr
    ring
  rwa [heq] at hbound

/-- **Concrete Complex Quantization Error Bound (`norm_complexQuantize_sub_le`, `[MS]` §3.2, Definition 3.1, eq. (4))**:
For any precision parameter `p : ℕ` and any `z : ℂ`, `complexQuantize p z` satisfies
`‖complexQuantize p z - z‖ ≤ complexQuantizeMaxErr p = √2 * 2^{-(p+2)}`. -/
theorem norm_complexQuantize_sub_le (p : ℕ) (z : ℂ) :
    ‖complexQuantize p z - z‖ ≤ complexQuantizeMaxErr p := by
  refine (norm_complexQuantize_sub_le_nearest p z).trans ?_
  unfold complexNearestQuantizeMaxErr complexQuantizeMaxErr
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(p + 2 : ℤ)) := zpow_nonneg (by norm_num) _
  have hsqrt : Real.sqrt 2 / 2 ≤ Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
  exact mul_le_mul_of_nonneg_right hsqrt hpow

/-- `negacyclicShiftStep` preserves `ℓ_∞` bounds on `0 .. r - 1`. -/
theorem norm_negacyclicShiftStep_le (r : ℕ) (hr : 0 < r) (B : ℕ → ℂ) (M : ℝ)
    (hB : ∀ k2 < r, ‖B k2‖ ≤ M) (k2 : ℕ) (hk2 : k2 < r) :
    ‖negacyclicShiftStep r B k2‖ ≤ M := by
  unfold negacyclicShiftStep
  split_ifs with hk0
  · rw [norm_neg]
    exact hB (r - 1) (Nat.sub_lt hr zero_lt_one)
  · exact hB (k2 - 1) (by omega)

/-- `negacyclicShiftIter` preserves `ℓ_∞` bounds on `0 .. r - 1`. -/
theorem norm_negacyclicShiftIter_le (r s : ℕ) (hr : 0 < r) (B : ℕ → ℂ) (M : ℝ)
    (hB : ∀ k2 < r, ‖B k2‖ ≤ M) (k2 : ℕ) (hk2 : k2 < r) :
    ‖negacyclicShiftIter r s B k2‖ ≤ M := by
  induction s generalizing B k2 with
  | zero => exact hB k2 hk2
  | succ s ih =>
    simp only [negacyclicShiftIter, Function.iterate_succ_apply']
    exact norm_negacyclicShiftStep_le r hr _ M (fun m hm => ih B hB m hm) k2 hk2

/-- `syntheticDFT` is `ℓ_∞`-contractive on `0 .. r - 1`. -/
theorem norm_syntheticDFT_le (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (P : ℕ → ℕ → ℂ) (M : ℝ) (hP : ∀ j1 < t1, ∀ k2 < r, ‖P j1 k2‖ ≤ M)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    ‖syntheticDFT t1 r P v1 k2‖ ≤ M := by
  unfold syntheticDFT
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr ht1
  have hsum :
      ‖∑ j1 ∈ Finset.range t1, negacyclicShiftIter r (2 * (r / t1) * j1 * v1) (P j1) k2‖ ≤
        (t1 : ℝ) * M := by
    calc ‖∑ j1 ∈ Finset.range t1, negacyclicShiftIter r (2 * (r / t1) * j1 * v1) (P j1) k2‖
        ≤ ∑ j1 ∈ Finset.range t1,
            ‖negacyclicShiftIter r (2 * (r / t1) * j1 * v1) (P j1) k2‖ := norm_sum_le _ _
      _ ≤ ∑ _j1 ∈ Finset.range t1, M :=
          Finset.sum_le_sum fun j1 hj1 =>
            norm_negacyclicShiftIter_le r _ hr (P j1) M
              (hP j1 (Finset.mem_range.mp hj1)) k2 hk2
      _ = (t1 : ℝ) * M := by simp [Finset.sum_const, nsmul_eq_mul]
  calc (1 / (t1 : ℝ)) *
        ‖∑ j1 ∈ Finset.range t1, negacyclicShiftIter r (2 * (r / t1) * j1 * v1) (P j1) k2‖
      ≤ (1 / (t1 : ℝ)) * ((t1 : ℝ) * M) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = M := by field_simp [ht1_pos.ne']

/-- Linearity of `negacyclicShiftStep` with respect to subtraction. -/
theorem negacyclicShiftStep_sub (r : ℕ) (B1 B2 : ℕ → ℂ) (k2 : ℕ) :
    negacyclicShiftStep r B1 k2 - negacyclicShiftStep r B2 k2 =
      negacyclicShiftStep r (fun m => B1 m - B2 m) k2 := by
  unfold negacyclicShiftStep
  split_ifs <;> ring

/-- Linearity of `negacyclicShiftIter` with respect to subtraction. -/
theorem negacyclicShiftIter_sub (r s : ℕ) (B1 B2 : ℕ → ℂ) (k2 : ℕ) :
    negacyclicShiftIter r s B1 k2 - negacyclicShiftIter r s B2 k2 =
      negacyclicShiftIter r s (fun m => B1 m - B2 m) k2 := by
  induction s generalizing B1 B2 k2 with
  | zero => rfl
  | succ s ih =>
    simp only [negacyclicShiftIter, Function.iterate_succ_apply']
    rw [negacyclicShiftStep_sub]
    congr 1
    funext m
    exact ih B1 B2 m

/-- Linearity of `syntheticDFT` with respect to subtraction. -/
theorem syntheticDFT_sub (t1 r : ℕ) (P1 P2 : ℕ → ℕ → ℂ) (v1 k2 : ℕ) :
    syntheticDFT t1 r P1 v1 k2 - syntheticDFT t1 r P2 v1 k2 =
      syntheticDFT t1 r (fun j1 m => P1 j1 m - P2 j1 m) v1 k2 := by
  unfold syntheticDFT
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j1 _ => ?_
  exact negacyclicShiftIter_sub r (2 * (r / t1) * j1 * v1) (P1 j1) (P2 j1) k2

end IntMul
