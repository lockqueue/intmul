import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.KroneckerSpread
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# 2-Term Bidiagonal Output Deconvolution, Nyquist Identity & Inductive Accuracy (`IntMul.Deconvolution`)

This module formalizes the two-term cyclic bidiagonal and Nyquist column deconvolution solvers,
their finite-precision rounding bounds, the multi-level additive precision recurrence, and root
integer product recovery (see Section 5 (`sec:deconv`), Section 6.3 (`sec:forward-error`), and
Section 7 (`sec:main-proof`)):
1. **Theorem 5.1(1)–(2) (`thm:deconv`) (Section 5.1 (`sec:deconv-thm`))**: Passband/stopband bounds
   and the 2-term cyclic bidiagonal deconvolution linear system (both forward-shift
   `cyclicBidiagSolve` and backward-shift `cyclicBidiagPrevSolve`), exact algebraic inversion
   (`cyclicBidiagSolve_spec`, `cyclicBidiagPrevSolve_spec`), uniqueness (`cyclicBidiagSolve_of_spec`,
   `cyclicBidiagPrevSolve_of_spec`), $\ell_\infty$ condition number bounds
   (`vecInfNorm_cyclicBidiagSolve_le`, `deconvolution_conditioning_le_236_t1_of_bounds`,
   `deconvolution_prev_conditioning_le_236_t1_of_bounds`), and unconditional `gHat` conditioning
   theorems (`gHat_deconvolution_conditioning_le_236_t1`,
   `gHat_deconvolution_prev_conditioning_le_236_t1`).
2. **Theorem 5.1(3) (`thm:deconv`) and equation (25) (`eq:nyquist-id`) (Section 5.1 (`sec:deconv-thm`))**:
   Exact Nyquist mode $u_2 = r/2$ character orthogonality, alternating-sum cancellation
   (`nyquist_alternating_sum_eq`), and the open-chain particular solution + nullspace projection
   solver (`nyquistOpenChainParticular`, `nyquistColumnSolve`, `nyquistColumnSolve_spec`,
   `vecInfNorm_nyquistColumnSolve_le`).
3. **Quantized Step 3 Fixed-Point Deconvolution (Section 5.2 (`sec:solvers`) and Lemma 5.2 (`lem:solver-err`))**:
   Quantized cyclic bidiagonal solvers `cyclicBidiagSolveQuant`, `cyclicBidiagPrevSolveQuant`, and
   `nyquistColumnSolveQuant` with $q$-bit quantized passband weights, input column, and output entries,
   together with explicit $\ell_\infty$ approximation bounds relative to the exact solvers.
4. **Lemma 6.5(1)–(2) (`lem:forward`) and schedule (34) (`eq:cert-sched`) (Section 6.3 (`sec:forward-error`))**:
   Per-level four-source error budget combination (`level_error_budget_le`), base-case leaf accuracy
   (`base_leaf_error_budget_le`), and inductive accuracy closure across all recursion levels
   (`inductive_accuracy_closure`).
5. **Theorem 1 (`thm:main`) (Section 7.1 (`sec:alg-spec`) and Section 7.2 (`sec:cost-proof`), Part 1)**:
   Root convolution coefficient bounds, nearest-integer rounding recovery, and bit-exact base-$2^b$
   carry-propagation reconstruction (`carry_propagation_eq_mul`).
-/

namespace IntMul

/-! ## 1. Cyclic Bidiagonal Deconvolution & Conditioning (Theorem 5.1(1)–(2) (`thm:deconv`), Section 5.1 (`sec:deconv-thm`)) -/

/-- Cyclic successor index `(m + 1) mod t1` on `Fin t1`. -/
def cyclicNext {t1 : ℕ} [NeZero t1] (m : Fin t1) : Fin t1 :=
  ⟨(m.val + 1) % t1, Nat.mod_lt _ (NeZero.pos t1)⟩

/-- Cyclic predecessor index `(m - 1) mod t1 = (m + (t1 - 1)) mod t1` on `Fin t1`. -/
def cyclicPrev {t1 : ℕ} [NeZero t1] (m : Fin t1) : Fin t1 :=
  ⟨(m.val + (t1 - 1)) % t1, Nat.mod_lt _ (NeZero.pos t1)⟩

/-- Cyclic forward shift `(m + s) mod t1` on `Fin t1`. -/
def cyclicShift {t1 : ℕ} [NeZero t1] (m : Fin t1) (s : ℕ) : Fin t1 :=
  ⟨(m.val + s) % t1, Nat.mod_lt _ (NeZero.pos t1)⟩

/-- Cyclic backward shift `(m - (s + 1)) mod t1 = (m + (t1 - 1) * (s + 1)) mod t1` on `Fin t1`. -/
def cyclicBackShift {t1 : ℕ} [NeZero t1] (m : Fin t1) (s : ℕ) : Fin t1 :=
  ⟨(m.val + (t1 - 1) * (s + 1)) % t1, Nat.mod_lt _ (NeZero.pos t1)⟩

@[simp]
theorem cyclicNext_cyclicPrev {t1 : ℕ} [NeZero t1] (m : Fin t1) :
    cyclicNext (cyclicPrev m) = m := by
  ext
  simp only [cyclicNext, cyclicPrev, Nat.mod_add_mod]
  have ht1 : 1 ≤ t1 := NeZero.one_le
  have heq : m.val + (t1 - 1) + 1 = m.val + t1 := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt m.isLt]

@[simp]
theorem cyclicPrev_cyclicNext {t1 : ℕ} [NeZero t1] (m : Fin t1) :
    cyclicPrev (cyclicNext m) = m := by
  ext
  simp only [cyclicPrev, cyclicNext, Nat.mod_add_mod]
  have ht1 : 1 ≤ t1 := NeZero.one_le
  have heq : m.val + 1 + (t1 - 1) = m.val + t1 := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt m.isLt]

/-- When `0 < u1.val`, `cyclicPrev u1` has index `u1.val - 1`. -/
theorem cyclicPrev_eq_sub_one_of_pos {t1 : ℕ} [NeZero t1] (u1 : Fin t1) (hu1 : 0 < u1.val) :
    cyclicPrev u1 = ⟨u1.val - 1, by omega⟩ := by
  ext
  simp only [cyclicPrev]
  have h1 : u1.val + (t1 - 1) = (u1.val - 1) + t1 * 1 := by omega
  have hlt : u1.val - 1 < t1 := by omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Equivalence between `intModFin t1 ht1 ((u1.val : ℤ) - 1)` from `PoissonKernel` and `cyclicPrev u1`. -/
theorem intModFin_sub_one_eq_cyclicPrev {t1 : ℕ} [NeZero t1] (u1 : Fin t1) :
    intModFin t1 (NeZero.pos t1) ((u1.val : ℤ) - 1) = cyclicPrev u1 := by
  have ht1_pos : 0 < t1 := NeZero.pos t1
  have ht1_one : 1 ≤ t1 := NeZero.one_le
  apply Fin.ext
  apply Nat.cast_injective (R := ℤ)
  rw [intModFin_coe]
  rcases eq_or_ne u1.val 0 with hu0 | hu_ne
  · simp only [cyclicPrev, hu0, zero_add, Nat.cast_zero]
    have hlt_nat : t1 - 1 < t1 := by omega
    rw [Nat.mod_eq_of_lt hlt_nat]
    have hsub : (0 : ℤ) - 1 = ((t1 - 1 : ℕ) : ℤ) + (t1 : ℤ) * (-1) := by
      push_cast [Nat.cast_sub ht1_one]
      ring
    rw [hsub, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (Nat.cast_nonneg _) (Nat.cast_lt.mpr hlt_nat)
  · have hu_pos : 0 < u1.val := Nat.pos_of_ne_zero hu_ne
    rw [cyclicPrev_eq_sub_one_of_pos u1 hu_pos]
    dsimp only
    have hlt_nat : u1.val - 1 < t1 := by omega
    have hsub : (u1.val : ℤ) - 1 = ((u1.val - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hu_pos]
      ring
    rw [hsub]
    exact Int.emod_eq_of_lt (Nat.cast_nonneg _) (Nat.cast_lt.mpr hlt_nat)

@[simp]
theorem vecInfNorm_comp_cyclicNext {t1 : ℕ} [NeZero t1] (B : Fin t1 → ℂ) :
    vecInfNorm (fun m => B (cyclicNext m)) = vecInfNorm B := by
  apply le_antisymm
  · rw [vecInfNorm_le_iff _ (vecInfNorm_nonneg B)]
    intro m
    exact norm_le_vecInfNorm B (cyclicNext m)
  · rw [vecInfNorm_le_iff _ (vecInfNorm_nonneg (fun m => B (cyclicNext m)))]
    intro m
    have h := norm_le_vecInfNorm (fun k => B (cyclicNext k)) (cyclicPrev m)
    simpa [cyclicNext_cyclicPrev] using h

@[simp]
theorem vecInfNorm_comp_cyclicPrev {t1 : ℕ} [NeZero t1] (B : Fin t1 → ℂ) :
    vecInfNorm (fun m => B (cyclicPrev m)) = vecInfNorm B := by
  apply le_antisymm
  · rw [vecInfNorm_le_iff _ (vecInfNorm_nonneg B)]
    intro m
    exact norm_le_vecInfNorm B (cyclicPrev m)
  · rw [vecInfNorm_le_iff _ (vecInfNorm_nonneg (fun m => B (cyclicPrev m)))]
    intro m
    have h := norm_le_vecInfNorm (fun k => B (cyclicPrev k)) (cyclicNext m)
    simpa [cyclicPrev_cyclicNext] using h

/-- Direct cyclic bidiagonal solver for $c_0 W_m + c_1 W_{(m+1) \bmod t_1} = B_m$
pivoted on $c_0$:
$$(M_{c_0, c_1}^{-1} B)_m = \frac{1}{c_0 (1 - (-c_1/c_0)^{t_1})} \sum_{s=0}^{t_1-1} \left(-\frac{c_1}{c_0}\right)^s B_{(m+s) \bmod t_1}.$$ -/
noncomputable def cyclicBidiagSolveDirect {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℂ) (B : Fin t1 → ℂ) (m : Fin t1) : ℂ :=
  (c0 * (1 - (-c1 / c0) ^ t1))⁻¹ *
    ∑ s ∈ Finset.range t1, (-c1 / c0) ^ s * B (cyclicShift m s)

/-- Column-pivoted cyclic bidiagonal solver for $c_0 W_m + c_1 W_{(m+1) \bmod t_1} = B_m$
pivoted on $c_1$:
$$(M_{c_0, c_1}^{-1} B)_m = \frac{1}{c_1 (1 - (-c_0/c_1)^{t_1})} \sum_{s=0}^{t_1-1} \left(-\frac{c_0}{c_1}\right)^s B_{(m - 1 - s) \bmod t_1}.$$ -/
noncomputable def cyclicBidiagSolvePivoted {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℂ) (B : Fin t1 → ℂ) (m : Fin t1) : ℂ :=
  (c1 * (1 - (-c0 / c1) ^ t1))⁻¹ *
    ∑ s ∈ Finset.range t1, (-c0 / c1) ^ s * B (cyclicBackShift m s)

/-- Uniformly conditioned 2-term cyclic bidiagonal solver for real passband weights $c_0, c_1 \in \mathbb{R}$,
pivoting on $\max(c_0, c_1)$ (Theorem 5.1(2) (`thm:deconv`), equation (23) (`eq:closed-form-B`)). -/
noncomputable def cyclicBidiagSolve {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ) : Fin t1 → ℂ :=
  if c1 ≤ c0 then
    cyclicBidiagSolveDirect (c0 : ℂ) (c1 : ℂ) B
  else
    cyclicBidiagSolvePivoted (c0 : ℂ) (c1 : ℂ) B

private theorem cyclicShift_zero {t1 : ℕ} [NeZero t1] (m : Fin t1) :
    cyclicShift m 0 = m := by
  ext
  simp [cyclicShift, Nat.mod_eq_of_lt m.isLt]

private theorem cyclicShift_self {t1 : ℕ} [NeZero t1] (m : Fin t1) :
    cyclicShift m t1 = m := by
  ext
  simp [cyclicShift, Nat.add_mod_right, Nat.mod_eq_of_lt m.isLt]

private theorem cyclicShift_cyclicNext {t1 : ℕ} [NeZero t1] (m : Fin t1) (s : ℕ) :
    cyclicShift (cyclicNext m) s = cyclicShift m (s + 1) := by
  ext
  simp only [cyclicShift, cyclicNext, Nat.mod_add_mod]
  congr 1
  omega

/-- Exact algebraic inversion for `cyclicBidiagSolveDirect`: when $c_0 \ne 0$ and
$(-c_1 / c_0)^{t_1} \ne 1$, `cyclicBidiagSolveDirect c0 c1 B` satisfies the 2-term cyclic
bidiagonal system $c_0 W_m + c_1 W_{(m+1) \bmod t_1} = B_m$ for all $m \in \text{Fin } t_1$. -/
theorem cyclicBidiagSolveDirect_spec {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℂ) (B : Fin t1 → ℂ) (hc0 : c0 ≠ 0) (hr : (-c1 / c0) ^ t1 ≠ 1) (m : Fin t1) :
    c0 * cyclicBidiagSolveDirect c0 c1 B m +
      c1 * cyclicBidiagSolveDirect c0 c1 B (cyclicNext m) = B m := by
  unfold cyclicBidiagSolveDirect
  set r : ℂ := -c1 / c0
  set f : ℕ → ℂ := fun s => r ^ s * B (cyclicShift m s)
  have hc1 : c1 = -c0 * r := by
    simp only [r]
    field_simp
  have h1mr : 1 - r ^ t1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have hshift : (∑ s ∈ Finset.range t1, r ^ s * B (cyclicShift (cyclicNext m) s)) =
      ∑ s ∈ Finset.range t1, r ^ s * B (cyclicShift m (s + 1)) := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [cyclicShift_cyclicNext]
  have hmul_sum : r * (∑ s ∈ Finset.range t1, r ^ s * B (cyclicShift m (s + 1))) =
      ∑ s ∈ Finset.range t1, f (s + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [f, pow_succ', mul_assoc]
  have htel : (∑ s ∈ Finset.range t1, f s) - (∑ s ∈ Finset.range t1, f (s + 1)) =
      (1 - r ^ t1) * B m := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub' f t1]
    simp only [f, pow_zero, one_mul, cyclicShift_zero, cyclicShift_self]
    ring
  rw [hshift, hc1]
  have hcomb :
      c0 * ((c0 * (1 - r ^ t1))⁻¹ * ∑ s ∈ Finset.range t1, f s) +
        -c0 * r * ((c0 * (1 - r ^ t1))⁻¹ * ∑ s ∈ Finset.range t1, r ^ s * B (cyclicShift m (s + 1))) =
      c0 * (c0 * (1 - r ^ t1))⁻¹ *
        ((∑ s ∈ Finset.range t1, f s) - r * ∑ s ∈ Finset.range t1, r ^ s * B (cyclicShift m (s + 1))) := by
    ring
  rw [hcomb, hmul_sum, htel]
  have hprod_ne : c0 * (1 - r ^ t1) ≠ 0 := mul_ne_zero hc0 h1mr
  calc
    c0 * (c0 * (1 - r ^ t1))⁻¹ * ((1 - r ^ t1) * B m)
      = (c0 * (1 - r ^ t1)) * (c0 * (1 - r ^ t1))⁻¹ * B m := by ring
    _ = 1 * B m := by rw [mul_inv_cancel₀ hprod_ne]
    _ = B m := one_mul (B m)

private theorem cyclicBackShift_cyclicNext {t1 : ℕ} [NeZero t1] (m : Fin t1) (s : ℕ) :
    cyclicBackShift (cyclicNext m) s =
      ⟨(m.val + (t1 - 1) * s) % t1, Nat.mod_lt _ (NeZero.pos t1)⟩ := by
  ext
  simp only [cyclicBackShift, cyclicNext, Nat.mod_add_mod]
  have ht1 : 1 ≤ t1 := NeZero.one_le
  have heq : m.val + 1 + (t1 - 1) * (s + 1) = (m.val + (t1 - 1) * s) + t1 := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [heq, Nat.add_mod_right]

/-- Exact algebraic inversion for `cyclicBidiagSolvePivoted`: when $c_1 \ne 0$ and
$(-c_0 / c_1)^{t_1} \ne 1$, `cyclicBidiagSolvePivoted c0 c1 B` satisfies the 2-term cyclic
bidiagonal system $c_0 W_m + c_1 W_{(m+1) \bmod t_1} = B_m$ for all $m \in \text{Fin } t_1$. -/
theorem cyclicBidiagSolvePivoted_spec {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℂ) (B : Fin t1 → ℂ) (hc1 : c1 ≠ 0) (hr : (-c0 / c1) ^ t1 ≠ 1) (m : Fin t1) :
    c0 * cyclicBidiagSolvePivoted c0 c1 B m +
      c1 * cyclicBidiagSolvePivoted c0 c1 B (cyclicNext m) = B m := by
  unfold cyclicBidiagSolvePivoted
  set r : ℂ := -c0 / c1
  set g : ℕ → ℂ := fun s =>
    r ^ s * B ⟨(m.val + (t1 - 1) * s) % t1, Nat.mod_lt _ (NeZero.pos t1)⟩
  have hc0 : c0 = -c1 * r := by
    simp only [r]
    field_simp
  have h1mr : 1 - r ^ t1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have hnext : (∑ s ∈ Finset.range t1, r ^ s * B (cyclicBackShift (cyclicNext m) s)) =
      ∑ s ∈ Finset.range t1, g s := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [cyclicBackShift_cyclicNext]
  have hmul_sum : r * (∑ s ∈ Finset.range t1, r ^ s * B (cyclicBackShift m s)) =
      ∑ s ∈ Finset.range t1, g (s + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [g, cyclicBackShift, pow_succ', mul_assoc]
  have hg0 : g 0 = B m := by
    simp only [g, pow_zero, one_mul, mul_zero, add_zero]
    congr 1
    ext
    exact Nat.mod_eq_of_lt m.isLt
  have hgt1 : g t1 = r ^ t1 * B m := by
    simp only [g, Nat.add_mul_mod_self_right]
    congr 2
    ext
    exact Nat.mod_eq_of_lt m.isLt
  have htel : (∑ s ∈ Finset.range t1, g s) - (∑ s ∈ Finset.range t1, g (s + 1)) =
      (1 - r ^ t1) * B m := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub' g t1, hg0, hgt1]
    ring
  rw [hnext, hc0]
  have hcomb :
      -c1 * r * ((c1 * (1 - r ^ t1))⁻¹ * ∑ s ∈ Finset.range t1, r ^ s * B (cyclicBackShift m s)) +
        c1 * ((c1 * (1 - r ^ t1))⁻¹ * ∑ s ∈ Finset.range t1, g s) =
      c1 * (c1 * (1 - r ^ t1))⁻¹ *
        ((∑ s ∈ Finset.range t1, g s) - r * ∑ s ∈ Finset.range t1, r ^ s * B (cyclicBackShift m s)) := by
    ring
  rw [hcomb, hmul_sum, htel]
  have hprod_ne : c1 * (1 - r ^ t1) ≠ 0 := mul_ne_zero hc1 h1mr
  calc
    c1 * (c1 * (1 - r ^ t1))⁻¹ * ((1 - r ^ t1) * B m)
      = (c1 * (1 - r ^ t1)) * (c1 * (1 - r ^ t1))⁻¹ * B m := by ring
    _ = 1 * B m := by rw [mul_inv_cancel₀ hprod_ne]
    _ = B m := one_mul (B m)

private theorem norm_neg_ofReal_div_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ‖-(a : ℂ) / (b : ℂ)‖ = a / b := by
  rw [norm_div, norm_neg, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_pos hb]

private theorem neg_div_pow_ne_one_of_pow_lt_one {t1 : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hq : (a / b) ^ t1 < 1) :
    (-(a : ℂ) / (b : ℂ)) ^ t1 ≠ 1 := by
  intro h
  have hnorm : ‖(-(a : ℂ) / (b : ℂ)) ^ t1‖ = ‖(1 : ℂ)‖ := congrArg (fun z => ‖z‖) h
  rw [norm_pow, norm_neg_ofReal_div_ofReal ha hb, norm_one] at hnorm
  linarith

/-- **Exact Algebraic Inversion Theorem (`cyclicBidiagSolve_spec`, Theorem 5.1(2) (`thm:deconv`))**:
Whenever $\max(c_0, c_1) > 0$, $\min(c_0, c_1) \ge 0$, and $(\min(c_0, c_1)/\max(c_0, c_1))^{t_1} < 1$,
`cyclicBidiagSolve c0 c1 B` satisfies the 2-term cyclic bidiagonal linear system
$c_0 W_m + c_1 W_{(m+1) \bmod t_1} = B_m$ for all $m \in \text{Fin } t_1$. -/
theorem cyclicBidiagSolve_spec {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ)
    (hcmax : 0 < max c0 c1) (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 < 1) (m : Fin t1) :
    (c0 : ℂ) * cyclicBidiagSolve c0 c1 B m +
      (c1 : ℂ) * cyclicBidiagSolve c0 c1 B (cyclicNext m) = B m := by
  unfold cyclicBidiagSolve
  split_ifs with hle
  · have hmax : max c0 c1 = c0 := max_eq_left hle
    have hmin : min c0 c1 = c1 := min_eq_right hle
    rw [hmax] at hcmax hq
    rw [hmin] at hcmin hq
    have hc0_ne : (c0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hcmax)
    have hr_ne : (-(c1 : ℂ) / (c0 : ℂ)) ^ t1 ≠ 1 :=
      neg_div_pow_ne_one_of_pow_lt_one hcmin hcmax hq
    exact cyclicBidiagSolveDirect_spec (c0 : ℂ) (c1 : ℂ) B hc0_ne hr_ne m
  · push_neg at hle
    have hmax : max c0 c1 = c1 := max_eq_right (le_of_lt hle)
    have hmin : min c0 c1 = c0 := min_eq_left (le_of_lt hle)
    rw [hmax] at hcmax hq
    rw [hmin] at hcmin hq
    have hc1_ne : (c1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hcmax)
    have hr_ne : (-(c0 : ℂ) / (c1 : ℂ)) ^ t1 ≠ 1 :=
      neg_div_pow_ne_one_of_pow_lt_one hcmin hcmax hq
    exact cyclicBidiagSolvePivoted_spec (c0 : ℂ) (c1 : ℂ) B hc1_ne hr_ne m

private theorem norm_inv_one_sub_neg_div_pow_le {t1 : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hq : (a / b) ^ t1 < 1) :
    ‖((b : ℂ) * (1 - (-(a : ℂ) / (b : ℂ)) ^ t1))⁻¹‖ ≤
      1 / (b * (1 - (a / b) ^ t1)) := by
  rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, one_div]
  have hnorm_r : ‖(-(a : ℂ) / (b : ℂ)) ^ t1‖ = (a / b) ^ t1 := by
    rw [norm_pow, norm_neg_ofReal_div_ofReal ha hb]
  have htri : 1 - (a / b) ^ t1 ≤ ‖(1 : ℂ) - (-(a : ℂ) / (b : ℂ)) ^ t1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((-(a : ℂ) / (b : ℂ)) ^ t1)
    simpa [hnorm_r] using h
  have hpos : 0 < 1 - (a / b) ^ t1 := sub_pos.mpr hq
  exact inv_anti₀ (mul_pos hb hpos) (mul_le_mul_of_nonneg_left htri (le_of_lt hb))

/-- **Geometric-Sum $\ell_\infty$ Condition Number Bound (Theorem 5.1(2) (`thm:deconv`), equation (24) (`eq:B-inv-norm`))**:
When $c_{\max} = \max(c_0, c_1) > 0$, $c_{\min} = \min(c_0, c_1) \ge 0$, and
$q_{\text{ratio}} = (c_{\min}/c_{\max})^{t_1} < 1$, the solution $W = \text{cyclicBidiagSolve } c_0 \, c_1 \, B$
satisfies:
$$\|W\|_\infty \le \frac{1}{1 - q_{\text{ratio}}} \cdot \frac{\sum_{s=0}^{t_1-1} (c_{\min}/c_{\max})^s}{c_{\max}} \|B\|_\infty.$$ -/
theorem vecInfNorm_cyclicBidiagSolve_geom_le {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ)
    (hcmax : 0 < max c0 c1) (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 < 1) :
    vecInfNorm (cyclicBidiagSolve c0 c1 B) ≤
      (1 / (1 - (min c0 c1 / max c0 c1) ^ t1)) *
        ((∑ s ∈ Finset.range t1, (min c0 c1 / max c0 c1) ^ s) / max c0 c1) *
        vecInfNorm B := by
  have hq_pos : 0 < 1 - (min c0 c1 / max c0 c1) ^ t1 := sub_pos.mpr hq
  have hratio_nonneg : 0 ≤ min c0 c1 / max c0 c1 := div_nonneg hcmin (le_of_lt hcmax)
  have hsum_nonneg : 0 ≤ ∑ s ∈ Finset.range t1, (min c0 c1 / max c0 c1) ^ s :=
    Finset.sum_nonneg (fun s _ => pow_nonneg hratio_nonneg s)
  have hrhs_nonneg :
      0 ≤ (1 / (1 - (min c0 c1 / max c0 c1) ^ t1)) *
        ((∑ s ∈ Finset.range t1, (min c0 c1 / max c0 c1) ^ s) / max c0 c1) *
        vecInfNorm B :=
    mul_nonneg (mul_nonneg (div_nonneg zero_le_one (le_of_lt hq_pos))
      (div_nonneg hsum_nonneg (le_of_lt hcmax))) (vecInfNorm_nonneg B)
  rw [vecInfNorm_le_iff _ hrhs_nonneg]
  intro m
  unfold cyclicBidiagSolve
  split_ifs with hle
  · have hmax : max c0 c1 = c0 := max_eq_left hle
    have hmin : min c0 c1 = c1 := min_eq_right hle
    have hc0_pos : 0 < c0 := by simpa [hmax] using hcmax
    have hc1_nonneg : 0 ≤ c1 := by simpa [hmin] using hcmin
    have hq' : (c1 / c0) ^ t1 < 1 := by simpa [hmax, hmin] using hq
    rw [hmax, hmin]
    unfold cyclicBidiagSolveDirect
    rw [norm_mul]
    have hinv := norm_inv_one_sub_neg_div_pow_le hc1_nonneg hc0_pos hq'
    have hsum : ‖∑ s ∈ Finset.range t1, (-(c1 : ℂ) / (c0 : ℂ)) ^ s * B (cyclicShift m s)‖ ≤
        (∑ s ∈ Finset.range t1, (c1 / c0) ^ s) * vecInfNorm B := by
      calc
        ‖∑ s ∈ Finset.range t1, (-(c1 : ℂ) / (c0 : ℂ)) ^ s * B (cyclicShift m s)‖
          ≤ ∑ s ∈ Finset.range t1, ‖(-(c1 : ℂ) / (c0 : ℂ)) ^ s * B (cyclicShift m s)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ s ∈ Finset.range t1, (c1 / c0) ^ s * vecInfNorm B := by
          apply Finset.sum_le_sum
          intro s _
          rw [norm_mul, norm_pow, norm_neg_ofReal_div_ofReal hc1_nonneg hc0_pos]
          exact mul_le_mul_of_nonneg_left (norm_le_vecInfNorm B _)
            (pow_nonneg (div_nonneg hc1_nonneg (le_of_lt hc0_pos)) s)
        _ = (∑ s ∈ Finset.range t1, (c1 / c0) ^ s) * vecInfNorm B := by
          rw [← Finset.sum_mul]
    have hinv_nn : 0 ≤ 1 / (c0 * (1 - (c1 / c0) ^ t1)) :=
      div_nonneg zero_le_one (mul_nonneg (le_of_lt hc0_pos) (le_of_lt (sub_pos.mpr hq')))
    set qv : ℝ := (c1 / c0) ^ t1
    set Sv : ℝ := ∑ s ∈ Finset.range t1, (c1 / c0) ^ s
    calc
      ‖((c0 : ℂ) * (1 - (-(c1 : ℂ) / (c0 : ℂ)) ^ t1))⁻¹‖ *
          ‖∑ s ∈ Finset.range t1, (-(c1 : ℂ) / (c0 : ℂ)) ^ s * B (cyclicShift m s)‖
        ≤ (1 / (c0 * (1 - qv))) * (Sv * vecInfNorm B) :=
          mul_le_mul hinv hsum (norm_nonneg _) hinv_nn
      _ = (1 / (1 - qv)) * (Sv / c0) * vecInfNorm B := by
          rw [one_div, mul_inv, one_div, div_eq_mul_inv]
          ring
  · push_neg at hle
    have hmax : max c0 c1 = c1 := max_eq_right (le_of_lt hle)
    have hmin : min c0 c1 = c0 := min_eq_left (le_of_lt hle)
    have hc1_pos : 0 < c1 := by simpa [hmax] using hcmax
    have hc0_nonneg : 0 ≤ c0 := by simpa [hmin] using hcmin
    have hq' : (c0 / c1) ^ t1 < 1 := by simpa [hmax, hmin] using hq
    rw [hmax, hmin]
    unfold cyclicBidiagSolvePivoted
    rw [norm_mul]
    have hinv := norm_inv_one_sub_neg_div_pow_le hc0_nonneg hc1_pos hq'
    have hsum : ‖∑ s ∈ Finset.range t1, (-(c0 : ℂ) / (c1 : ℂ)) ^ s * B (cyclicBackShift m s)‖ ≤
        (∑ s ∈ Finset.range t1, (c0 / c1) ^ s) * vecInfNorm B := by
      calc
        ‖∑ s ∈ Finset.range t1, (-(c0 : ℂ) / (c1 : ℂ)) ^ s * B (cyclicBackShift m s)‖
          ≤ ∑ s ∈ Finset.range t1, ‖(-(c0 : ℂ) / (c1 : ℂ)) ^ s * B (cyclicBackShift m s)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ s ∈ Finset.range t1, (c0 / c1) ^ s * vecInfNorm B := by
          apply Finset.sum_le_sum
          intro s _
          rw [norm_mul, norm_pow, norm_neg_ofReal_div_ofReal hc0_nonneg hc1_pos]
          exact mul_le_mul_of_nonneg_left (norm_le_vecInfNorm B _)
            (pow_nonneg (div_nonneg hc0_nonneg (le_of_lt hc1_pos)) s)
        _ = (∑ s ∈ Finset.range t1, (c0 / c1) ^ s) * vecInfNorm B := by
          rw [← Finset.sum_mul]
    have hinv_nn : 0 ≤ 1 / (c1 * (1 - (c0 / c1) ^ t1)) :=
      div_nonneg zero_le_one (mul_nonneg (le_of_lt hc1_pos) (le_of_lt (sub_pos.mpr hq')))
    set qv : ℝ := (c0 / c1) ^ t1
    set Sv : ℝ := ∑ s ∈ Finset.range t1, (c0 / c1) ^ s
    calc
      ‖((c1 : ℂ) * (1 - (-(c0 : ℂ) / (c1 : ℂ)) ^ t1))⁻¹‖ *
          ‖∑ s ∈ Finset.range t1, (-(c0 : ℂ) / (c1 : ℂ)) ^ s * B (cyclicBackShift m s)‖
        ≤ (1 / (c1 * (1 - qv))) * (Sv * vecInfNorm B) :=
          mul_le_mul hinv hsum (norm_nonneg _) hinv_nn
      _ = (1 / (1 - qv)) * (Sv / c1) * vecInfNorm B := by
          rw [one_div, mul_inv, one_div, div_eq_mul_inv]
          ring

/-- **Uniform $\ell_\infty$ Condition Number Bound (`vecInfNorm_cyclicBidiagSolve_le`, Theorem 5.1(2) (`thm:deconv`))**:
$$\|W\|_\infty \le \frac{t_1}{c_{\max} (1 - q_{\text{ratio}})} \|B\|_\infty.$$ -/
theorem vecInfNorm_cyclicBidiagSolve_le {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ)
    (hcmax : 0 < max c0 c1) (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 < 1) :
    vecInfNorm (cyclicBidiagSolve c0 c1 B) ≤
      ((t1 : ℝ) / (max c0 c1 * (1 - (min c0 c1 / max c0 c1) ^ t1))) * vecInfNorm B := by
  have hgeom := vecInfNorm_cyclicBidiagSolve_geom_le c0 c1 B hcmax hcmin hq
  have hratio_le_one : min c0 c1 / max c0 c1 ≤ 1 :=
    div_le_one_of_le₀ (min_le_max) (le_of_lt hcmax)
  have hratio_nonneg : 0 ≤ min c0 c1 / max c0 c1 := div_nonneg hcmin (le_of_lt hcmax)
  have hsum_le : (∑ s ∈ Finset.range t1, (min c0 c1 / max c0 c1) ^ s) ≤ (t1 : ℝ) := by
    calc
      (∑ s ∈ Finset.range t1, (min c0 c1 / max c0 c1) ^ s)
        ≤ ∑ _s ∈ Finset.range t1, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro s _
          exact pow_le_one₀ hratio_nonneg hratio_le_one
      _ = (t1 : ℝ) := by simp
  have hq_pos : 0 < 1 - (min c0 c1 / max c0 c1) ^ t1 := sub_pos.mpr hq
  set qv : ℝ := (min c0 c1 / max c0 c1) ^ t1
  set cm : ℝ := max c0 c1
  have hstep :
      (1 / (1 - qv)) *
        ((∑ s ∈ Finset.range t1, (min c0 c1 / max c0 c1) ^ s) / cm) ≤
      (t1 : ℝ) / (cm * (1 - qv)) := by
    calc
      (1 / (1 - qv)) *
          ((∑ s ∈ Finset.range t1, (min c0 c1 / max c0 c1) ^ s) / cm)
        ≤ (1 / (1 - qv)) * ((t1 : ℝ) / cm) := by
          apply mul_le_mul_of_nonneg_left
          · exact div_le_div_of_nonneg_right hsum_le (le_of_lt hcmax)
          · exact div_nonneg zero_le_one (le_of_lt hq_pos)
      _ = (t1 : ℝ) / (cm * (1 - qv)) := by
          rw [one_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
          ring
  exact le_trans hgeom (mul_le_mul_of_nonneg_right hstep (vecInfNorm_nonneg B))

/-- Numerical conditioning factor bound: when $c_{\max} \ge 0.49999999$ and $q_{\text{ratio}} \le 0.15$,
$$\frac{1}{c_{\max} (1 - q_{\text{ratio}})} \le \frac{1}{0.49999999 \times 0.85} < 2.36.$$ -/
theorem inv_cmax_mul_one_sub_q_lt_236 {cmax q : ℝ}
    (hcmax : (49999999 / 100000000 : ℝ) ≤ cmax) (hq : q ≤ (15 / 100 : ℝ)) :
    1 / (cmax * (1 - q)) < (236 / 100 : ℝ) := by
  have h1mq : (85 / 100 : ℝ) ≤ 1 - q := by linarith
  have hprod : (49999999 / 100000000 : ℝ) * (85 / 100 : ℝ) ≤ cmax * (1 - q) :=
    mul_le_mul hcmax h1mq (by norm_num) (by linarith)
  have hpos : (0 : ℝ) < cmax * (1 - q) := by linarith
  rw [div_lt_iff₀ hpos]
  linarith

/-- **Explicit $2.36 \, t_1$ Deconvolution Conditioning Bound (`deconvolution_conditioning_le_236_t1_of_bounds`, Theorem 5.1(2) (`thm:deconv`))**:
When $\max(c_0, c_1) \ge 0.49999999$, $\min(c_0, c_1) \ge 0$, and
$(\min(c_0, c_1)/\max(c_0, c_1))^{t_1} \le 0.15$, the cyclic bidiagonal solver satisfies:
$$\|\text{cyclicBidiagSolve } c_0 \, c_1 \, B\|_\infty \le 2.36 \, t_1 \, \|B\|_\infty.$$ -/
theorem deconvolution_conditioning_le_236_t1_of_bounds {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ)
    (hcmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1)
    (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 ≤ (15 / 100 : ℝ)) :
    vecInfNorm (cyclicBidiagSolve c0 c1 B) ≤ (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm B := by
  have hcmax_pos : 0 < max c0 c1 := by linarith
  have hq_lt : (min c0 c1 / max c0 c1) ^ t1 < 1 := by linarith
  have hbase := vecInfNorm_cyclicBidiagSolve_le c0 c1 B hcmax_pos hcmin hq_lt
  have hfac := le_of_lt (inv_cmax_mul_one_sub_q_lt_236 hcmax hq)
  have hstep :
      (t1 : ℝ) / (max c0 c1 * (1 - (min c0 c1 / max c0 c1) ^ t1)) ≤
        (236 / 100 : ℝ) * (t1 : ℝ) := by
    calc
      (t1 : ℝ) / (max c0 c1 * (1 - (min c0 c1 / max c0 c1) ^ t1))
        = (1 / (max c0 c1 * (1 - (min c0 c1 / max c0 c1) ^ t1))) * (t1 : ℝ) := by ring
      _ ≤ (236 / 100 : ℝ) * (t1 : ℝ) :=
        mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg t1)
  exact le_trans hbase (mul_le_mul_of_nonneg_right hstep (vecInfNorm_nonneg B))

private theorem min_lt_max_of_div_pow_lt_one {t1 : ℕ} {c0 c1 : ℝ}
    (hcmax : 0 < max c0 c1) (hq : (min c0 c1 / max c0 c1) ^ t1 < 1) :
    min c0 c1 < max c0 c1 := by
  rcases eq_or_lt_of_le (min_le_max (a := c0) (b := c1)) with heq | hlt
  · exfalso
    rw [heq, div_self (ne_of_gt hcmax), one_pow] at hq
    exact lt_irrefl 1 hq
  · exact hlt

/-- **Uniqueness / Left-Inverse Theorem for `cyclicBidiagSolve` (`cyclicBidiagSolve_of_spec`)**:
If $W : \text{Fin } t_1 \to \mathbb{C}$ satisfies the 2-term cyclic bidiagonal system
$c_0 W_m + c_1 W_{(m+1) \bmod t_1} = B_m$ for all $m \in \text{Fin } t_1$, then
`cyclicBidiagSolve c0 c1 B = W`. -/
theorem cyclicBidiagSolve_of_spec {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B W : Fin t1 → ℂ)
    (hcmax : 0 < max c0 c1) (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 < 1)
    (hW : ∀ m : Fin t1, (c0 : ℂ) * W m + (c1 : ℂ) * W (cyclicNext m) = B m) :
    cyclicBidiagSolve c0 c1 B = W := by
  set E : Fin t1 → ℂ := fun m => cyclicBidiagSolve c0 c1 B m - W m
  have hc0_nn : 0 ≤ c0 := le_trans hcmin (min_le_left c0 c1)
  have hc1_nn : 0 ≤ c1 := le_trans hcmin (min_le_right c0 c1)
  have hE_eq : ∀ m : Fin t1, (c0 : ℂ) * E m = -((c1 : ℂ) * E (cyclicNext m)) := by
    intro m
    have h1 := cyclicBidiagSolve_spec c0 c1 B hcmax hcmin hq m
    have h2 := hW m
    dsimp [E]
    linear_combination h1 - h2
  have hE_norm : ∀ m : Fin t1, c0 * ‖E m‖ = c1 * ‖E (cyclicNext m)‖ := by
    intro m
    have h := congrArg (fun z : ℂ => ‖z‖) (hE_eq m)
    simpa [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0_nn,
      Real.norm_of_nonneg hc1_nn] using h
  have hE_nn : 0 ≤ vecInfNorm E := vecInfNorm_nonneg E
  have hle1 : c0 * vecInfNorm E ≤ c1 * vecInfNorm E := by
    rcases le_or_gt c0 0 with hc0_0 | hc0_pos
    · have hc0_eq : c0 = 0 := le_antisymm hc0_0 hc0_nn
      rw [hc0_eq, zero_mul]
      exact mul_nonneg hc1_nn hE_nn
    · have hE_le : vecInfNorm E ≤ (c1 * vecInfNorm E) / c0 := by
        rw [vecInfNorm_le_iff E (div_nonneg (mul_nonneg hc1_nn hE_nn) (le_of_lt hc0_pos))]
        intro m
        rw [le_div_iff₀ hc0_pos]
        have hm := hE_norm m
        have hnext := norm_le_vecInfNorm E (cyclicNext m)
        nlinarith
      have hmul := (le_div_iff₀ hc0_pos).mp hE_le
      linarith
  have hle2 : c1 * vecInfNorm E ≤ c0 * vecInfNorm E := by
    rcases le_or_gt c1 0 with hc1_0 | hc1_pos
    · have hc1_eq : c1 = 0 := le_antisymm hc1_0 hc1_nn
      rw [hc1_eq, zero_mul]
      exact mul_nonneg hc0_nn hE_nn
    · have hE_le : vecInfNorm E ≤ (c0 * vecInfNorm E) / c1 := by
        rw [vecInfNorm_le_iff E (div_nonneg (mul_nonneg hc0_nn hE_nn) (le_of_lt hc1_pos))]
        intro m
        rw [le_div_iff₀ hc1_pos]
        have hm := hE_norm (cyclicPrev m)
        rw [cyclicNext_cyclicPrev] at hm
        have hprev := norm_le_vecInfNorm E (cyclicPrev m)
        nlinarith
      have hmul := (le_div_iff₀ hc1_pos).mp hE_le
      linarith
  have hlt : min c0 c1 < max c0 c1 := min_lt_max_of_div_pow_lt_one hcmax hq
  have hmax_min : max c0 c1 * vecInfNorm E ≤ min c0 c1 * vecInfNorm E := by
    rcases le_total c0 c1 with h | h
    · simpa [max_eq_right h, min_eq_left h] using hle2
    · simpa [max_eq_left h, min_eq_right h] using hle1
  have hE_zero : vecInfNorm E ≤ 0 := by nlinarith [vecInfNorm_nonneg E]
  funext m
  have hm0 : ‖E m‖ ≤ 0 := (norm_le_vecInfNorm E m).trans hE_zero
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hm0)

/-! ### 1.2 Backward-Shift `(u1 - 1) mod t1` Cyclic Bidiagonal Solver (`cyclicBidiagPrevSolve`, Theorem 5.1(2) (`thm:deconv`)) -/

/-- Uniformly conditioned backward-shift 2-term cyclic bidiagonal solver for the Poisson recurrence
$c_0 W_m + c_1 W_{(m-1) \bmod t_1} = B_m$ (Theorem 4.2 (`thm:poisson`) and Theorem 5.1(2) (`thm:deconv`),
equation (23) (`eq:closed-form-B`)). Since $c_0 W_m + c_1 W_{\text{cyclicPrev } m} = B_m$ at
$m = \text{cyclicNext } m'$ is equivalent to
$c_1 W_{m'} + c_0 W_{\text{cyclicNext } m'} = B_{\text{cyclicNext } m'}$, this is defined via
`cyclicBidiagSolve c1 c0 (fun m => B (cyclicNext m))`. -/
noncomputable def cyclicBidiagPrevSolve {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ) : Fin t1 → ℂ :=
  cyclicBidiagSolve c1 c0 (fun m => B (cyclicNext m))

/-- **Exact Algebraic Inversion for `cyclicBidiagPrevSolve` (`cyclicBidiagPrevSolve_spec`, Theorem 5.1(2) (`thm:deconv`))**:
Whenever $\max(c_0, c_1) > 0$, $\min(c_0, c_1) \ge 0$, and $(\min(c_0, c_1)/\max(c_0, c_1))^{t_1} < 1$,
`cyclicBidiagPrevSolve c0 c1 B` satisfies the backward-shift 2-term cyclic bidiagonal system
$c_0 W_m + c_1 W_{(m-1) \bmod t_1} = B_m$ for all $m \in \text{Fin } t_1$. -/
theorem cyclicBidiagPrevSolve_spec {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ)
    (hcmax : 0 < max c0 c1) (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 < 1) (m : Fin t1) :
    (c0 : ℂ) * cyclicBidiagPrevSolve c0 c1 B m +
      (c1 : ℂ) * cyclicBidiagPrevSolve c0 c1 B (cyclicPrev m) = B m := by
  unfold cyclicBidiagPrevSolve
  have hcmax' : 0 < max c1 c0 := by rwa [max_comm]
  have hcmin' : 0 ≤ min c1 c0 := by rwa [min_comm]
  have hq' : (min c1 c0 / max c1 c0) ^ t1 < 1 := by rwa [min_comm, max_comm]
  have h := cyclicBidiagSolve_spec c1 c0 (fun k => B (cyclicNext k)) hcmax' hcmin' hq' (cyclicPrev m)
  rw [cyclicNext_cyclicPrev] at h
  linear_combination h

/-- **Uniqueness / Left-Inverse Theorem for `cyclicBidiagPrevSolve` (`cyclicBidiagPrevSolve_of_spec`)**:
If $W : \text{Fin } t_1 \to \mathbb{C}$ satisfies $c_0 W_m + c_1 W_{\text{cyclicPrev } m} = B_m$
for all $m \in \text{Fin } t_1$, then `cyclicBidiagPrevSolve c0 c1 B = W`. -/
theorem cyclicBidiagPrevSolve_of_spec {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B W : Fin t1 → ℂ)
    (hcmax : 0 < max c0 c1) (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 < 1)
    (hW : ∀ m : Fin t1, (c0 : ℂ) * W m + (c1 : ℂ) * W (cyclicPrev m) = B m) :
    cyclicBidiagPrevSolve c0 c1 B = W := by
  unfold cyclicBidiagPrevSolve
  have hcmax' : 0 < max c1 c0 := by rwa [max_comm]
  have hcmin' : 0 ≤ min c1 c0 := by rwa [min_comm]
  have hq' : (min c1 c0 / max c1 c0) ^ t1 < 1 := by rwa [min_comm, max_comm]
  apply cyclicBidiagSolve_of_spec c1 c0 (fun m => B (cyclicNext m)) W hcmax' hcmin' hq'
  intro m
  have h := hW (cyclicNext m)
  rw [cyclicPrev_cyclicNext] at h
  linear_combination h

/-- **Uniform $\ell_\infty$ Condition Number Bound for `cyclicBidiagPrevSolve`
(`vecInfNorm_cyclicBidiagPrevSolve_le`, Theorem 5.1(2) (`thm:deconv`))**:
$$\|\text{cyclicBidiagPrevSolve } c_0 \, c_1 \, B\|_\infty \le \frac{t_1}{c_{\max} (1 - q_{\text{ratio}})} \|B\|_\infty.$$ -/
theorem vecInfNorm_cyclicBidiagPrevSolve_le {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ)
    (hcmax : 0 < max c0 c1) (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 < 1) :
    vecInfNorm (cyclicBidiagPrevSolve c0 c1 B) ≤
      ((t1 : ℝ) / (max c0 c1 * (1 - (min c0 c1 / max c0 c1) ^ t1))) * vecInfNorm B := by
  unfold cyclicBidiagPrevSolve
  have hcmax' : 0 < max c1 c0 := by rwa [max_comm]
  have hcmin' : 0 ≤ min c1 c0 := by rwa [min_comm]
  have hq' : (min c1 c0 / max c1 c0) ^ t1 < 1 := by rwa [min_comm, max_comm]
  have h := vecInfNorm_cyclicBidiagSolve_le c1 c0 (fun m => B (cyclicNext m)) hcmax' hcmin' hq'
  simpa [max_comm, min_comm, vecInfNorm_comp_cyclicNext] using h

/-- **Explicit $2.36 \, t_1$ Backward-Shift Deconvolution Conditioning Bound
(`deconvolution_prev_conditioning_le_236_t1_of_bounds`, Theorem 5.1(2) (`thm:deconv`))**:
When $\max(c_0, c_1) \ge 0.49999999$, $\min(c_0, c_1) \ge 0$, and
$(\min(c_0, c_1)/\max(c_0, c_1))^{t_1} \le 0.15$, the backward-shift solver satisfies:
$$\|\text{cyclicBidiagPrevSolve } c_0 \, c_1 \, B\|_\infty \le 2.36 \, t_1 \, \|B\|_\infty.$$ -/
theorem deconvolution_prev_conditioning_le_236_t1_of_bounds {t1 : ℕ} [NeZero t1]
    (c0 c1 : ℝ) (B : Fin t1 → ℂ)
    (hcmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1)
    (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 ≤ (15 / 100 : ℝ)) :
    vecInfNorm (cyclicBidiagPrevSolve c0 c1 B) ≤ (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm B := by
  unfold cyclicBidiagPrevSolve
  have hcmax' : (49999999 / 100000000 : ℝ) ≤ max c1 c0 := by rwa [max_comm]
  have hcmin' : 0 ≤ min c1 c0 := by rwa [min_comm]
  have hq' : (min c1 c0 / max c1 c0) ^ t1 ≤ (15 / 100 : ℝ) := by rwa [min_comm, max_comm]
  have h := deconvolution_conditioning_le_236_t1_of_bounds c1 c0 (fun m => B (cyclicNext m)) hcmax' hcmin' hq'
  simpa [vecInfNorm_comp_cyclicNext] using h

/-! ### 1.3 Unconditional Passband, Stopband, and Conditioning Bounds for `gHat` (Theorem 5.1(1)–(2) (`thm:deconv`), Section 5.1 (`sec:deconv-thm`)) -/

/-- Unconditional passband dominant weight bound at level $(K, p)$ ($p \ge 8$):
for every column $u_2 \in \text{Fin}(r_\ell)$,
$\max(\hat{g}_{\alpha_\ell}(u_2/r_\ell), \hat{g}_{\alpha_\ell}(u_2/r_\ell - 1)) \ge \frac{49999999}{100000000}$
(Theorem 5.1(1) (`thm:deconv`), equation (20) (`eq:passband`)). -/
theorem gHat_passband_max_ge_level {K p : ℕ} (hp : 8 ≤ p) (u2 : Fin (rEll K)) :
    (49999999 / 100000000 : ℝ) ≤
      max (gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ)))
          (gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1)) := by
  unfold alphaEll
  have hpWork : 8 ≤ pWorkEll K p := by unfold pWorkEll; omega
  have hr_pos : (0 : ℝ) < (rEll K : ℝ) := Nat.cast_pos.mpr (rEll_pos K)
  have hy0 : 0 ≤ (u2.val : ℝ) / (rEll K : ℝ) := div_nonneg (Nat.cast_nonneg _) hr_pos.le
  have hy1 : (u2.val : ℝ) / (rEll K : ℝ) ≤ 1 :=
    div_le_one_of_le₀ (Nat.cast_le.mpr u2.isLt.le) hr_pos.le
  exact gHat_passband_max_ge (pWorkEll K p) hpWork ((u2.val : ℝ) / (rEll K : ℝ)) hy0 hy1

/-- Unconditional passband non-negativity at level $(K, p)$:
for every column $u_2 \in \text{Fin}(r_\ell)$,
$0 \le \min(\hat{g}_{\alpha_\ell}(u_2/r_\ell), \hat{g}_{\alpha_\ell}(u_2/r_\ell - 1))$. -/
theorem gHat_passband_min_nonneg_level (K p : ℕ) (u2 : Fin (rEll K)) :
    0 ≤ min (gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ)))
            (gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1)) := by
  unfold alphaEll
  have halpha : 0 ≤ alphaFromPWork (pWorkEll K p) :=
    (alphaFromPWork_pos (by unfold pWorkEll; omega)).le
  exact le_min (gHat_nonneg _ halpha _) (gHat_nonneg _ halpha _)

/-- **Unconditional Level-$(K, p)$ Stopband Alias Tail Bound (`gHat_stopband_alias_lt_level`,
Theorem 5.1(1) (`thm:deconv`), equation (21) (`eq:stopband`))**:
For all $K \in \mathbb{N}$, $p \ge 8$, and every column $u_2 \in \text{Fin}(r_\ell)$,
$$1 - \hat{g}_{\alpha_\ell}(u_2 / r_\ell) - \hat{g}_{\alpha_\ell}(u_2 / r_\ell - 1) < 0.15 \cdot 2^{-p_{\text{work},\ell}}.$$ -/
theorem gHat_stopband_alias_lt_level {K p : ℕ} (hp : 8 ≤ p) (u2 : Fin (rEll K)) :
    1 - gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ)) -
      gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1) <
      (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ)) := by
  unfold alphaEll
  have hpWork : 8 ≤ pWorkEll K p := by unfold pWorkEll; omega
  have hr_pos : (0 : ℝ) < (rEll K : ℝ) := Nat.cast_pos.mpr (rEll_pos K)
  have hy0 : 0 ≤ (u2.val : ℝ) / (rEll K : ℝ) := div_nonneg (Nat.cast_nonneg _) hr_pos.le
  have hy1 : (u2.val : ℝ) / (rEll K : ℝ) ≤ 1 :=
    div_le_one_of_le₀ (Nat.cast_le.mpr u2.isLt.le) hr_pos.le
  exact gHat_stopband_alias_lt (pWorkEll K p) hpWork ((u2.val : ℝ) / (rEll K : ℝ)) hy0 hy1

/-- Non-negativity of the stopband alias tail $1 - c_0(u_2) - c_1(u_2) \ge 0$ at level $(K, p)$. -/
theorem gHat_stopband_alias_nonneg_level (K p : ℕ) (u2 : Fin (rEll K)) :
    0 ≤ 1 - gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ)) -
      gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1) := by
  rw [gHat_symm_one, one_sub_gHat_sub_gHat_one_sub]
  have h1 := erfc_nonneg (Real.sqrt Real.pi * alphaEll K p * ((u2.val : ℝ) / (rEll K : ℝ) + 1 / 2))
  have h2 := erfc_nonneg (Real.sqrt Real.pi * alphaEll K p * (3 / 2 - (u2.val : ℝ) / (rEll K : ℝ)))
  linarith

/-- **Unconditional Exact Algebraic Inversion for `gHat` (`gHat_cyclicBidiagSolve_spec`,
Theorem 5.1(2) (`thm:deconv`))**:
For $K \ge 2$, $p \ge 8$, and any non-Nyquist column $u_2 \in \text{Fin}(r_\ell)$ with
$u_2 \ne r_\ell / 2$, `cyclicBidiagSolve` with the Sinc-Gaussian passband weights
$c_0 = \hat{g}_{\alpha_\ell}(u_2/r_\ell)$ and $c_1 = \hat{g}_{\alpha_\ell}(u_2/r_\ell - 1)$
satisfies the 2-term cyclic bidiagonal system unconditionally. -/
theorem gHat_cyclicBidiagSolve_spec {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2)
    (B : Fin (t1Ell K) → ℂ) (m : Fin (t1Ell K)) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    let c0 := gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ))
    let c1 := gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1)
    (c0 : ℂ) * cyclicBidiagSolve c0 c1 B m +
      (c1 : ℂ) * cyclicBidiagSolve c0 c1 B (cyclicNext m) = B m := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  intro c0 c1
  have hcmax : 0 < max c0 c1 :=
    lt_of_lt_of_le (by norm_num) (gHat_passband_max_ge_level hp u2)
  have hcmin : 0 ≤ min c0 c1 := gHat_passband_min_nonneg_level K p u2
  have hq : (min c0 c1 / max c0 c1) ^ (t1Ell K) < 1 :=
    lt_of_le_of_lt (gHat_ratio_pow_t1_le_015 K p hK hp u2 hu2) (by norm_num)
  exact cyclicBidiagSolve_spec c0 c1 B hcmax hcmin hq m

/-- **Unconditional Exact Backward-Shift Inversion for `gHat` (`gHat_cyclicBidiagPrevSolve_spec`,
Theorem 5.1(2) (`thm:deconv`))**:
For $K \ge 2$, $p \ge 8$, and any non-Nyquist column $u_2 \in \text{Fin}(r_\ell)$ with
$u_2 \ne r_\ell / 2$, `cyclicBidiagPrevSolve` with the Sinc-Gaussian passband weights
$c_0 = \hat{g}_{\alpha_\ell}(u_2/r_\ell)$ and $c_1 = \hat{g}_{\alpha_\ell}(u_2/r_\ell - 1)$
satisfies the backward-shift system $c_0 W_m + c_1 W_{(m-1) \bmod t_1} = B_m$ unconditionally. -/
theorem gHat_cyclicBidiagPrevSolve_spec {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2)
    (B : Fin (t1Ell K) → ℂ) (m : Fin (t1Ell K)) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    let c0 := gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ))
    let c1 := gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1)
    (c0 : ℂ) * cyclicBidiagPrevSolve c0 c1 B m +
      (c1 : ℂ) * cyclicBidiagPrevSolve c0 c1 B (cyclicPrev m) = B m := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  intro c0 c1
  have hcmax : 0 < max c0 c1 :=
    lt_of_lt_of_le (by norm_num) (gHat_passband_max_ge_level hp u2)
  have hcmin : 0 ≤ min c0 c1 := gHat_passband_min_nonneg_level K p u2
  have hq : (min c0 c1 / max c0 c1) ^ (t1Ell K) < 1 :=
    lt_of_le_of_lt (gHat_ratio_pow_t1_le_015 K p hK hp u2 hu2) (by norm_num)
  exact cyclicBidiagPrevSolve_spec c0 c1 B hcmax hcmin hq m

/-- **Unconditional Deconvolution Conditioning Bound for `gHat`
(`gHat_deconvolution_conditioning_le_236_t1`, Theorem 5.1(2) (`thm:deconv`), equation (24) (`eq:B-inv-norm`))**:
For $K \ge 2$, $p \ge 8$, and any non-Nyquist column $u_2 \in \text{Fin}(r_\ell)$ with
$u_2 \ne r_\ell / 2$, the Sinc-Gaussian passband weights
$c_0 = \hat{g}_{\alpha_\ell}(u_2/r_\ell)$ and $c_1 = \hat{g}_{\alpha_\ell}(u_2/r_\ell - 1)$
satisfy $\|\text{cyclicBidiagSolve } c_0 \, c_1 \, B\|_\infty \le 2.36 \, t_{1,\ell} \, \|B\|_\infty$. -/
theorem gHat_deconvolution_conditioning_le_236_t1 {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2) (B : Fin (t1Ell K) → ℂ) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    let c0 := gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ))
    let c1 := gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1)
    vecInfNorm (cyclicBidiagSolve c0 c1 B) ≤
      (236 / 100 : ℝ) * (t1Ell K : ℝ) * vecInfNorm B := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  intro c0 c1
  exact deconvolution_conditioning_le_236_t1_of_bounds c0 c1 B
    (gHat_passband_max_ge_level hp u2)
    (gHat_passband_min_nonneg_level K p u2)
    (gHat_ratio_pow_t1_le_015 K p hK hp u2 hu2)

/-- **Unconditional Backward-Shift Deconvolution Conditioning Bound for `gHat`
(`gHat_deconvolution_prev_conditioning_le_236_t1`, Theorem 5.1(2) (`thm:deconv`), equation (24) (`eq:B-inv-norm`))**:
For $K \ge 2$, $p \ge 8$, and any non-Nyquist column $u_2 \in \text{Fin}(r_\ell)$ with
$u_2 \ne r_\ell / 2$, the Sinc-Gaussian passband weights
$c_0 = \hat{g}_{\alpha_\ell}(u_2/r_\ell)$ and $c_1 = \hat{g}_{\alpha_\ell}(u_2/r_\ell - 1)$
satisfy $\|\text{cyclicBidiagPrevSolve } c_0 \, c_1 \, B\|_\infty \le 2.36 \, t_{1,\ell} \, \|B\|_\infty$. -/
theorem gHat_deconvolution_prev_conditioning_le_236_t1 {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2) (B : Fin (t1Ell K) → ℂ) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    let c0 := gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ))
    let c1 := gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1)
    vecInfNorm (cyclicBidiagPrevSolve c0 c1 B) ≤
      (236 / 100 : ℝ) * (t1Ell K : ℝ) * vecInfNorm B := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  intro c0 c1
  exact deconvolution_prev_conditioning_le_236_t1_of_bounds c0 c1 B
    (gHat_passband_max_ge_level hp u2)
    (gHat_passband_min_nonneg_level K p u2)
    (gHat_ratio_pow_t1_le_015 K p hK hp u2 hu2)

/-! ## 3. Passband/Stopband Decay & Ratio Bounds (Theorem 5.1(1)–(2) (`thm:deconv`)) -/

/-- Rational lower bound $\ln 2 > 0.693147$ from `Real.log_two_gt_d9`. -/
theorem log_two_gt_693147 : (693147 / 1000000 : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

/-- Rational upper bound $\pi < 3.141593$ from `Real.pi_lt_d6`. -/
theorem pi_lt_3141593 : Real.pi < (3141593 / 1000000 : ℝ) := by
  have h := Real.pi_lt_d6
  linarith

/-- Rational lower bound $\pi > 3.141592$ from `Real.pi_gt_d6`. -/
theorem pi_gt_3141592 : (3141592 / 1000000 : ℝ) < Real.pi := by
  have h := Real.pi_gt_d6
  linarith

/-- For all $p_{\text{work}} \ge 8$, the Sinc-Gaussian shape parameter satisfies
$\alpha = 2\sqrt{p_{\text{work}} \ln 2 / \pi} \ge 2.65$ (Section 5.1 (`sec:deconv-thm`)). -/
theorem alphaFromPWork_ge_265 {pWork : ℕ} (hp : 8 ≤ pWork) :
    (265 / 100 : ℝ) ≤ alphaFromPWork pWork := by
  unfold alphaFromPWork
  have hp_cast : (8 : ℝ) ≤ (pWork : ℝ) := by exact_mod_cast hp
  have hln2 := log_two_gt_693147
  have hpi := pi_lt_3141593
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hquot : (175625 / 100000 : ℝ) ≤ ((pWork : ℝ) * Real.log 2) / Real.pi := by
    rw [le_div_iff₀ hpi_pos]
    nlinarith
  have hsqrt : (265 / 200 : ℝ) ≤ Real.sqrt (((pWork : ℝ) * Real.log 2) / Real.pi) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 265 / 200)]
    apply Real.sqrt_le_sqrt
    linarith
  linarith

/-- For all $p_{\text{work}} \ge 12$, the Sinc-Gaussian shape parameter satisfies
$\alpha = 2\sqrt{p_{\text{work}} \ln 2 / \pi} \ge 3.25$ (Section 5.1 (`sec:deconv-thm`)). -/
theorem alphaFromPWork_ge_325 {pWork : ℕ} (hp : 12 ≤ pWork) :
    (325 / 100 : ℝ) ≤ alphaFromPWork pWork := by
  unfold alphaFromPWork
  have hp_cast : (12 : ℝ) ≤ (pWork : ℝ) := by exact_mod_cast hp
  have hln2 := log_two_gt_693147
  have hpi := pi_lt_3141593
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hquot : (2640625 / 1000000 : ℝ) ≤ ((pWork : ℝ) * Real.log 2) / Real.pi := by
    rw [le_div_iff₀ hpi_pos]
    nlinarith
  have hsqrt : (325 / 200 : ℝ) ≤ Real.sqrt (((pWork : ℝ) * Real.log 2) / Real.pi) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 325 / 200)]
    apply Real.sqrt_le_sqrt
    linarith
  linarith

/-- Taylor lower bound $1 + x + x^2/2 + x^3/6 + x^4/24 \le e^x$ for all $x \ge 0$. -/
theorem quartic_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ Real.exp x := by
  have hsum := Real.sum_le_exp_of_nonneg hx 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hsum
  linarith

/-- Exponential decay bound: for all $\alpha \ge 2.65$ (and in particular for $\alpha \ge 4.7$
or any $p_{\text{work}} \ge 8$), $\exp(-0.74 \alpha) < 0.15$ (Theorem 5.1(2) (`thm:deconv`),
equation (22) (`eq:wrap-bound`)). -/
theorem exp_neg_074_alpha_lt_015 {α : ℝ} (hα : (265 / 100 : ℝ) ≤ α) :
    Real.exp (-(74 / 100 : ℝ) * α) < (15 / 100 : ℝ) := by
  set x : ℝ := (74 / 100 : ℝ) * α
  have hx : (1961 / 1000 : ℝ) ≤ x := by
    simp only [x]
    linarith
  have hx_nonneg : 0 ≤ x := by linarith
  have hexp_ge : (20 / 3 : ℝ) < Real.exp x := by
    have hq := quartic_le_exp_of_nonneg hx_nonneg
    have hpow2 : (1961 / 1000 : ℝ) ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hx 2
    have hpow3 : (1961 / 1000 : ℝ) ^ 3 ≤ x ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx 3
    have hpow4 : (1961 / 1000 : ℝ) ^ 4 ≤ x ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hx 4
    linarith
  have hneg : -(74 / 100 : ℝ) * α = -x := by ring
  rw [hneg, Real.exp_neg]
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  rw [inv_lt_iff_one_lt_mul₀ hexp_pos]
  linarith

/-- Corollary for $\alpha \ge 4.7$: $\exp(-0.74 \alpha) < 0.15$. -/
theorem exp_neg_074_alpha_lt_015_of_ge_47 {α : ℝ} (hα : (47 / 10 : ℝ) ≤ α) :
    Real.exp (-(74 / 100 : ℝ) * α) < (15 / 100 : ℝ) :=
  exp_neg_074_alpha_lt_015 (by linarith)

/-! ## 4. Nyquist Mode $u_2 = r/2$ Exact Algebraic Cancellation (Theorem 5.1(3) (`thm:deconv`), Section 5.1 (`sec:deconv-thm`)) -/

/-- Natural-number power identity `(expTwoPiI x) ^ k = expTwoPiI (k * x)`. -/
theorem expTwoPiI_pow (x : ℝ) (k : ℕ) :
    (expTwoPiI x) ^ k = expTwoPiI ((k : ℝ) * x) := by
  unfold expTwoPiI
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Half-period value `expTwoPiI (1 / 2) = -1`. -/
@[simp]
theorem expTwoPiI_one_half : expTwoPiI (1 / 2 : ℝ) = -1 := by
  unfold expTwoPiI
  have h : 2 * Real.pi * ((1 / 2 : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_pi_mul_I]

/-- Quarter-period value `expTwoPiI (1 / 4) = i`. -/
@[simp]
theorem expTwoPiI_one_fourth : expTwoPiI (1 / 4 : ℝ) = Complex.I := by
  unfold expTwoPiI
  have h : 2 * Real.pi * ((1 / 4 : ℝ) : ℂ) * Complex.I = (Real.pi / 2) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_pi_div_two_mul_I]

/-- Alternating half-integer phase `expTwoPiI (j2 / 2) = (-1) ^ j2`. -/
theorem expTwoPiI_nat_div_two (j2 : ℕ) :
    expTwoPiI ((j2 : ℝ) / 2) = (-1 : ℂ) ^ j2 := by
  have h : (j2 : ℝ) / 2 = (j2 : ℝ) * (1 / 2 : ℝ) := by ring
  rw [h, ← expTwoPiI_pow, expTwoPiI_one_half]

/-- Nyquist quarter-plus-half-integer phase `expTwoPiI (1/4 + j2/2) = i * (-1) ^ j2`
(Section 5.1 (`sec:deconv-thm`), proof of Theorem 5.1(3) (`thm:deconv`)). -/
theorem expTwoPiI_one_fourth_add_div_two (j2 : ℕ) :
    expTwoPiI ((1 / 4 : ℝ) + (j2 : ℝ) / 2) = Complex.I * (-1 : ℂ) ^ j2 := by
  rw [expTwoPiI_add, expTwoPiI_one_fourth, expTwoPiI_nat_div_two]

/-- Character orthogonality on $\mathbb{Z}_{t_1}$ at the Nyquist sign $(-1)^{u_1}$
(Section 5.1 (`sec:deconv-thm`), proof of Theorem 5.1(3) (`thm:deconv`)):
For $t_1 = 2 h_1$ with $h_1 \ge 1$ and $j_1 \in \text{Fin } t_1$:
$$\sum_{u_1 : \text{Fin } t_1} (-1)^{u_1} e^{2\pi i j_1 u_1 / t_1} = \begin{cases} t_1 & \text{if } j_1 = h_1, \\ 0 & \text{otherwise.} \end{cases}$$ -/
theorem sum_alternating_expTwoPiI_eq {h1 : ℕ} (hh1 : 0 < h1) (j1 : Fin (2 * h1)) :
    (∑ u1 : Fin (2 * h1),
      (-1 : ℂ) ^ u1.val * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ))) =
      if j1.val = h1 then ((2 * h1 : ℕ) : ℂ) else 0 := by
  have ht1_pos : (0 : ℝ) < ((2 * h1 : ℕ) : ℝ) := by positivity
  set w : ℂ := -expTwoPiI ((j1.val : ℝ) / ((2 * h1 : ℕ) : ℝ))
  have hterm : ∀ u1 : Fin (2 * h1),
      (-1 : ℂ) ^ u1.val * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ)) =
        w ^ u1.val := by
    intro u1
    have hdiv : ((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ) =
        (u1.val : ℝ) * ((j1.val : ℝ) / ((2 * h1 : ℕ) : ℝ)) := by
      push_cast
      ring
    rw [hdiv, ← expTwoPiI_pow, ← mul_pow, neg_one_mul]
  have hsum_range :
      (∑ u1 : Fin (2 * h1),
        (-1 : ℂ) ^ u1.val * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ))) =
      ∑ u1 ∈ Finset.range (2 * h1), w ^ u1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun u => w ^ u) (2 * h1)]
    exact Finset.sum_congr rfl (fun u1 _ => hterm u1)
  rw [hsum_range]
  split_ifs with hj1
  · have hw1 : w = 1 := by
      simp only [w, hj1]
      have hhalf : (h1 : ℝ) / ((2 * h1 : ℕ) : ℝ) = (1 / 2 : ℝ) := by
        have hh1_ne : (h1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hh1)
        push_cast
        field_simp
      rw [hhalf, expTwoPiI_one_half, neg_neg]
    simp [hw1]
  · have hw_pow : w ^ (2 * h1) = 1 := by
      simp only [w]
      rw [neg_pow, Even.neg_one_pow ⟨h1, by ring⟩, one_mul, expTwoPiI_pow]
      have hmul : ((2 * h1 : ℕ) : ℝ) * ((j1.val : ℝ) / ((2 * h1 : ℕ) : ℝ)) =
          (0 : ℝ) + ((j1.val : ℤ) : ℝ) := by
        have ht1_ne : ((2 * h1 : ℕ) : ℝ) ≠ 0 := ne_of_gt ht1_pos
        push_cast
        field_simp
        ring
      rw [hmul, expTwoPiI_add_int]
      simp [expTwoPiI]
    have hw_ne_one : w ≠ 1 := by
      intro hw1
      have hexp : expTwoPiI ((j1.val : ℝ) / ((2 * h1 : ℕ) : ℝ) + (1 / 2 : ℝ)) = 1 := by
        rw [expTwoPiI_add, expTwoPiI_one_half, mul_neg_one]
        exact hw1
      unfold expTwoPiI at hexp
      rw [Complex.exp_eq_one_iff] at hexp
      rcases hexp with ⟨m, hm⟩
      have hpi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hm_eq : (((j1.val : ℝ) / ((2 * h1 : ℕ) : ℝ) + (1 / 2 : ℝ) : ℝ) : ℂ) *
          (2 * Real.pi * Complex.I) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
        calc
          (((j1.val : ℝ) / ((2 * h1 : ℕ) : ℝ) + (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
            = 2 * Real.pi * (((j1.val : ℝ) / ((2 * h1 : ℕ) : ℝ) + (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.I := by ring
          _ = (m : ℂ) * (2 * Real.pi * Complex.I) := hm
      have hreal : (j1.val : ℝ) / ((2 * h1 : ℕ) : ℝ) + (1 / 2 : ℝ) = (m : ℝ) := by
        exact_mod_cast mul_right_cancel₀ hpi_ne hm_eq
      have hmul2 : (j1.val : ℝ) + (h1 : ℝ) = (m : ℝ) * (2 * (h1 : ℝ)) := by
        have hcast_t1 : ((2 * h1 : ℕ) : ℝ) = 2 * (h1 : ℝ) := by push_cast; ring
        rw [hcast_t1] at hreal
        have hh1_ne : (h1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hh1)
        calc
          (j1.val : ℝ) + (h1 : ℝ)
            = ((j1.val : ℝ) / (2 * (h1 : ℝ)) + (1 / 2 : ℝ)) * (2 * (h1 : ℝ)) := by
              field_simp
          _ = (m : ℝ) * (2 * (h1 : ℝ)) := by rw [hreal]
      have hint : (j1.val : ℤ) + (h1 : ℤ) = m * (2 * (h1 : ℤ)) := by
        exact_mod_cast hmul2
      have hj1_lt : (j1.val : ℤ) < 2 * (h1 : ℤ) := by exact_mod_cast j1.isLt
      have hj1_nn : (0 : ℤ) ≤ (j1.val : ℤ) := Int.natCast_nonneg j1.val
      have hh1_pos_z : (0 : ℤ) < (h1 : ℤ) := by exact_mod_cast hh1
      have hm_gt : 0 < m := by nlinarith
      have hm_lt : m < 2 := by nlinarith
      have hm_one : m = 1 := by omega
      rw [hm_one] at hint
      have hj1_eq : j1.val = h1 := by omega
      exact hj1 hj1_eq
    rw [geom_sum_eq hw_ne_one, hw_pow, sub_self, zero_div]

/-- **Exact Nyquist Mode $u_2 = r/2$ Alternating-Sum Identity (`nyquist_alternating_sum_eq`,
Theorem 5.1(3) (`thm:deconv`), equation (25) (`eq:nyquist-id`))**:
For $t_1 = 2 h_1$ ($h_1 \ge 1$), $r = 2 h_2$ ($h_2 \ge 1$), and $R = t_1 r$, at the Nyquist column
$u_2 = h_2 = r / 2$, the alternating sum of $Z_{u_1} = (F_R x)_{r/2 + r u_1}$ is given with zero
multiplications by:
$$\sum_{u_1=0}^{t_1-1} (-1)^{u_1} Z_{u_1} = \frac{i}{r} \sum_{j_2=0}^{r-1} (-1)^{j_2} x(t_1/2 + t_1 j_2).$$ -/
theorem nyquist_alternating_sum_eq {h1 h2 : ℕ} (hh1 : 0 < h1) (hh2 : 0 < h2)
    (x : Fin ((2 * h1) * (2 * h2)) → ℂ) :
    (∑ u1 : Fin (2 * h1),
      (-1 : ℂ) ^ u1.val *
        normDFT1D x ⟨h2 + (2 * h2) * u1.val, by have := u1.isLt; nlinarith⟩) =
      (Complex.I / ((2 * h2 : ℕ) : ℂ)) *
        ∑ j2 : Fin (2 * h2),
          (-1 : ℂ) ^ j2.val * x ⟨h1 + (2 * h1) * j2.val, by have := j2.isLt; nlinarith⟩ := by
  have ht1_pos : 0 < 2 * h1 := by positivity
  have hr_pos : 0 < 2 * h2 := by positivity
  have hR_pos : 0 < (2 * h1) * (2 * h2) := mul_pos ht1_pos hr_pos
  -- Bijection `(j1, j2) ↦ j1 + (2 * h1) * j2` between `Fin (2 * h1) × Fin (2 * h2)` and `Fin ((2 * h1) * (2 * h2))`
  let pairToFin : Fin (2 * h1) × Fin (2 * h2) ≃ Fin ((2 * h1) * (2 * h2)) :=
    { toFun := fun p => ⟨p.1.val + (2 * h1) * p.2.val, by
        have h1' := p.1.isLt
        have h2' := p.2.isLt
        nlinarith⟩
      invFun := fun j =>
        (⟨j.val % (2 * h1), Nat.mod_lt _ ht1_pos⟩,
         ⟨j.val / (2 * h1),
          (Nat.div_lt_iff_lt_mul ht1_pos).mpr (by have := j.isLt; linarith)⟩)
      left_inv := fun ⟨j1, j2⟩ => by
        ext
        · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j1.isLt]
        · simp [Nat.add_mul_div_left _ _ ht1_pos, Nat.div_eq_of_lt j1.isLt]
      right_inv := fun j => by
        ext
        simp [Nat.mod_add_div] }
  have hphase : ∀ (j1 : Fin (2 * h1)) (j2 : Fin (2 * h2)) (u1 : Fin (2 * h1)),
      expTwoPiI ((((j1.val + (2 * h1) * j2.val) * (h2 + (2 * h2) * u1.val) : ℕ) : ℝ) /
        (((2 * h1) * (2 * h2) : ℕ) : ℝ)) =
        expTwoPiI ((((j1.val + (2 * h1) * j2.val) * h2 : ℕ) : ℝ) /
          (((2 * h1) * (2 * h2) : ℕ) : ℝ)) *
          expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ)) := by
    intro j1 j2 u1
    have ht1_ne : ((2 * h1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ht1_pos)
    have hr_ne : ((2 * h2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hr_pos)
    have hsplit :
        ((((j1.val + (2 * h1) * j2.val) * (h2 + (2 * h2) * u1.val) : ℕ) : ℝ) /
          (((2 * h1) * (2 * h2) : ℕ) : ℝ)) =
        ((((j1.val + (2 * h1) * j2.val) * h2 : ℕ) : ℝ) / (((2 * h1) * (2 * h2) : ℕ) : ℝ) +
          ((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ)) +
          (((j2.val * u1.val : ℕ) : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [hsplit, expTwoPiI_add_int, expTwoPiI_add]
  have hexpand : ∀ u1 : Fin (2 * h1),
      (-1 : ℂ) ^ u1.val *
        normDFT1D x ⟨h2 + (2 * h2) * u1.val, by have := u1.isLt; nlinarith⟩ =
      ((((2 * h1) * (2 * h2) : ℕ) : ℝ)⁻¹ : ℂ) *
        ∑ j1 : Fin (2 * h1), ∑ j2 : Fin (2 * h2),
          x (pairToFin (j1, j2)) *
            expTwoPiI ((((j1.val + (2 * h1) * j2.val) * h2 : ℕ) : ℝ) /
              (((2 * h1) * (2 * h2) : ℕ) : ℝ)) *
            ((-1 : ℂ) ^ u1.val * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ))) := by
    intro u1
    unfold normDFT1D
    rw [← mul_assoc, mul_comm ((-1 : ℂ) ^ u1.val), mul_assoc, Finset.mul_sum]
    congr 1
    rw [← Equiv.sum_comp pairToFin, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j1 _ => Finset.sum_congr rfl (fun j2 _ => ?_))
    simp only [pairToFin, Equiv.coe_fn_mk]
    rw [hphase j1 j2 u1]
    ring
  simp_rw [hexpand, ← Finset.mul_sum]
  have hswap2 :
      (∑ u1 : Fin (2 * h1), ∑ j1 : Fin (2 * h1), ∑ j2 : Fin (2 * h2),
        x (pairToFin (j1, j2)) *
          expTwoPiI ((((j1.val + (2 * h1) * j2.val) * h2 : ℕ) : ℝ) /
            (((2 * h1) * (2 * h2) : ℕ) : ℝ)) *
          ((-1 : ℂ) ^ u1.val * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ)))) =
      ∑ j1 : Fin (2 * h1),
        (∑ j2 : Fin (2 * h2),
          x (pairToFin (j1, j2)) *
            expTwoPiI ((((j1.val + (2 * h1) * j2.val) * h2 : ℕ) : ℝ) /
              (((2 * h1) * (2 * h2) : ℕ) : ℝ))) *
        (∑ u1 : Fin (2 * h1),
          (-1 : ℂ) ^ u1.val * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / ((2 * h1 : ℕ) : ℝ))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j1 _ => ?_)
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j2 _ => ?_)
    rw [← Finset.mul_sum]
  rw [hswap2]
  simp_rw [sum_alternating_expTwoPiI_eq hh1]
  let h1Fin : Fin (2 * h1) := ⟨h1, by omega⟩
  have hfin_eq : ∀ j1 : Fin (2 * h1), (j1.val = h1) ↔ (j1 = h1Fin) := by
    intro j1
    constructor
    · intro h
      ext
      exact h
    · intro h
      exact congrArg Fin.val h
  simp_rw [hfin_eq, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hnyq_phase : ∀ j2 : Fin (2 * h2),
      expTwoPiI ((((h1Fin.val + (2 * h1) * j2.val) * h2 : ℕ) : ℝ) /
        (((2 * h1) * (2 * h2) : ℕ) : ℝ)) =
        Complex.I * (-1 : ℂ) ^ j2.val := by
    intro j2
    have hfrac : (((h1Fin.val + (2 * h1) * j2.val) * h2 : ℕ) : ℝ) /
        (((2 * h1) * (2 * h2) : ℕ) : ℝ) =
        (1 / 4 : ℝ) + (j2.val : ℝ) / 2 := by
      simp only [h1Fin]
      have hh1_ne : (h1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hh1)
      have hh2_ne : (h2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hh2)
      push_cast
      field_simp
      ring
    rw [hfrac, expTwoPiI_one_fourth_add_div_two]
  simp_rw [hnyq_phase]
  have hpull :
      (∑ j2 : Fin (2 * h2), x (pairToFin (h1Fin, j2)) * (Complex.I * (-1 : ℂ) ^ j2.val)) =
      Complex.I * ∑ j2 : Fin (2 * h2), (-1 : ℂ) ^ j2.val * x (pairToFin (h1Fin, j2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j2 _ => by ring)
  rw [hpull]
  have ht1_ne : ((2 * h1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ht1_pos)
  have hr_ne : ((2 * h2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hr_pos)
  have hR_cast : ((((2 * h1) * (2 * h2) : ℕ) : ℝ)⁻¹ : ℂ) =
      (((2 * h1 : ℕ) : ℂ) * ((2 * h2 : ℕ) : ℂ))⁻¹ := by
    push_cast
    rfl
  rw [hR_cast]
  simp only [pairToFin, h1Fin, Equiv.coe_fn_mk]
  field_simp

/-- Auxiliary recursive definition of the Nyquist open-chain particular solution
(Section 5.1 (`sec:deconv-thm`) and Section 5.2 (`sec:solvers`)):
$Z^{\text{part}}_0 = 0$ and $Z^{\text{part}}_{k+1} = c_0^{-1} B_{k+1} - Z^{\text{part}}_k$. -/
noncomputable def nyquistOpenChainParticularAux {t1 : ℕ} (c0 : ℝ) (B : Fin t1 → ℂ) :
    (k : ℕ) → k < t1 → ℂ
  | 0, _ => 0
  | k + 1, hk =>
    (c0 : ℂ)⁻¹ * B ⟨k + 1, hk⟩ - nyquistOpenChainParticularAux c0 B k (Nat.lt_of_succ_lt hk)

/-- Nyquist open-chain particular solution $Z^{\text{part}}_{u_1}$ for $u_1 \in \text{Fin } t_1$
(Theorem 5.1(3) (`thm:deconv`), Section 5.2 (`sec:solvers`)):
$$Z^{\text{part}}_0 = 0, \qquad Z^{\text{part}}_{u_1} = c_0^{-1} B_{u_1} - Z^{\text{part}}_{u_1 - 1}
= \frac{1}{c_0} \sum_{s=1}^{u_1} (-1)^{u_1 - s} B_s.$$ -/
noncomputable def nyquistOpenChainParticular {t1 : ℕ} (c0 : ℝ) (B : Fin t1 → ℂ)
    (u1 : Fin t1) : ℂ :=
  nyquistOpenChainParticularAux c0 B u1.val u1.isLt

/-- Base case $Z^{\text{part}}_0 = 0$ for `nyquistOpenChainParticular`. -/
@[simp]
theorem nyquistOpenChainParticular_zero {t1 : ℕ} (ht1 : 0 < t1) (c0 : ℝ) (B : Fin t1 → ℂ) :
    nyquistOpenChainParticular c0 B ⟨0, ht1⟩ = 0 := rfl

/-- Step recurrence for `nyquistOpenChainParticular` at index $k + 1 < t_1$. -/
theorem nyquistOpenChainParticular_succ {t1 : ℕ} (c0 : ℝ) (B : Fin t1 → ℂ)
    (k : ℕ) (hk : k + 1 < t1) :
    nyquistOpenChainParticular c0 B ⟨k + 1, hk⟩ =
      (c0 : ℂ)⁻¹ * B ⟨k + 1, hk⟩ -
        nyquistOpenChainParticular c0 B ⟨k, Nat.lt_of_succ_lt hk⟩ := rfl

/-- **Nyquist Open-Chain Particular Solution Recurrence (`nyquistOpenChainParticular_recurrence`,
Theorem 5.1(3) (`thm:deconv`))**:
For $1 \le u_1 < t_1$ and $c_0 \ne 0$, the open-chain particular solution satisfies:
$$c_0 Z^{\text{part}}_{u_1} + c_0 Z^{\text{part}}_{u_1 - 1} = B_{u_1}.$$ -/
theorem nyquistOpenChainParticular_recurrence {t1 : ℕ} [NeZero t1] {c0 : ℝ} (hc0 : c0 ≠ 0)
    (B : Fin t1 → ℂ) (u1 : Fin t1) (hu1 : 0 < u1.val) :
    (c0 : ℂ) * nyquistOpenChainParticular c0 B u1 +
      (c0 : ℂ) * nyquistOpenChainParticular c0 B (cyclicPrev u1) = B u1 := by
  have hc0_c : (c0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0
  obtain ⟨k, hk_eq⟩ : ∃ k, u1.val = k + 1 := ⟨u1.val - 1, by omega⟩
  have hk_lt : k + 1 < t1 := hk_eq ▸ u1.isLt
  have hu1_eq : u1 = ⟨k + 1, hk_lt⟩ := by
    ext
    exact hk_eq
  have hprev_eq : cyclicPrev u1 = ⟨k, Nat.lt_of_succ_lt hk_lt⟩ := by
    rw [cyclicPrev_eq_sub_one_of_pos u1 hu1]
    ext
    dsimp
    omega
  rw [hprev_eq, hu1_eq, nyquistOpenChainParticular_succ]
  calc
    (c0 : ℂ) * ((c0 : ℂ)⁻¹ * B ⟨k + 1, hk_lt⟩ -
        nyquistOpenChainParticular c0 B ⟨k, Nat.lt_of_succ_lt hk_lt⟩) +
      (c0 : ℂ) * nyquistOpenChainParticular c0 B ⟨k, Nat.lt_of_succ_lt hk_lt⟩
      = ((c0 : ℂ) * (c0 : ℂ)⁻¹) * B ⟨k + 1, hk_lt⟩ := by ring
    _ = B ⟨k + 1, hk_lt⟩ := by rw [mul_inv_cancel₀ hc0_c, one_mul]

/-- Alternating-sign prefix $P_{u_1} = (-1)^{u_1} Z^{\text{part}}_{u_1}$ of the Nyquist
open-chain particular solution (Section 5.1 (`sec:deconv-thm`)). -/
noncomputable def nyquistAlternatingPrefix {t1 : ℕ} (c0 : ℝ) (B : Fin t1 → ℂ)
    (u1 : Fin t1) : ℂ :=
  (-1 : ℂ) ^ u1.val * nyquistOpenChainParticular c0 B u1

@[simp]
theorem nyquistAlternatingPrefix_zero {t1 : ℕ} (ht1 : 0 < t1) (c0 : ℝ) (B : Fin t1 → ℂ) :
    nyquistAlternatingPrefix c0 B ⟨0, ht1⟩ = 0 := by
  simp [nyquistAlternatingPrefix]

theorem nyquistAlternatingPrefix_succ {t1 : ℕ} (c0 : ℝ) (B : Fin t1 → ℂ)
    (k : ℕ) (hk : k + 1 < t1) :
    nyquistAlternatingPrefix c0 B ⟨k + 1, hk⟩ =
      nyquistAlternatingPrefix c0 B ⟨k, Nat.lt_of_succ_lt hk⟩ +
        (-1 : ℂ) ^ (k + 1) * (c0 : ℂ)⁻¹ * B ⟨k + 1, hk⟩ := by
  simp only [nyquistAlternatingPrefix, nyquistOpenChainParticular_succ]
  rw [pow_succ (-1 : ℂ) k]
  ring

/-- Pairwise distance bound on `nyquistAlternatingPrefix`: for any $j$ and $d$ with $j + d < t_1$
and $0 < c_0$, the alternating prefix changes by at most $d \cdot c_0^{-1} \|B\|_\infty$. -/
theorem norm_nyquistAlternatingPrefix_add_sub_le {t1 : ℕ} {c0 : ℝ} (hc0 : 0 < c0)
    (B : Fin t1 → ℂ) (j d : ℕ) (hjd : j + d < t1) :
    ‖nyquistAlternatingPrefix c0 B ⟨j + d, hjd⟩ -
      nyquistAlternatingPrefix c0 B ⟨j, by omega⟩‖ ≤
      (d : ℝ) * (c0⁻¹ * vecInfNorm B) := by
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hjd' : j + d < t1 := by omega
    have hstep :
        nyquistAlternatingPrefix c0 B ⟨j + (d + 1), hjd⟩ -
          nyquistAlternatingPrefix c0 B ⟨j, by omega⟩ =
        (nyquistAlternatingPrefix c0 B ⟨j + d, hjd'⟩ -
          nyquistAlternatingPrefix c0 B ⟨j, by omega⟩) +
          (-1 : ℂ) ^ (j + d + 1) * (c0 : ℂ)⁻¹ * B ⟨j + d + 1, hjd⟩ := by
      have heq : (⟨j + (d + 1), hjd⟩ : Fin t1) = ⟨(j + d) + 1, hjd⟩ := by
        ext
        dsimp
        omega
      rw [heq, nyquistAlternatingPrefix_succ]
      ring
    rw [hstep]
    have hnorm_term :
        ‖(-1 : ℂ) ^ (j + d + 1) * (c0 : ℂ)⁻¹ * B ⟨j + d + 1, hjd⟩‖ ≤
          c0⁻¹ * vecInfNorm B := by
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        norm_inv, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hc0)]
      exact mul_le_mul_of_nonneg_left (norm_le_vecInfNorm B ⟨j + d + 1, hjd⟩) (by positivity)
    calc
      ‖(nyquistAlternatingPrefix c0 B ⟨j + d, hjd'⟩ -
          nyquistAlternatingPrefix c0 B ⟨j, by omega⟩) +
          (-1 : ℂ) ^ (j + d + 1) * (c0 : ℂ)⁻¹ * B ⟨j + d + 1, hjd⟩‖
        ≤ ‖nyquistAlternatingPrefix c0 B ⟨j + d, hjd'⟩ -
            nyquistAlternatingPrefix c0 B ⟨j, by omega⟩‖ +
          ‖(-1 : ℂ) ^ (j + d + 1) * (c0 : ℂ)⁻¹ * B ⟨j + d + 1, hjd⟩‖ := norm_add_le _ _
      _ ≤ (d : ℝ) * (c0⁻¹ * vecInfNorm B) + c0⁻¹ * vecInfNorm B :=
          add_le_add (ih hjd') hnorm_term
      _ = ((d + 1 : ℕ) : ℝ) * (c0⁻¹ * vecInfNorm B) := by
          push_cast
          ring

/-- For any two indices $u_1, m \in \text{Fin } t_1$ and $0 < c_0$,
$\|P_{u_1} - P_m\| \le (t_1 / c_0) \|B\|_\infty$. -/
theorem norm_nyquistAlternatingPrefix_sub_le {t1 : ℕ} {c0 : ℝ} (hc0 : 0 < c0)
    (B : Fin t1 → ℂ) (u1 m : Fin t1) :
    ‖nyquistAlternatingPrefix c0 B u1 - nyquistAlternatingPrefix c0 B m‖ ≤
      ((t1 : ℝ) / c0) * vecInfNorm B := by
  have hB_nn : 0 ≤ vecInfNorm B := vecInfNorm_nonneg B
  rcases le_total m.val u1.val with hle | hle
  · set d : ℕ := u1.val - m.val
    have hd_lt : m.val + d < t1 := by
      have : m.val + d = u1.val := by omega
      rw [this]
      exact u1.isLt
    have hu1_eq : u1 = ⟨m.val + d, hd_lt⟩ := by
      ext
      dsimp [d]
      omega
    have hd_le : (d : ℝ) ≤ (t1 : ℝ) := by
      have : d ≤ t1 := by omega
      exact_mod_cast this
    rw [hu1_eq]
    calc
      ‖nyquistAlternatingPrefix c0 B ⟨m.val + d, hd_lt⟩ - nyquistAlternatingPrefix c0 B m‖
        ≤ (d : ℝ) * (c0⁻¹ * vecInfNorm B) :=
          norm_nyquistAlternatingPrefix_add_sub_le hc0 B m.val d hd_lt
      _ ≤ (t1 : ℝ) * (c0⁻¹ * vecInfNorm B) :=
          mul_le_mul_of_nonneg_right hd_le (by positivity)
      _ = ((t1 : ℝ) / c0) * vecInfNorm B := by ring
  · set d : ℕ := m.val - u1.val
    have hd_lt : u1.val + d < t1 := by
      have : u1.val + d = m.val := by omega
      rw [this]
      exact m.isLt
    have hm_eq : m = ⟨u1.val + d, hd_lt⟩ := by
      ext
      dsimp [d]
      omega
    have hd_le : (d : ℝ) ≤ (t1 : ℝ) := by
      have : d ≤ t1 := by omega
      exact_mod_cast this
    rw [norm_sub_rev, hm_eq]
    calc
      ‖nyquistAlternatingPrefix c0 B ⟨u1.val + d, hd_lt⟩ - nyquistAlternatingPrefix c0 B u1‖
        ≤ (d : ℝ) * (c0⁻¹ * vecInfNorm B) :=
          norm_nyquistAlternatingPrefix_add_sub_le hc0 B u1.val d hd_lt
      _ ≤ (t1 : ℝ) * (c0⁻¹ * vecInfNorm B) :=
          mul_le_mul_of_nonneg_right hd_le (by positivity)
      _ = ((t1 : ℝ) / c0) * vecInfNorm B := by ring

/-- Pointwise norm bound on `nyquistOpenChainParticular`: for $0 < c_0$,
$\|Z^{\text{part}}\|_\infty \le (t_1 / c_0) \|B\|_\infty$. -/
theorem vecInfNorm_nyquistOpenChainParticular_le {t1 : ℕ} {c0 : ℝ} (hc0 : 0 < c0)
    (B : Fin t1 → ℂ) :
    vecInfNorm (nyquistOpenChainParticular c0 B) ≤ ((t1 : ℝ) / c0) * vecInfNorm B := by
  have hB_nn : 0 ≤ vecInfNorm B := vecInfNorm_nonneg B
  rw [vecInfNorm_le_iff _ (by positivity)]
  intro u1
  have ht1_pos : 0 < t1 := lt_of_le_of_lt (Nat.zero_le u1.val) u1.isLt
  have hnorm_eq :
      ‖nyquistOpenChainParticular c0 B u1‖ =
        ‖nyquistAlternatingPrefix c0 B u1 - nyquistAlternatingPrefix c0 B ⟨0, ht1_pos⟩‖ := by
    rw [nyquistAlternatingPrefix_zero, sub_zero, nyquistAlternatingPrefix,
      norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hnorm_eq]
  exact norm_nyquistAlternatingPrefix_sub_le hc0 B u1 ⟨0, ht1_pos⟩

/-- Nullspace-projected Nyquist column solver (`nyquistColumnSolve`, Theorem 5.1(3) (`thm:deconv`)
and Section 5.2 (`sec:solvers`)):
given the open-chain particular solution $Z^{\text{part}} = \text{nyquistOpenChainParticular } c_0 \, B$
and the true alternating sum $\text{altTrue} = \sum_{u_1=0}^{t_1-1} (-1)^{u_1} Z_{u_1}$, projects onto
the nullspace vector $v_{u_1} = (-1)^{u_1}$ via:
$$Z_{u_1} = Z^{\text{part}}_{u_1} + (-1)^{u_1} \frac{\text{altTrue} - \sum_{m=0}^{t_1-1} (-1)^m Z^{\text{part}}_m}{t_1}.$$ -/
noncomputable def nyquistColumnSolve {t1 : ℕ} (c0 : ℝ) (B : Fin t1 → ℂ)
    (altTrue : ℂ) (u1 : Fin t1) : ℂ :=
  let Zpart := nyquistOpenChainParticular c0 B
  let altPart := ∑ m : Fin t1, (-1 : ℂ) ^ m.val * Zpart m
  Zpart u1 + (-1 : ℂ) ^ u1.val * ((altTrue - altPart) / (t1 : ℂ))

/-- **Nyquist Column Solver Alternating-Sum Identity (`nyquistColumnSolve_alternating_sum`,
Theorem 5.1(3) (`thm:deconv`))**:
For any $t_1 \ge 1$ (`[NeZero t1]`), the projected solution $Z = \text{nyquistColumnSolve } c_0 \, B \, \text{altTrue}$
has alternating sum equal to $\text{altTrue}$:
$$\sum_{u_1 : \text{Fin } t_1} (-1)^{u_1} \text{nyquistColumnSolve } c_0 \, B \, \text{altTrue } u_1 = \text{altTrue}.$$ -/
theorem nyquistColumnSolve_alternating_sum {t1 : ℕ} [NeZero t1] (c0 : ℝ)
    (B : Fin t1 → ℂ) (altTrue : ℂ) :
    (∑ u1 : Fin t1, (-1 : ℂ) ^ u1.val * nyquistColumnSolve c0 B altTrue u1) = altTrue := by
  have ht1_ne : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t1)
  set Zpart := nyquistOpenChainParticular c0 B
  set altPart : ℂ := ∑ m : Fin t1, (-1 : ℂ) ^ m.val * Zpart m
  have hterm : ∀ u1 : Fin t1,
      (-1 : ℂ) ^ u1.val * nyquistColumnSolve c0 B altTrue u1 =
        (-1 : ℂ) ^ u1.val * Zpart u1 + (altTrue - altPart) / (t1 : ℂ) := by
    intro u1
    simp only [nyquistColumnSolve]
    have hsq : (-1 : ℂ) ^ u1.val * (-1 : ℂ) ^ u1.val = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      (-1 : ℂ) ^ u1.val * (Zpart u1 + (-1 : ℂ) ^ u1.val * ((altTrue - altPart) / (t1 : ℂ)))
        = (-1 : ℂ) ^ u1.val * Zpart u1 +
            ((-1 : ℂ) ^ u1.val * (-1 : ℂ) ^ u1.val) * ((altTrue - altPart) / (t1 : ℂ)) := by ring
      _ = (-1 : ℂ) ^ u1.val * Zpart u1 + (altTrue - altPart) / (t1 : ℂ) := by
        rw [hsq, one_mul]
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  calc
    altPart + (t1 : ℂ) * ((altTrue - altPart) / (t1 : ℂ))
      = altPart + (altTrue - altPart) := by
        rw [mul_div_cancel₀ _ ht1_ne]
    _ = altTrue := by ring

/-- **Nyquist Column Solver Specification & Uniqueness (`nyquistColumnSolve_spec`,
Theorem 5.1(3) (`thm:deconv`), Section 5.1 (`sec:deconv-thm`))**:
If a vector $Z : \text{Fin } t_1 \to \mathbb{C}$ satisfies the Nyquist open-chain recurrence
$c_0 Z_m + c_0 Z_{m-1} = B_m$ for all $1 \le m < t_1$ (in particular if $Z$ satisfies the
singular cyclic system $c_0 Z_m + c_0 Z_{(m-1) \bmod t_1} = B_m$ for all $m \in \text{Fin } t_1$)
with $c_0 \ne 0$ and has alternating sum $\sum_{u_1=0}^{t_1-1} (-1)^{u_1} Z_{u_1} = \text{altTrue}$,
then $Z = \text{nyquistColumnSolve } c_0 \, B \, \text{altTrue}$. -/
theorem nyquistColumnSolve_spec {t1 : ℕ} [NeZero t1] {c0 : ℝ} (hc0 : c0 ≠ 0)
    (B Z : Fin t1 → ℂ) (altTrue : ℂ)
    (hrec : ∀ m : Fin t1, (c0 : ℂ) * Z m + (c0 : ℂ) * Z (cyclicPrev m) = B m)
    (halt : (∑ u1 : Fin t1, (-1 : ℂ) ^ u1.val * Z u1) = altTrue) :
    ∀ u1 : Fin t1, Z u1 = nyquistColumnSolve c0 B altTrue u1 := by
  have ht1_pos : 0 < t1 := NeZero.pos t1
  have ht1_ne : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t1)
  have hc0_c : (c0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0
  set Zpart := nyquistOpenChainParticular c0 B
  have hdiff : ∀ (k : ℕ) (hk : k < t1),
      Z ⟨k, hk⟩ - Zpart ⟨k, hk⟩ = (-1 : ℂ) ^ k * Z ⟨0, ht1_pos⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : (⟨0, hk⟩ : Fin t1) = ⟨0, ht1_pos⟩ := rfl
      rw [h0]
      change Z ⟨0, ht1_pos⟩ - 0 = (-1 : ℂ) ^ 0 * Z ⟨0, ht1_pos⟩
      ring
    | succ k ih =>
      intro hk
      have hk_prev : k < t1 := Nat.lt_of_succ_lt hk
      have hpos : 0 < (⟨k + 1, hk⟩ : Fin t1).val := Nat.succ_pos k
      have hZ_rec := hrec ⟨k + 1, hk⟩
      have hZp_rec := nyquistOpenChainParticular_recurrence hc0 B ⟨k + 1, hk⟩ hpos
      have hprev_eq : cyclicPrev (⟨k + 1, hk⟩ : Fin t1) = ⟨k, hk_prev⟩ := by
        rw [cyclicPrev_eq_sub_one_of_pos ⟨k + 1, hk⟩ hpos]
        rfl
      rw [hprev_eq] at hZ_rec hZp_rec
      have hsub_mul :
          (c0 : ℂ) * ((Z ⟨k + 1, hk⟩ - Zpart ⟨k + 1, hk⟩) +
            (Z ⟨k, hk_prev⟩ - Zpart ⟨k, hk_prev⟩)) = 0 := by
        calc
          (c0 : ℂ) * ((Z ⟨k + 1, hk⟩ - Zpart ⟨k + 1, hk⟩) +
              (Z ⟨k, hk_prev⟩ - Zpart ⟨k, hk_prev⟩))
            = ((c0 : ℂ) * Z ⟨k + 1, hk⟩ + (c0 : ℂ) * Z ⟨k, hk_prev⟩) -
                ((c0 : ℂ) * Zpart ⟨k + 1, hk⟩ + (c0 : ℂ) * Zpart ⟨k, hk_prev⟩) := by ring
          _ = B ⟨k + 1, hk⟩ - B ⟨k + 1, hk⟩ := by rw [hZ_rec, hZp_rec]
          _ = 0 := sub_self _
      have hsum_zero :
          (Z ⟨k + 1, hk⟩ - Zpart ⟨k + 1, hk⟩) +
            (Z ⟨k, hk_prev⟩ - Zpart ⟨k, hk_prev⟩) = 0 :=
        (mul_eq_zero.mp hsub_mul).resolve_left hc0_c
      have hneg :
          Z ⟨k + 1, hk⟩ - Zpart ⟨k + 1, hk⟩ =
            -(Z ⟨k, hk_prev⟩ - Zpart ⟨k, hk_prev⟩) :=
        eq_neg_of_add_eq_zero_left hsum_zero
      rw [hneg, ih hk_prev, pow_succ]
      ring
  have hZ_decomp : ∀ u1 : Fin t1,
      Z u1 = Zpart u1 + (-1 : ℂ) ^ u1.val * Z ⟨0, ht1_pos⟩ := by
    intro u1
    have h := hdiff u1.val u1.isLt
    exact eq_add_of_sub_eq' h
  set altPart : ℂ := ∑ m : Fin t1, (-1 : ℂ) ^ m.val * Zpart m
  have halt_eq : altTrue = altPart + (t1 : ℂ) * Z ⟨0, ht1_pos⟩ := by
    rw [← halt]
    have hterm : ∀ m : Fin t1,
        (-1 : ℂ) ^ m.val * Z m =
          (-1 : ℂ) ^ m.val * Zpart m + Z ⟨0, ht1_pos⟩ := by
      intro m
      rw [hZ_decomp m]
      have hsq : (-1 : ℂ) ^ m.val * (-1 : ℂ) ^ m.val = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (-1 : ℂ) ^ m.val * (Zpart m + (-1 : ℂ) ^ m.val * Z ⟨0, ht1_pos⟩)
          = (-1 : ℂ) ^ m.val * Zpart m +
              ((-1 : ℂ) ^ m.val * (-1 : ℂ) ^ m.val) * Z ⟨0, ht1_pos⟩ := by ring
        _ = (-1 : ℂ) ^ m.val * Zpart m + Z ⟨0, ht1_pos⟩ := by rw [hsq, one_mul]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rfl
  have hZ0 : Z ⟨0, ht1_pos⟩ = (altTrue - altPart) / (t1 : ℂ) := by
    rw [halt_eq]
    field_simp
    ring
  intro u1
  rw [hZ_decomp u1, hZ0]
  rfl

/-- **Nyquist Column Solver $\ell_\infty$ Stability Bound (`vecInfNorm_nyquistColumnSolve_le`,
Theorem 5.1(3) (`thm:deconv`), Section 5.1 (`sec:deconv-thm`))**:
For any $t_1 \ge 1$ (`[NeZero t1]`) and $c_0 > 0$:
$$\|\text{nyquistColumnSolve } c_0 \, B \, \text{altTrue}\|_\infty \le \frac{t_1}{c_0} \|B\|_\infty + \frac{\|\text{altTrue}\|}{t_1}.$$ -/
theorem vecInfNorm_nyquistColumnSolve_le {t1 : ℕ} [NeZero t1] {c0 : ℝ} (hc0 : 0 < c0)
    (B : Fin t1 → ℂ) (altTrue : ℂ) :
    vecInfNorm (nyquistColumnSolve c0 B altTrue) ≤
      ((t1 : ℝ) / c0) * vecInfNorm B + ‖altTrue‖ / (t1 : ℝ) := by
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr (NeZero.pos t1)
  have ht1_ne : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t1)
  have hB_nn : 0 ≤ vecInfNorm B := vecInfNorm_nonneg B
  rw [vecInfNorm_le_iff _ (by positivity)]
  intro u1
  set P := nyquistAlternatingPrefix c0 B
  have hrep :
      nyquistColumnSolve c0 B altTrue u1 =
        (-1 : ℂ) ^ u1.val *
          ((∑ m : Fin t1, (P u1 - P m)) / (t1 : ℂ) + altTrue / (t1 : ℂ)) := by
    simp only [nyquistColumnSolve, P, nyquistAlternatingPrefix]
    have hsq : (-1 : ℂ) ^ u1.val * (-1 : ℂ) ^ u1.val = 1 := by
      rw [← mul_pow]
      norm_num
    have hsum_sub :
        (∑ m : Fin t1, ((-1 : ℂ) ^ u1.val * nyquistOpenChainParticular c0 B u1 -
          (-1 : ℂ) ^ m.val * nyquistOpenChainParticular c0 B m)) =
        (t1 : ℂ) * ((-1 : ℂ) ^ u1.val * nyquistOpenChainParticular c0 B u1) -
          ∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticular c0 B m := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [hsum_sub]
    calc
      nyquistOpenChainParticular c0 B u1 +
          (-1 : ℂ) ^ u1.val *
            ((altTrue - ∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticular c0 B m) /
              (t1 : ℂ))
        = ((-1 : ℂ) ^ u1.val * (-1 : ℂ) ^ u1.val) * nyquistOpenChainParticular c0 B u1 +
            (-1 : ℂ) ^ u1.val *
              ((altTrue - ∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticular c0 B m) /
                (t1 : ℂ)) := by rw [hsq, one_mul]
      _ = (-1 : ℂ) ^ u1.val *
            (((t1 : ℂ) * ((-1 : ℂ) ^ u1.val * nyquistOpenChainParticular c0 B u1) -
              ∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticular c0 B m) / (t1 : ℂ) +
              altTrue / (t1 : ℂ)) := by
          field_simp
          ring
  rw [hrep, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hsum_norm :
      ‖(∑ m : Fin t1, (P u1 - P m)) / (t1 : ℂ)‖ ≤ ((t1 : ℝ) / c0) * vecInfNorm B := by
    rw [norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ ht1_pos]
    calc
      ‖∑ m : Fin t1, (P u1 - P m)‖
        ≤ ∑ m : Fin t1, ‖P u1 - P m‖ := norm_sum_le _ _
      _ ≤ ∑ _m : Fin t1, (((t1 : ℝ) / c0) * vecInfNorm B) :=
          Finset.sum_le_sum (fun m _ => norm_nyquistAlternatingPrefix_sub_le hc0 B u1 m)
      _ = ((t1 : ℝ) / c0) * vecInfNorm B * (t1 : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have halt_norm : ‖altTrue / (t1 : ℂ)‖ = ‖altTrue‖ / (t1 : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
  calc
    ‖(∑ m : Fin t1, (P u1 - P m)) / (t1 : ℂ) + altTrue / (t1 : ℂ)‖
      ≤ ‖(∑ m : Fin t1, (P u1 - P m)) / (t1 : ℂ)‖ + ‖altTrue / (t1 : ℂ)‖ := norm_add_le _ _
    _ ≤ ((t1 : ℝ) / c0) * vecInfNorm B + ‖altTrue‖ / (t1 : ℝ) := by
        rw [halt_norm]
        linarith

/-- **Nyquist Column Conditioning Bound (`nyquist_conditioning_le_236_t1_of_bounds`,
Theorem 5.1(3) (`thm:deconv`), Section 5.1 (`sec:deconv-thm`))**:
When $c_0 \ge 0.49999999$, the Nyquist column solver satisfies:
$$\|\text{nyquistColumnSolve } c_0 \, B \, \text{altTrue}\|_\infty \le 2.36 \, t_1 \|B\|_\infty + \frac{\|\text{altTrue}\|}{t_1}.$$ -/
theorem nyquist_conditioning_le_236_t1_of_bounds {t1 : ℕ} [NeZero t1] {c0 : ℝ}
    (hc0 : (49999999 / 100000000 : ℝ) ≤ c0)
    (B : Fin t1 → ℂ) (altTrue : ℂ) :
    vecInfNorm (nyquistColumnSolve c0 B altTrue) ≤
      (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm B + ‖altTrue‖ / (t1 : ℝ) := by
  have hc0_pos : 0 < c0 := by linarith
  have hB_nn : 0 ≤ vecInfNorm B := vecInfNorm_nonneg B
  have ht1_nn : (0 : ℝ) ≤ (t1 : ℝ) := Nat.cast_nonneg t1
  have hinv : (t1 : ℝ) / c0 ≤ (236 / 100 : ℝ) * (t1 : ℝ) := by
    rw [div_le_iff₀ hc0_pos]
    nlinarith
  have hmul : ((t1 : ℝ) / c0) * vecInfNorm B ≤ (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm B :=
    mul_le_mul_of_nonneg_right hinv hB_nn
  have hnyq := vecInfNorm_nyquistColumnSolve_le hc0_pos B altTrue
  linarith

/-! ### 4B. Single-Pass $O(t_1)$ Quantized Fixed-Point Step 3 Solvers (`bidiagSweepQuant`, `cyclicBidiagSolveQuant`, `cyclicBidiagPrevSolveQuant`, `nyquistColumnSolveQuant`; Section 5.2 (`sec:solvers`) and Lemma 5.2 (`lem:solver-err`)) -/

/-- Single step of the open-chain Nyquist recurrence $Z_{\text{part}}[k+1] = B_{\text{scaled}}[k+1] - Z_{\text{part}}[k]$
(`nyquistOpenChainStep`, Section 5.2 (`sec:solvers`)). -/
def nyquistOpenChainStep {t1 : ℕ} {α : Type*} [Zero α] [Sub α]
    (B_scaled : Fin t1 → α) (k : ℕ) (prev : α) : α :=
  if hk : k + 1 < t1 then B_scaled ⟨k + 1, hk⟩ - prev else 0

/-- Single step of the non-Nyquist cyclic bidiagonal affine recurrence sweep
$(z_{p, s+1}, z_{h, s+1}) = (B_{\text{scaled}}[s] + \mathrm{Round}_{q_{\text{work}}}(\text{ratio}_q \cdot z_{p, s}), \mathrm{Round}_{q_{\text{work}}}(\text{ratio}_q \cdot z_{h, s}))$
(`bidiagSweepStep`, Section 5.2 (`sec:solvers`)). -/
noncomputable def bidiagSweepStep (qWork : ℕ) (ratio_q : ℝ) (B_scaled : ℕ → ℂ)
    (s : ℕ) (st : ℂ × ℝ) : ℂ × ℝ :=
  (B_scaled s + quantizeComplex qWork ((ratio_q : ℂ) * st.1),
   quantizeReal qWork (ratio_q * st.2))

/-- Single-pass $O(t_1)$ fixed-point linear recurrence sweep (`bidiagSweepQuant`,
Section 5.2 (`sec:solvers`) and Lemma 5.2 (`lem:solver-err`)): computes the column
reciprocal `invA_q := quantizeReal qWork (c_max_q⁻¹)` **once per column**, scales each RHS entry
via fixed-point multiplication `quantizeComplex qWork ((invA_q : ℂ) * B_seq s)`, computes the
particular and homogeneous recurrence trajectories `(zp, zh)` in a **single pass of $t_1$ steps**
via `buildRecurrenceArray` outside `fun u1 => ...`, solves the scalar periodic boundary closure
$Z_0 = \mathrm{Round}_{q_{\text{work}}}(z_{p, t_1} / (1 - z_{h, t_1}))$, and reconstructs each row
in $O(1)$ per entry. -/
noncomputable def bidiagSweepQuant (t1 q : ℕ) (a_max a_min : ℤ)
    (B_seq : ℕ → ℂ) (idx : Fin t1 → ℕ) : Fin t1 → ℂ :=
  let qWork : ℕ := q + 9
  let c_max_q : ℝ := (a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  let c_min_q : ℝ := (a_min : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  let invA_q : ℝ := quantizeReal qWork (c_max_q⁻¹)
  let ratio_q : ℝ := quantizeReal qWork (-c_min_q / c_max_q)
  let B_scaled : ℕ → ℂ := fun s => quantizeComplex qWork ((invA_q : ℂ) * B_seq s)
  let (trajArr, lastSt) :=
    buildRecurrenceArray ((0 : ℂ), (1 : ℝ)) (bidiagSweepStep qWork ratio_q B_scaled) t1
  let Z0 : ℂ := quantizeComplex qWork (lastSt.1 / ((1 - lastSt.2 : ℝ) : ℂ))
  fun u1 =>
    let st := trajArr.getD (idx u1) ((0 : ℂ), (1 : ℝ))
    quantizeComplex q (st.1 + quantizeComplex qWork ((st.2 : ℂ) * Z0))

/-- Quantized fixed-point Step 3 forward-shift cyclic bidiagonal solver with explicit integer
mantissas `a, b : ℤ` (`cyclicBidiagSolveQuantWithMantissa`, Section 5.2 (`sec:solvers`)):
executes `bidiagSweepQuant` in $O(t_1)$ operations per column. -/
noncomputable def cyclicBidiagSolveQuantWithMantissa {t1 : ℕ} [NeZero t1] (q : ℕ) (a b : ℤ)
    (B : Fin t1 → ℂ) : Fin t1 → ℂ :=
  let B_q : Fin t1 → ℂ := fun m => quantizeComplex q (B m)
  have ht1 : 0 < t1 := NeZero.pos t1
  if b ≤ a then
    bidiagSweepQuant t1 q a b
      (fun s => B_q ⟨(t1 - 1 - s % t1) % t1, Nat.mod_lt _ ht1⟩)
      (fun u1 => (t1 - u1.val) % t1)
  else
    bidiagSweepQuant t1 q b a
      (fun s => B_q ⟨s % t1, Nat.mod_lt _ ht1⟩)
      (fun u1 => u1.val)

/-- Quantized fixed-point Step 3 forward-shift cyclic bidiagonal solver (`cyclicBidiagSolveQuant`,
Section 5.2 (`sec:solvers`)). -/
noncomputable def cyclicBidiagSolveQuant {t1 : ℕ} [NeZero t1] (q : ℕ) (c0 c1 : ℝ)
    (B : Fin t1 → ℂ) : Fin t1 → ℂ :=
  cyclicBidiagSolveQuantWithMantissa q (quantizeRealMantissa q c0) (quantizeRealMantissa q c1) B

/-- Quantized fixed-point Step 3 backward-shift cyclic bidiagonal solver with explicit integer
mantissas `a, b : ℤ` (`cyclicBidiagPrevSolveQuantWithMantissa`, Section 5.2 (`sec:solvers`)). -/
noncomputable def cyclicBidiagPrevSolveQuantWithMantissa {t1 : ℕ} [NeZero t1] (q : ℕ) (a b : ℤ)
    (B : Fin t1 → ℂ) : Fin t1 → ℂ :=
  cyclicBidiagSolveQuantWithMantissa q b a (fun m => B (cyclicNext m))

/-- Quantized fixed-point Step 3 backward-shift cyclic bidiagonal solver (`cyclicBidiagPrevSolveQuant`,
Section 5.2 (`sec:solvers`)). -/
noncomputable def cyclicBidiagPrevSolveQuant {t1 : ℕ} [NeZero t1] (q : ℕ) (c0 c1 : ℝ)
    (B : Fin t1 → ℂ) : Fin t1 → ℂ :=
  cyclicBidiagPrevSolveQuantWithMantissa q (quantizeRealMantissa q c0) (quantizeRealMantissa q c1) B

/-- Quantized fixed-point Step 3 Nyquist column solver with explicit integer mantissa `a : ℤ`
(`nyquistColumnSolveQuantWithMantissa`, Section 5.2 (`sec:solvers`)): executes the 2-pass $O(t_1)$
open-chain + cyclic rank-1 correction in fixed-point arithmetic using `buildRecurrenceArray`
outside `fun u1 => ...`. -/
noncomputable def nyquistColumnSolveQuantWithMantissa {t1 : ℕ} (q : ℕ) (a : ℤ)
    (B : Fin t1 → ℂ) (altTrue : ℂ) : Fin t1 → ℂ :=
  let qWork : ℕ := q + 4
  let c0_q : ℝ := (a : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  let invC0_q : ℝ := quantizeReal qWork (c0_q⁻¹)
  let B_q : Fin t1 → ℂ := fun m => quantizeComplex q (B m)
  let B_scaled : Fin t1 → ℂ := fun m => quantizeComplex qWork ((invC0_q : ℂ) * B_q m)
  let alt_q : ℂ := quantizeComplex q altTrue
  let zpartArr : Array ℂ :=
    (buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) t1).1
  let altPart : ℂ := ∑ m : Fin t1, (-1 : ℂ) ^ m.val * zpartArr.getD m.val 0
  let corr : ℂ := quantizeComplex qWork ((alt_q - altPart) / (t1 : ℂ))
  fun u1 => quantizeComplex q (zpartArr.getD u1.val 0 + (-1 : ℂ) ^ u1.val * corr)

/-- Quantized fixed-point Step 3 Nyquist column solver (`nyquistColumnSolveQuant`,
Section 5.2 (`sec:solvers`)). -/
noncomputable def nyquistColumnSolveQuant {t1 : ℕ} (q : ℕ) (c0 : ℝ)
    (B : Fin t1 → ℂ) (altTrue : ℂ) : Fin t1 → ℂ :=
  nyquistColumnSolveQuantWithMantissa q (quantizeRealMantissa q c0) B altTrue

/-- Exact reduction from `cyclicBidiagPrevSolveQuant` to `cyclicBidiagSolveQuant`. -/
theorem cyclicBidiagPrevSolveQuant_eq_cyclicBidiagSolveQuant {t1 : ℕ} [NeZero t1]
    (q : ℕ) (c0 c1 : ℝ) (B : Fin t1 → ℂ) (u1 : Fin t1) :
    cyclicBidiagPrevSolveQuant q c0 c1 B u1 =
      cyclicBidiagSolveQuant q c1 c0 (fun m => B (cyclicNext m)) u1 := rfl

/-- Rescaling identity for `nyquistOpenChainParticularAux`: dividing by $c_0$ is equivalent
to solving with weight $1$ on input $c_0^{-1} B$. -/
theorem nyquistOpenChainParticularAux_eq_one {t1 : ℕ} (c0 : ℝ) (B : Fin t1 → ℂ) :
    ∀ (k : ℕ) (hk : k < t1),
      nyquistOpenChainParticularAux c0 B k hk =
        nyquistOpenChainParticularAux 1 (fun m => (c0 : ℂ)⁻¹ * B m) k hk
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [nyquistOpenChainParticularAux, Complex.ofReal_one, inv_one, one_mul,
      nyquistOpenChainParticularAux_eq_one c0 B k (Nat.lt_of_succ_lt hk)]

/-- Linearity of `nyquistOpenChainParticularAux` under subtraction of right-hand sides. -/
theorem nyquistOpenChainParticularAux_sub {t1 : ℕ} (c0 : ℝ) (B1 B2 : Fin t1 → ℂ) :
    ∀ (k : ℕ) (hk : k < t1),
      nyquistOpenChainParticularAux c0 B1 k hk - nyquistOpenChainParticularAux c0 B2 k hk =
        nyquistOpenChainParticularAux c0 (fun m => B1 m - B2 m) k hk
  | 0, _ => by simp [nyquistOpenChainParticularAux]
  | k + 1, hk => by
    simp only [nyquistOpenChainParticularAux]
    rw [← nyquistOpenChainParticularAux_sub c0 B1 B2 k (Nat.lt_of_succ_lt hk)]
    ring

/-- Difference of two `nyquistColumnSolve` evaluations expressed as a single `nyquistColumnSolve 1`
evaluation on the difference of scaled inputs and alternating sums. -/
theorem nyquistColumnSolve_sub_eq_one {t1 : ℕ} (c0 c1 : ℝ) (B0 B1 : Fin t1 → ℂ)
    (alt0 alt1 : ℂ) (u1 : Fin t1) :
    nyquistColumnSolve c0 B0 alt0 u1 - nyquistColumnSolve c1 B1 alt1 u1 =
      nyquistColumnSolve 1 (fun m => (c0 : ℂ)⁻¹ * B0 m - (c1 : ℂ)⁻¹ * B1 m) (alt0 - alt1) u1 := by
  simp only [nyquistColumnSolve, nyquistOpenChainParticular]
  have hpart : ∀ m : Fin t1,
      nyquistOpenChainParticularAux c0 B0 m.val m.isLt -
        nyquistOpenChainParticularAux c1 B1 m.val m.isLt =
      nyquistOpenChainParticularAux 1
        (fun j => (c0 : ℂ)⁻¹ * B0 j - (c1 : ℂ)⁻¹ * B1 j) m.val m.isLt := by
    intro m
    rw [nyquistOpenChainParticularAux_eq_one c0 B0,
      nyquistOpenChainParticularAux_eq_one c1 B1,
      nyquistOpenChainParticularAux_sub]
  have hsum :
      (∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticularAux c0 B0 m.val m.isLt) -
        (∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticularAux c1 B1 m.val m.isLt) =
      ∑ m : Fin t1, (-1 : ℂ) ^ m.val *
        nyquistOpenChainParticularAux 1
          (fun j => (c0 : ℂ)⁻¹ * B0 j - (c1 : ℂ)⁻¹ * B1 j) m.val m.isLt := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← mul_sub, hpart m]
  rw [← hpart u1, ← hsum]
  ring

/-- Trajectory equivalence between `buildRecurrenceArray` on `nyquistOpenChainStep B_scaled`
and `nyquistOpenChainParticularAux 1 B_scaled`. -/
theorem buildRecurrenceArray_nyquistOpenChainStep_eq {t1 : ℕ} (B_scaled : Fin t1 → ℂ) :
    ∀ (k : ℕ) (hk : k < t1),
      (buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) k).2 =
        nyquistOpenChainParticularAux 1 B_scaled k hk
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [buildRecurrenceArray, nyquistOpenChainStep, dif_pos hk,
      nyquistOpenChainParticularAux, Complex.ofReal_one, inv_one, one_mul,
      buildRecurrenceArray_nyquistOpenChainStep_eq B_scaled k (Nat.lt_of_succ_lt hk)]

/-- Array lookup equivalence for `nyquistOpenChainStep`. -/
theorem getD_buildRecurrenceArray_nyquistOpenChainStep_eq {t1 : ℕ}
    (B_scaled : Fin t1 → ℂ) (m : Fin t1) :
    (buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) t1).1.getD m.val 0 =
      nyquistOpenChainParticular 1 B_scaled m := by
  rw [getD_buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) (le_of_lt m.isLt)]
  exact buildRecurrenceArray_nyquistOpenChainStep_eq B_scaled m.val m.isLt

/-- Pointwise unfolding of `nyquistColumnSolveQuantWithMantissa` in terms of
`nyquistOpenChainParticular 1 B_scaled`. -/
theorem nyquistColumnSolveQuantWithMantissa_eq {t1 : ℕ} (q : ℕ) (a : ℤ)
    (B : Fin t1 → ℂ) (altTrue : ℂ) (u1 : Fin t1) :
    let qWork : ℕ := q + 4
    let c0_q : ℝ := (a : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
    let invC0_q : ℝ := quantizeReal qWork (c0_q⁻¹)
    let B_q : Fin t1 → ℂ := fun m => quantizeComplex q (B m)
    let B_scaled : Fin t1 → ℂ := fun m => quantizeComplex qWork ((invC0_q : ℂ) * B_q m)
    let alt_q : ℂ := quantizeComplex q altTrue
    let altPart : ℂ := ∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticular 1 B_scaled m
    let corr : ℂ := quantizeComplex qWork ((alt_q - altPart) / (t1 : ℂ))
    nyquistColumnSolveQuantWithMantissa q a B altTrue u1 =
      quantizeComplex q (nyquistOpenChainParticular 1 B_scaled u1 + (-1 : ℂ) ^ u1.val * corr) := by
  intro qWork c0_q invC0_q B_q B_scaled alt_q altPart corr
  unfold nyquistColumnSolveQuantWithMantissa
  dsimp only
  have hzpart : ∀ m : Fin t1,
      (buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) t1).1.getD m.val 0 =
        nyquistOpenChainParticular 1 B_scaled m :=
    getD_buildRecurrenceArray_nyquistOpenChainStep_eq B_scaled
  have hsum :
      (∑ m : Fin t1, (-1 : ℂ) ^ m.val *
        (buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) t1).1.getD m.val 0) = altPart :=
    Finset.sum_congr rfl (fun m _ => by rw [hzpart m])
  rw [hzpart u1, hsum]

/-- Non-negative reals remain non-negative under `quantizeReal q`. -/
theorem quantizeReal_nonneg (q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ quantizeReal q x := by
  unfold quantizeReal quantizeRealMantissa
  have hscaled : 0 ≤ x * (2 : ℝ) ^ q + (1 / 2 : ℝ) := by positivity
  have hfloor : (0 : ℤ) ≤ ⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋ := Int.floor_nonneg.mpr hscaled
  have hfloor_r : (0 : ℝ) ≤ (⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋ : ℝ) := by exact_mod_cast hfloor
  positivity

/-- Absolute quantization error of `quantizeReal q` is at most $\frac{1}{2} 2^{-q}$. -/
theorem abs_quantizeReal_sub_le_half_zpow (q : ℕ) (x : ℝ) :
    |quantizeReal q x - x| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) :=
  abs_quantizeReal_sub_self_le q x

/-- Pointwise complex quantization error is at most $2^{-q}$. -/
theorem norm_quantizeComplex_sub_le_pow (q : ℕ) (z : ℂ) :
    ‖quantizeComplex q z - z‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  have h1 := norm_quantizeComplex_sub_self_le q z
  have h2 := sqrt_two_le
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  nlinarith

/-- Vector $\ell_\infty$ quantization error of `quantizeComplex q` is at most $2^{-q}$. -/
theorem vecInfNorm_quantizeComplex_sub_le {n : ℕ} (q : ℕ) (v : Fin n → ℂ) :
    vecInfNorm (fun m => quantizeComplex q (v m) - v m) ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  rw [vecInfNorm_le_iff _ (by positivity)]
  intro m
  exact norm_quantizeComplex_sub_le_pow q (v m)

/-- For any $a, b \in [0, 1]$ and $n \in \mathbb{N}$, $|a^n - b^n| \le n |a - b|$. -/
theorem abs_pow_sub_pow_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (n : ℕ) :
    |a ^ n - b ^ n| ≤ (n : ℝ) * |a - b| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by
      rw [pow_succ', pow_succ']
      ring
    have h1 : |a * (a ^ n - b ^ n)| ≤ 1 * ((n : ℝ) * |a - b|) := by
      rw [abs_mul, abs_of_nonneg ha0]
      exact mul_le_mul ha1 ih (abs_nonneg _) zero_le_one
    have h2 : |(a - b) * b ^ n| ≤ |a - b| * 1 := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hb0 n)]
      exact mul_le_mul_of_nonneg_left (pow_le_one₀ hb0 hb1) (abs_nonneg _)
    have htri := abs_add_le (a * (a ^ n - b ^ n)) ((a - b) * b ^ n)
    rw [hsplit]
    push_cast
    linarith

/-- Any $x \in [-1, 1]$ remains in $[-1, 1]$ under `quantizeReal q`. -/
theorem abs_quantizeReal_le_one_of_abs_le_one (q : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |quantizeReal q x| ≤ 1 := by
  obtain ⟨hx_lo, hx_hi⟩ := abs_le.mp hx
  unfold quantizeReal quantizeRealMantissa
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hzpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have hcancel : (2 : ℝ) ^ q * (2 : ℝ) ^ (-(q : ℤ)) = 1 :=
    two_pow_mul_two_zpow_neg q
  have hlo : ((-(2 : ℤ) ^ q : ℤ) : ℝ) ≤ x * (2 : ℝ) ^ q + (1 / 2 : ℝ) := by
    rw [Int.cast_neg, Int.cast_pow, Int.cast_ofNat]
    nlinarith
  have hhi : x * (2 : ℝ) ^ q + (1 / 2 : ℝ) < (((2 : ℤ) ^ q + 1 : ℤ) : ℝ) := by
    rw [Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_one]
    nlinarith
  have hfl_lo : -(2 : ℤ) ^ q ≤ ⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋ := Int.le_floor.mpr hlo
  have hfl_lt : ⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋ < (2 : ℤ) ^ q + 1 := Int.floor_lt.mpr hhi
  have hfl_hi : ⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋ ≤ (2 : ℤ) ^ q := by omega
  have hfl_lo_r : -(2 : ℝ) ^ q ≤ (⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋ : ℝ) := by
    exact_mod_cast hfl_lo
  have hfl_hi_r : (⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋ : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast hfl_hi
  rw [abs_le]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hfl_lo_r (le_of_lt hzpow_pos)
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_right hfl_hi_r (le_of_lt hzpow_pos)
    nlinarith

/-- **Single-Pass $O(t_1)$ Bidiagonal Sweep Error Bound (`norm_bidiagSweepQuant_sub_le`,
Lemma 5.2 (`lem:solver-err`) and Appendix C.1 (`app:solver-err-proof`))**:
For any periodic linear recurrence sequence $W_{\text{seq}}$ satisfying $W_{\text{seq}}(t_1) = W_{\text{seq}}(0)$,
$\|W_{\text{seq}}(s)\| \le M_W$, and $W_{\text{seq}}(s + 1) = c_{\max, q}^{-1} B_{\text{seq}}(s) + (-c_{\min, q} / c_{\max, q}) W_{\text{seq}}(s)$
with $c_{\max, q} \le 2$, the single-pass $O(t_1)$ fixed-point sweep `bidiagSweepQuant` at working
precision $q + 9$ (using the column reciprocal `invA_q` computed once per column) approximates
$W_{\text{seq}}(\text{idx } u_1)$ within:
$$\|\text{bidiagSweepQuant } t_1 \, q \, a_{\max} \, a_{\min} \, B_{\text{seq}} \, \text{idx } u_1 - W_{\text{seq}}(\text{idx } u_1)\|
\le 2^{-q} + \frac{1}{16} t_1 2^{-q} (1 + M_W).$$ -/
theorem norm_bidiagSweepQuant_sub_le {t1 q : ℕ} (ht1_pos : 1 ≤ t1)
    (a_max a_min : ℤ)
    (hc_min_nn : 0 ≤ (a_min : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hc_le : (a_min : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ (a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hc_max_pos : 0 < (a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hc_max_le : (a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 2)
    (hr_pow : (((a_min : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) / ((a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))) ^ t1 ≤ 4 / 5)
    (ht1_q : (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 2)
    (B_seq W_seq : ℕ → ℂ) (M_W : ℝ) (hMW_nn : 0 ≤ M_W)
    (hW_per : W_seq t1 = W_seq 0)
    (hW_bound : ∀ s : ℕ, ‖W_seq s‖ ≤ M_W)
    (hW_rec : ∀ s < t1,
      W_seq (s + 1) =
        B_seq s / (((a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) : ℝ) : ℂ) +
          ((-(((a_min : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) /
              ((a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))) : ℝ) : ℂ) * W_seq s)
    (idx : Fin t1 → ℕ) (hidx : ∀ u1 : Fin t1, idx u1 ≤ t1)
    (u1 : Fin t1) :
    ‖bidiagSweepQuant t1 q a_max a_min B_seq idx u1 - W_seq (idx u1)‖ ≤
      (2 : ℝ) ^ (-(q : ℤ)) +
        (1 / 16 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (1 + M_W) := by
  set qWork : ℕ := q + 9
  set c_max_q : ℝ := (a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  set c_min_q : ℝ := (a_min : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  set invA_q : ℝ := quantizeReal qWork (c_max_q⁻¹)
  set β : ℝ := -c_min_q / c_max_q
  set ratio_q : ℝ := quantizeReal qWork β
  set B_scaled : ℕ → ℂ := fun s => quantizeComplex qWork ((invA_q : ℂ) * B_seq s)
  set st : ℕ → ℂ × ℝ :=
    fun s => (buildRecurrenceArray ((0 : ℂ), (1 : ℝ)) (bidiagSweepStep qWork ratio_q B_scaled) s).2
  have hzpow_q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have hzpow_w_pos : (0 : ℝ) < (2 : ℝ) ^ (-(qWork : ℤ)) := zpow_pos (by norm_num) _
  have hzpow_w_eq : (2 : ℝ) ^ (-(qWork : ℤ)) = (1 / 512 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hexp : -(qWork : ℤ) = (-9 : ℤ) + -(q : ℤ) := by dsimp [qWork]; omega
    rw [hexp, zpow_add₀ (by norm_num)]
    norm_num
  have hβ_abs_eq : |β| = c_min_q / c_max_q := by
    dsimp [β]
    rw [neg_div, abs_neg, abs_of_nonneg (div_nonneg hc_min_nn (le_of_lt hc_max_pos))]
  have hβ_abs_le : |β| ≤ 1 := by
    rw [hβ_abs_eq]
    exact div_le_one_of_le₀ hc_le (le_of_lt hc_max_pos)
  have hratio_abs_le : |ratio_q| ≤ 1 :=
    abs_quantizeReal_le_one_of_abs_le_one qWork hβ_abs_le
  have hratio_err : |ratio_q - β| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) :=
    abs_quantizeReal_sub_le_half_zpow qWork β
  have hinvA_err : |invA_q - c_max_q⁻¹| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) :=
    abs_quantizeReal_sub_le_half_zpow qWork (c_max_q⁻¹)
  have hzh_abs : ∀ s : ℕ, |(st s).2| ≤ 1 := by
    intro s
    induction s with
    | zero =>
      simp [st, buildRecurrenceArray]
    | succ s ih =>
      simp only [st, buildRecurrenceArray, bidiagSweepStep]
      apply abs_quantizeReal_le_one_of_abs_le_one qWork
      rw [abs_mul]
      calc
        |ratio_q| * |(st s).2| ≤ 1 * 1 :=
          mul_le_mul hratio_abs_le ih (abs_nonneg _) zero_le_one
        _ = 1 := mul_one 1
  have hzh_err : ∀ s : ℕ, |(st s).2 - β ^ s| ≤ (s : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
    intro s
    induction s with
    | zero =>
      simp [st, buildRecurrenceArray]
    | succ s ih =>
      have hstep_eq : (st (s + 1)).2 = quantizeReal qWork (ratio_q * (st s).2) := rfl
      have hsplit :
          (st (s + 1)).2 - β ^ (s + 1) =
            ((st (s + 1)).2 - ratio_q * (st s).2) +
              (ratio_q * ((st s).2 - β ^ s) + (ratio_q - β) * β ^ s) := by
        rw [pow_succ']
        ring
      have h1 : |(st (s + 1)).2 - ratio_q * (st s).2| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
        rw [hstep_eq]
        exact abs_quantizeReal_sub_le_half_zpow qWork (ratio_q * (st s).2)
      have h2 : |ratio_q * ((st s).2 - β ^ s)| ≤ 1 * ((s : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ))) := by
        rw [abs_mul]
        exact mul_le_mul hratio_abs_le ih (abs_nonneg _) zero_le_one
      have hβs_le : |β ^ s| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hβ_abs_le
      have h3 : |(ratio_q - β) * β ^ s| ≤ ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ))) * 1 := by
        rw [abs_mul]
        exact mul_le_mul hratio_err hβs_le (abs_nonneg _) (by positivity)
      have htri1 := abs_add_le ((st (s + 1)).2 - ratio_q * (st s).2)
        (ratio_q * ((st s).2 - β ^ s) + (ratio_q - β) * β ^ s)
      have htri2 := abs_add_le (ratio_q * ((st s).2 - β ^ s)) ((ratio_q - β) * β ^ s)
      rw [hsplit]
      push_cast
      linarith
  have hMW_zpow : 0 ≤ M_W * (2 : ℝ) ^ (-(qWork : ℤ)) :=
    mul_nonneg hMW_nn (le_of_lt hzpow_w_pos)
  have hE_bound : ∀ s ≤ t1,
      ‖((st s).1 + ((st s).2 : ℂ) * W_seq 0) - W_seq s‖ ≤
        3 * (s : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
    intro s hs
    induction s with
    | zero =>
      simp [st, buildRecurrenceArray]
    | succ s ih =>
      have hs_lt : s < t1 := Nat.lt_of_succ_le hs
      have ih_s := ih (le_of_lt hs_lt)
      have hzp_step : (st (s + 1)).1 = B_scaled s + quantizeComplex qWork ((ratio_q : ℂ) * (st s).1) := rfl
      have hzh_step : (st (s + 1)).2 = quantizeReal qWork (ratio_q * (st s).2) := rfl
      have hW_step : W_seq (s + 1) = B_seq s / (c_max_q : ℂ) + (β : ℂ) * W_seq s := by
        simpa [c_max_q, c_min_q, β, neg_div] using hW_rec s hs_lt
      set E_s : ℂ := ((st s).1 + ((st s).2 : ℂ) * W_seq 0) - W_seq s
      set d1 : ℂ := B_scaled s - B_seq s / (c_max_q : ℂ)
      set d2 : ℂ := quantizeComplex qWork ((ratio_q : ℂ) * (st s).1) - (ratio_q : ℂ) * (st s).1
      set d3 : ℂ := ((ratio_q - β : ℝ) : ℂ) * W_seq s
      set d4 : ℂ := (((st (s + 1)).2 - ratio_q * (st s).2 : ℝ) : ℂ) * W_seq 0
      have hsplit :
          ((st (s + 1)).1 + ((st (s + 1)).2 : ℂ) * W_seq 0) - W_seq (s + 1) =
            (ratio_q : ℂ) * E_s + (d1 + d2 + (d3 + d4)) := by
        rw [hzp_step, hW_step]
        dsimp only [E_s, d1, d2, d3, d4]
        push_cast
        ring
      have hB_div_eq : B_seq s / (c_max_q : ℂ) = W_seq (s + 1) - (β : ℂ) * W_seq s := by
        rw [hW_step, add_sub_cancel_right]
      have hB_div_norm : ‖B_seq s / (c_max_q : ℂ)‖ ≤ 2 * M_W := by
        rw [hB_div_eq]
        have htri_B := norm_sub_le (W_seq (s + 1)) ((β : ℂ) * W_seq s)
        have hWs1 := hW_bound (s + 1)
        have hβWs : ‖(β : ℂ) * W_seq s‖ ≤ 1 * M_W := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul hβ_abs_le (hW_bound s) (norm_nonneg _) zero_le_one
        linarith
      have hB_norm : ‖B_seq s‖ ≤ 4 * M_W := by
        have hc_ne : (c_max_q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc_max_pos)
        have hB_eq : B_seq s = (c_max_q : ℂ) * (B_seq s / (c_max_q : ℂ)) :=
          (mul_div_cancel₀ _ hc_ne).symm
        rw [hB_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hc_max_pos)]
        calc
          c_max_q * ‖B_seq s / (c_max_q : ℂ)‖ ≤ 2 * (2 * M_W) :=
            mul_le_mul hc_max_le hB_div_norm (norm_nonneg _) (by positivity)
          _ = 4 * M_W := by ring
      have hd1_split :
          d1 = (B_scaled s - (invA_q : ℂ) * B_seq s) + ((invA_q - c_max_q⁻¹ : ℝ) : ℂ) * B_seq s := by
        dsimp only [d1]
        push_cast
        ring
      have hd1_a : ‖B_scaled s - (invA_q : ℂ) * B_seq s‖ ≤ (2 : ℝ) ^ (-(qWork : ℤ)) :=
        norm_quantizeComplex_sub_le_pow qWork ((invA_q : ℂ) * B_seq s)
      have hd1_b :
          ‖((invA_q - c_max_q⁻¹ : ℝ) : ℂ) * B_seq s‖ ≤
            ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ))) * (4 * M_W) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hinvA_err hB_norm (norm_nonneg _) (by positivity)
      have hd1 : ‖d1‖ ≤ (2 : ℝ) ^ (-(qWork : ℤ)) + 2 * (2 : ℝ) ^ (-(qWork : ℤ)) * M_W := by
        have htri_d1 := norm_add_le (B_scaled s - (invA_q : ℂ) * B_seq s)
          (((invA_q - c_max_q⁻¹ : ℝ) : ℂ) * B_seq s)
        rw [hd1_split]
        linarith
      have hd2 : ‖d2‖ ≤ (2 : ℝ) ^ (-(qWork : ℤ)) :=
        norm_quantizeComplex_sub_le_pow qWork ((ratio_q : ℂ) * (st s).1)
      have hd3 : ‖d3‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) * M_W := by
        dsimp only [d3]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hratio_err (hW_bound s) (norm_nonneg _) (by positivity)
      have hd4 : ‖d4‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) * M_W := by
        dsimp only [d4]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hzh_step]
        exact mul_le_mul (abs_quantizeReal_sub_le_half_zpow qWork (ratio_q * (st s).2))
          (hW_bound 0) (norm_nonneg _) (by positivity)
      have hrE : ‖(ratio_q : ℂ) * E_s‖ ≤ 1 * (3 * (s : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ))) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hratio_abs_le ih_s (norm_nonneg _) zero_le_one
      have htri1 := norm_add_le ((ratio_q : ℂ) * E_s) (d1 + d2 + (d3 + d4))
      have htri2 := norm_add_le (d1 + d2) (d3 + d4)
      have htri3 := norm_add_le d1 d2
      have htri4 := norm_add_le d3 d4
      rw [hsplit]
      push_cast
      linarith
  have hβ_pow_le : β ^ t1 ≤ 4 / 5 := by
    have h1 : β ^ t1 ≤ |β ^ t1| := le_abs_self _
    have h2 : |β ^ t1| ≤ 4 / 5 := by
      rw [abs_pow, hβ_abs_eq]
      exact hr_pow
    linarith
  have hzh_t1_err : |(st t1).2 - β ^ t1| ≤ 1 / 100 := by
    have h1 := hzh_err t1
    rw [hzpow_w_eq] at h1
    linarith
  have hzh_t1_hi := (abs_le.mp hzh_t1_err).2
  have hdenom_ge : (1 / 6 : ℝ) ≤ 1 - (st t1).2 := by linarith
  have hdenom_pos : (0 : ℝ) < 1 - (st t1).2 := by linarith
  have hEt1 : ‖(st t1).1 - ((1 - (st t1).2 : ℝ) : ℂ) * W_seq 0‖ ≤
      3 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
    have h1 := hE_bound t1 (le_refl t1)
    have heq : (st t1).1 - ((1 - (st t1).2 : ℝ) : ℂ) * W_seq 0 =
        ((st t1).1 + ((st t1).2 : ℂ) * W_seq 0) - W_seq t1 := by
      rw [hW_per]
      push_cast
      ring
    rwa [heq]
  set Z0_exact : ℂ := (st t1).1 / ((1 - (st t1).2 : ℝ) : ℂ)
  set Z0 : ℂ := quantizeComplex qWork Z0_exact
  have hZ0_exact_err : ‖Z0_exact - W_seq 0‖ ≤
      18 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
    have hdenom_c_ne : ((1 - (st t1).2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hdenom_pos)
    have hsub_eq : Z0_exact - W_seq 0 =
        ((st t1).1 - ((1 - (st t1).2 : ℝ) : ℂ) * W_seq 0) / ((1 - (st t1).2 : ℝ) : ℂ) := by
      dsimp [Z0_exact]
      rw [sub_div, mul_div_cancel_left₀ _ hdenom_c_ne]
    rw [hsub_eq, norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hdenom_pos),
      div_le_iff₀ hdenom_pos]
    have hmul := mul_le_mul_of_nonneg_left hdenom_ge (norm_nonneg (Z0_exact - W_seq 0))
    have hmul2 :
        18 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) * (1 / 6 : ℝ) ≤
          18 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) * (1 - (st t1).2) :=
      mul_le_mul_of_nonneg_left hdenom_ge (by positivity)
    linarith
  have hZ0_q_err : ‖Z0 - Z0_exact‖ ≤ (2 : ℝ) ^ (-(qWork : ℤ)) :=
    norm_quantizeComplex_sub_le_pow qWork Z0_exact
  have ht1_ge1 : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1_pos
  have h1MW_ge1 : (1 : ℝ) ≤ 1 + M_W := by linarith
  have hpow_le_prod : (2 : ℝ) ^ (-(qWork : ℤ)) ≤ (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
    have h1 : (1 : ℝ) ≤ (t1 : ℝ) * (1 + M_W) := by nlinarith
    nlinarith
  have hZ0_err : ‖Z0 - W_seq 0‖ ≤ 19 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
    have htri : ‖Z0 - W_seq 0‖ ≤ ‖Z0 - Z0_exact‖ + ‖Z0_exact - W_seq 0‖ :=
      norm_sub_le_norm_sub_add_norm_sub Z0 Z0_exact (W_seq 0)
    linarith
  set s := idx u1
  have hs_le : s ≤ t1 := hidx u1
  have hs_r_le : (s : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast hs_le
  have hEs : ‖((st s).1 + ((st s).2 : ℂ) * W_seq 0) - W_seq s‖ ≤
      3 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
    have h1 := hE_bound s hs_le
    have h2 : 3 * (s : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) ≤
        3 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hzpow_w_pos)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith
  set W_tilde : ℂ := (st s).1 + quantizeComplex qWork (((st s).2 : ℂ) * Z0)
  have hgetD :
      (buildRecurrenceArray ((0 : ℂ), (1 : ℝ)) (bidiagSweepStep qWork ratio_q B_scaled) t1).1.getD s
        ((0 : ℂ), (1 : ℝ)) = st s :=
    getD_buildRecurrenceArray ((0 : ℂ), (1 : ℝ)) (bidiagSweepStep qWork ratio_q B_scaled) hs_le
  have hsweep_eq : bidiagSweepQuant t1 q a_max a_min B_seq idx u1 = quantizeComplex q W_tilde := by
    unfold bidiagSweepQuant
    dsimp only [qWork, c_max_q, c_min_q, invA_q, β, ratio_q, B_scaled, st, Z0, Z0_exact, W_tilde, s]
    rw [hgetD]
  have hW_tilde_split :
      W_tilde - W_seq s =
        (((st s).1 + ((st s).2 : ℂ) * W_seq 0) - W_seq s) +
          (((st s).2 : ℂ) * (Z0 - W_seq 0) +
            (quantizeComplex qWork (((st s).2 : ℂ) * Z0) - ((st s).2 : ℂ) * Z0)) := by
    dsimp [W_tilde]
    ring
  have hzh_Z0 : ‖((st s).2 : ℂ) * (Z0 - W_seq 0)‖ ≤
      1 * (19 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hzh_abs s) hZ0_err (norm_nonneg _) zero_le_one
  have hhom_q : ‖quantizeComplex qWork (((st s).2 : ℂ) * Z0) - ((st s).2 : ℂ) * Z0‖ ≤
      (2 : ℝ) ^ (-(qWork : ℤ)) :=
    norm_quantizeComplex_sub_le_pow qWork (((st s).2 : ℂ) * Z0)
  have hW_tilde_err :
      ‖W_tilde - W_seq s‖ ≤ (1 / 16 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (1 + M_W) := by
    have htri1 := norm_add_le (((st s).1 + ((st s).2 : ℂ) * W_seq 0) - W_seq s)
      (((st s).2 : ℂ) * (Z0 - W_seq 0) +
        (quantizeComplex qWork (((st s).2 : ℂ) * Z0) - ((st s).2 : ℂ) * Z0))
    have htri2 := norm_add_le (((st s).2 : ℂ) * (Z0 - W_seq 0))
      (quantizeComplex qWork (((st s).2 : ℂ) * Z0) - ((st s).2 : ℂ) * Z0)
    have hprod_nn : 0 ≤ (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by positivity
    have hsum :
        ‖W_tilde - W_seq s‖ ≤ 32 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := by
      rw [hW_tilde_split]
      linarith
    calc
      ‖W_tilde - W_seq s‖ ≤ 32 * (t1 : ℝ) * (1 + M_W) * (2 : ℝ) ^ (-(qWork : ℤ)) := hsum
      _ = (1 / 16 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (1 + M_W) := by
        rw [hzpow_w_eq]
        ring
  rw [hsweep_eq]
  have htri_out := norm_sub_le_norm_sub_add_norm_sub (quantizeComplex q W_tilde) W_tilde (W_seq s)
  have hout_q := norm_quantizeComplex_sub_le_pow q W_tilde
  linarith

/-- Elementary Bernoulli-type inequality: for $0 \le r \le 1$ and $n \in \mathbb{N}$,
$1 - r^n \le n (1 - r)$. -/
theorem one_sub_pow_le_nat_mul_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    1 - r ^ n ≤ (n : ℝ) * (1 - r) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hpow_le : r ^ n ≤ 1 := pow_le_one₀ hr0 hr1
    have h1mr_nn : 0 ≤ 1 - r := by linarith
    have hstep : r ^ n * (1 - r) ≤ 1 * (1 - r) :=
      mul_le_mul_of_nonneg_right hpow_le h1mr_nn
    calc
      1 - r ^ (n + 1) = (1 - r ^ n) + r ^ n * (1 - r) := by
        rw [pow_succ]
        ring
      _ ≤ (n : ℝ) * (1 - r) + 1 * (1 - r) := add_le_add ih hstep
      _ = ((n + 1 : ℕ) : ℝ) * (1 - r) := by
        push_cast
        ring

/-- Under the conditioning bounds of Theorem 5.1 (`thm:deconv`), $2.36 \, t_1 \cdot 2^{-q} \le 1/4$, and mantissa
approximation errors $|c_{0,q} - c_0|, |c_{1,q} - c_1| \le \frac{11}{20} 2^{-q}$, the quantized
weights preserve strict dominance and satisfy $(\min(c_{0,q}, c_{1,q}) / \max(c_{0,q}, c_{1,q}))^{t_1} \le 4/5 < 1$. -/
theorem mantissa_weights_invertible_and_ratio_pow_le {t1 : ℕ} [NeZero t1] {q : ℕ} {c0 c1 c0_q c1_q : ℝ}
    (hcmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1)
    (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 ≤ 15 / 100)
    (hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4)
    (ha_err : |c0_q - c0| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hb_err : |c1_q - c1| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hc0q_nn : 0 ≤ c0_q) (hc1q_nn : 0 ≤ c1_q) :
    (44 / 100 : ℝ) ≤ max c0_q c1_q ∧
      0 ≤ min c0_q c1_q ∧
      (min c0_q c1_q / max c0_q c1_q) ^ t1 ≤ 4 / 5 := by
  have ht1_pos_nat : 1 ≤ t1 := NeZero.one_le
  have ht1_ge1 : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1_pos_nat
  have hzpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have ht1_zpow : (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 25 / 236 := by linarith
  have hzpow_le : (2 : ℝ) ^ (-(q : ℤ)) ≤ 25 / 236 := by
    have h1 : 1 * (2 : ℝ) ^ (-(q : ℤ)) ≤ (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) :=
      mul_le_mul_of_nonneg_right ht1_ge1 (le_of_lt hzpow_pos)
    linarith
  have ha_bds := abs_le.mp ha_err
  have hb_bds := abs_le.mp hb_err
  have hmax_err : |max c0_q c1_q - max c0 c1| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rcases le_total c1 c0 with h1 | h1 <;> rcases le_total c1_q c0_q with h2 | h2
    · rw [max_eq_left h1, max_eq_left h2]
      exact ha_err
    · rw [max_eq_left h1, max_eq_right h2, abs_le]
      constructor <;> linarith
    · rw [max_eq_right h1, max_eq_left h2, abs_le]
      constructor <;> linarith
    · rw [max_eq_right h1, max_eq_right h2]
      exact hb_err
  have hmin_err : |min c0_q c1_q - min c0 c1| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rcases le_total c1 c0 with h1 | h1 <;> rcases le_total c1_q c0_q with h2 | h2
    · rw [min_eq_right h1, min_eq_right h2]
      exact hb_err
    · rw [min_eq_right h1, min_eq_left h2, abs_le]
      constructor <;> linarith
    · rw [min_eq_left h1, min_eq_right h2, abs_le]
      constructor <;> linarith
    · rw [min_eq_left h1, min_eq_left h2]
      exact ha_err
  have hmax_bds := abs_le.mp hmax_err
  have hmax_q_ge : (44 / 100 : ℝ) ≤ max c0_q c1_q := by linarith
  have hmax_q_pos : 0 < max c0_q c1_q := by linarith
  have hmax_pos : 0 < max c0 c1 := by linarith
  have hmin_q_nn : 0 ≤ min c0_q c1_q := le_min hc0q_nn hc1q_nn
  set r_q : ℝ := min c0_q c1_q / max c0_q c1_q
  set r : ℝ := min c0 c1 / max c0 c1
  have hrq_0 : 0 ≤ r_q := div_nonneg hmin_q_nn (le_of_lt hmax_q_pos)
  have hrq_1 : r_q ≤ 1 := div_le_one_of_le₀ min_le_max (le_of_lt hmax_q_pos)
  have hr_0 : 0 ≤ r := div_nonneg hcmin (le_of_lt hmax_pos)
  have hr_1 : r ≤ 1 := div_le_one_of_le₀ min_le_max (le_of_lt hmax_pos)
  have hr_diff_eq :
      r_q - r =
        ((min c0_q c1_q - min c0 c1) + r * (max c0 c1 - max c0_q c1_q)) / max c0_q c1_q := by
    dsimp [r_q, r]
    have hne1 : max c0_q c1_q ≠ 0 := ne_of_gt hmax_q_pos
    have hne2 : max c0 c1 ≠ 0 := ne_of_gt hmax_pos
    field_simp
    ring
  have hr_diff_le : |r_q - r| ≤ (5 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rw [hr_diff_eq, abs_div, abs_of_pos hmax_q_pos, div_le_iff₀ hmax_q_pos]
    have htri := abs_add_le (min c0_q c1_q - min c0 c1) (r * (max c0 c1 - max c0_q c1_q))
    have hrmul : |r * (max c0 c1 - max c0_q c1_q)| ≤ 1 * ((11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) := by
      rw [abs_mul, abs_of_nonneg hr_0, abs_sub_comm]
      exact mul_le_mul hr_1 hmax_err (abs_nonneg _) zero_le_one
    have hden :
        (5 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (44 / 100 : ℝ) ≤
          (5 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * max c0_q c1_q :=
      mul_le_mul_of_nonneg_left hmax_q_ge (by positivity)
    linarith
  have hpow_diff := abs_pow_sub_pow_le hrq_0 hrq_1 hr_0 hr_1 t1
  have hpow_diff_le : |r_q ^ t1 - r ^ t1| ≤ (5 / 2 : ℝ) * ((t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) := by
    have hmul := mul_le_mul_of_nonneg_left hr_diff_le (by positivity : (0 : ℝ) ≤ (t1 : ℝ))
    linarith
  have hpow_hi := (abs_le.mp hpow_diff_le).2
  exact ⟨hmax_q_ge, hmin_q_nn, by linarith⟩

/-- Under the conditioning bounds of Theorem 5.1 (`thm:deconv`) and $2.36 \, t_1 \cdot 2^{-q} \le 1/2$, the quantized
weights $\tilde{c}_0 = \text{quantizeReal } q \, c_0$ and $\tilde{c}_1 = \text{quantizeReal } q \, c_1$
preserve strict dominance ($0 < \max(\tilde{c}_0, \tilde{c}_1)$, $0 \le \min(\tilde{c}_0, \tilde{c}_1)$,
and $(\min(\tilde{c}_0, \tilde{c}_1) / \max(\tilde{c}_0, \tilde{c}_1))^{t_1} < 1$). -/
theorem quantizeReal_weights_invertible {t1 : ℕ} [NeZero t1] {q : ℕ} {c0 c1 : ℝ}
    (hcmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1)
    (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 ≤ 15 / 100)
    (hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 2) :
    0 < max (quantizeReal q c0) (quantizeReal q c1) ∧
      0 ≤ min (quantizeReal q c0) (quantizeReal q c1) ∧
      (min (quantizeReal q c0) (quantizeReal q c1) /
        max (quantizeReal q c0) (quantizeReal q c1)) ^ t1 < 1 := by
  have ht1_pos_nat : 0 < t1 := NeZero.pos t1
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr ht1_pos_nat
  have hcmax_pos : 0 < max c0 c1 := by linarith
  have hc0_nn : 0 ≤ c0 := le_trans hcmin (min_le_left c0 c1)
  have hc1_nn : 0 ≤ c1 := le_trans hcmin (min_le_right c0 c1)
  set c0_q := quantizeReal q c0
  set c1_q := quantizeReal q c1
  have hc0q_nn : 0 ≤ c0_q := quantizeReal_nonneg q hc0_nn
  have hc1q_nn : 0 ≤ c1_q := quantizeReal_nonneg q hc1_nn
  have hmin_q_nn : 0 ≤ min c0_q c1_q := le_min hc0q_nn hc1q_nn
  set r : ℝ := min c0 c1 / max c0 c1
  have hr0 : 0 ≤ r := div_nonneg hcmin (le_of_lt hcmax_pos)
  have hr1 : r ≤ 1 := div_le_one_of_le₀ (min_le_max) (le_of_lt hcmax_pos)
  have hbern := one_sub_pow_le_nat_mul_one_sub hr0 hr1 t1
  have h1mr_eq : 1 - r = (max c0 c1 - min c0 c1) / max c0 c1 := by
    simp only [r]
    rw [one_sub_div (ne_of_gt hcmax_pos)]
  rw [h1mr_eq] at hbern
  have hgap_div : (85 / 100 : ℝ) ≤ (t1 : ℝ) * ((max c0 c1 - min c0 c1) / max c0 c1) := by
    linarith
  have hgap_t1 : (2 / 5 : ℝ) ≤ (t1 : ℝ) * (max c0 c1 - min c0 c1) := by
    have hmul := mul_le_mul_of_nonneg_right hgap_div (le_of_lt hcmax_pos)
    have hcancel :
        (t1 : ℝ) * ((max c0 c1 - min c0 c1) / max c0 c1) * max c0 c1 =
          (t1 : ℝ) * (max c0 c1 - min c0 c1) := by
      have hne : max c0 c1 ≠ 0 := ne_of_gt hcmax_pos
      field_simp
    rw [hcancel] at hmul
    nlinarith
  have hprec_lt : (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) < (t1 : ℝ) * (max c0 c1 - min c0 c1) := by
    linarith
  have hpow_lt_gap : (2 : ℝ) ^ (-(q : ℤ)) < max c0 c1 - min c0 c1 :=
    lt_of_mul_lt_mul_left hprec_lt (le_of_lt ht1_pos)
  have herr0 := abs_quantizeReal_sub_le_half_zpow q c0
  have herr1 := abs_quantizeReal_sub_le_half_zpow q c1
  rw [abs_le] at herr0 herr1
  have hne_q : c0_q ≠ c1_q := by
    intro heq
    rcases le_total c1 c0 with hle | hle
    · have hmax_eq : max c0 c1 = c0 := max_eq_left hle
      have hmin_eq : min c0 c1 = c1 := min_eq_right hle
      rw [hmax_eq, hmin_eq] at hpow_lt_gap
      linarith
    · have hmax_eq : max c0 c1 = c1 := max_eq_right hle
      have hmin_eq : min c0 c1 = c0 := min_eq_left hle
      rw [hmax_eq, hmin_eq] at hpow_lt_gap
      linarith
  have hmin_lt_max_q : min c0_q c1_q < max c0_q c1_q := by
    rcases lt_or_gt_of_ne hne_q with hlt | hgt
    · rwa [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
    · rwa [min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt)]
  have hmax_q_pos : 0 < max c0_q c1_q := lt_of_le_of_lt hmin_q_nn hmin_lt_max_q
  have hdiv_q_nn : 0 ≤ min c0_q c1_q / max c0_q c1_q :=
    div_nonneg hmin_q_nn (le_of_lt hmax_q_pos)
  have hdiv_q_lt : min c0_q c1_q / max c0_q c1_q < 1 :=
    (div_lt_one hmax_q_pos).mpr hmin_lt_max_q
  exact ⟨hmax_q_pos, hmin_q_nn, pow_lt_one₀ hdiv_q_nn hdiv_q_lt (NeZero.ne t1)⟩

/-- **Quantized Step 3 Forward-Shift Solver Approximation Bound with Mantissa Tolerance
(`vecInfNorm_cyclicBidiagSolveQuantWithMantissa_sub_le_of_bounds`, Section 5.2 (`sec:solvers`) and
Lemma 5.2 (`lem:solver-err`))**:
Under the conditioning hypotheses of Theorem 5.1 (`thm:deconv`) (`hcmax`, `hcmax_le`, `hcmin`, `hq`),
precision condition `hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4`, and
mantissa bounds `|(a : ℝ) * 2^(-q) - c0|, |(b : ℝ) * 2^(-q) - c1| ≤ (11 / 20) * 2^(-q)`, the
$O(t_1)$ single-pass solver `cyclicBidiagSolveQuantWithMantissa q a b B` approximates
`cyclicBidiagSolve c0 c1 B` within:
$$\|\text{cyclicBidiagSolveQuantWithMantissa } q \, a \, b \, B - \text{cyclicBidiagSolve } c_0 \, c_1 \, B\|_\infty
\le 2^{-q} + 2 \cdot (2.36 \, t_1 \cdot 2^{-q}) \left(1 + \|\text{cyclicBidiagSolve } c_0 \, c_1 \, B\|_\infty\right).$$ -/
theorem vecInfNorm_cyclicBidiagSolveQuantWithMantissa_sub_le_of_bounds
    {t1 : ℕ} [NeZero t1] {q : ℕ} {c0 c1 : ℝ} {a b : ℤ}
    (hcmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1)
    (hcmax_le : max c0 c1 ≤ 1)
    (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 ≤ 15 / 100)
    (hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4)
    (ha_err : |(a : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) - c0| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hb_err : |(b : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) - c1| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (ha_nn : 0 ≤ (a : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hb_nn : 0 ≤ (b : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (B : Fin t1 → ℂ) :
    vecInfNorm (fun u1 =>
      cyclicBidiagSolveQuantWithMantissa q a b B u1 - cyclicBidiagSolve c0 c1 B u1) ≤
      (2 : ℝ) ^ (-(q : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) *
          (1 + vecInfNorm (cyclicBidiagSolve c0 c1 B)) := by
  have ht1_pos : 0 < t1 := NeZero.pos t1
  have ht1_ge1 : 1 ≤ t1 := NeZero.one_le
  have ht1_ge1_r : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1_ge1
  have hcmax_pos : 0 < max c0 c1 := by linarith
  have hq_lt1 : (min c0 c1 / max c0 c1) ^ t1 < 1 := by linarith
  set c0_q : ℝ := (a : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  set c1_q : ℝ := (b : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  obtain ⟨hmax_q_ge, hmin_q_nn, hq_q_le⟩ :=
    mantissa_weights_invertible_and_ratio_pow_le hcmax hcmin hq hq_prec ha_err hb_err ha_nn hb_nn
  have hmax_q_pos : 0 < max c0_q c1_q := by linarith
  have hq_q_lt1 : (min c0_q c1_q / max c0_q c1_q) ^ t1 < 1 := by linarith
  set B_q : Fin t1 → ℂ := fun m => quantizeComplex q (B m)
  set W : Fin t1 → ℂ := cyclicBidiagSolve c0 c1 B
  set W_mid : Fin t1 → ℂ := cyclicBidiagSolve c0_q c1_q B_q
  set D : Fin t1 → ℂ := fun m => W_mid m - W m
  set R : Fin t1 → ℂ := fun m =>
    (B_q m - B m) +
      (((c0 - c0_q : ℝ) : ℂ) * W_mid m + ((c1 - c1_q : ℝ) : ℂ) * W_mid (cyclicNext m))
  have hD_rec : ∀ m : Fin t1, (c0 : ℂ) * D m + (c1 : ℂ) * D (cyclicNext m) = R m := by
    intro m
    have hW := cyclicBidiagSolve_spec c0 c1 B hcmax_pos hcmin hq_lt1 m
    have hW_mid := cyclicBidiagSolve_spec c0_q c1_q B_q hmax_q_pos hmin_q_nn hq_q_lt1 m
    simp only [D, R, W, W_mid]
    push_cast
    linear_combination hW_mid - hW
  have hD_eq : D = cyclicBidiagSolve c0 c1 R :=
    (cyclicBidiagSolve_of_spec c0 c1 R D hcmax_pos hcmin hq_lt1 hD_rec).symm
  have hD_cond : vecInfNorm D ≤ (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm R := by
    rw [hD_eq]
    exact deconvolution_conditioning_le_236_t1_of_bounds c0 c1 R hcmax hcmin hq
  have hW_mid_nn : 0 ≤ vecInfNorm W_mid := vecInfNorm_nonneg W_mid
  have hW_nn : 0 ≤ vecInfNorm W := vecInfNorm_nonneg W
  have hzpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have hzpow_le : (2 : ℝ) ^ (-(q : ℤ)) ≤ 25 / 236 := by
    have h1 : 1 * (2 : ℝ) ^ (-(q : ℤ)) ≤ (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) :=
      mul_le_mul_of_nonneg_right ht1_ge1_r (le_of_lt hzpow_pos)
    linarith
  have hc0_le1 : c0 ≤ 1 := (le_max_left c0 c1).trans hcmax_le
  have hc1_le1 : c1 ≤ 1 := (le_max_right c0 c1).trans hcmax_le
  have hc0q_le2 : c0_q ≤ 2 := by
    have h := (abs_le.mp ha_err).2
    linarith
  have hc1q_le2 : c1_q ≤ 2 := by
    have h := (abs_le.mp hb_err).2
    linarith
  have hR_bound : vecInfNorm R ≤ (11 / 10 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (1 + vecInfNorm W_mid) := by
    rw [vecInfNorm_le_iff _ (by positivity)]
    intro m
    have hBm : ‖B_q m - B m‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) :=
      norm_quantizeComplex_sub_le_pow q (B m)
    have herr0 : ‖((c0 - c0_q : ℝ) : ℂ)‖ ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact ha_err
    have herr1 : ‖((c1 - c1_q : ℝ) : ℂ)‖ ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact hb_err
    have hWm : ‖W_mid m‖ ≤ vecInfNorm W_mid := norm_le_vecInfNorm W_mid m
    have hWnext : ‖W_mid (cyclicNext m)‖ ≤ vecInfNorm W_mid :=
      norm_le_vecInfNorm W_mid (cyclicNext m)
    have hmul0 :
        ‖((c0 - c0_q : ℝ) : ℂ) * W_mid m‖ ≤
          (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm W_mid := by
      rw [norm_mul]
      exact mul_le_mul herr0 hWm (norm_nonneg _) (by positivity)
    have hmul1 :
        ‖((c1 - c1_q : ℝ) : ℂ) * W_mid (cyclicNext m)‖ ≤
          (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm W_mid := by
      rw [norm_mul]
      exact mul_le_mul herr1 hWnext (norm_nonneg _) (by positivity)
    have htri1 := norm_add_le (B_q m - B m)
      (((c0 - c0_q : ℝ) : ℂ) * W_mid m + ((c1 - c1_q : ℝ) : ℂ) * W_mid (cyclicNext m))
    have htri2 := norm_add_le (((c0 - c0_q : ℝ) : ℂ) * W_mid m)
      (((c1 - c1_q : ℝ) : ℂ) * W_mid (cyclicNext m))
    linarith
  have hW_mid_le : vecInfNorm W_mid ≤ vecInfNorm W + vecInfNorm D := by
    have heq : W_mid = fun m => W m + D m := by
      ext m
      simp [D]
    rw [heq]
    exact vecInfNorm_add_le W D
  have ht1_q : (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 2 := by linarith
  set δ : ℝ := (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  have hδ_nn : 0 ≤ δ := by positivity
  have hD_step : vecInfNorm D ≤ (11 / 10 : ℝ) * δ * (1 + vecInfNorm W + vecInfNorm D) := by
    calc
      vecInfNorm D ≤ (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm R := hD_cond
      _ ≤ (236 / 100 : ℝ) * (t1 : ℝ) *
            ((11 / 10 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (1 + vecInfNorm W_mid)) :=
        mul_le_mul_of_nonneg_left hR_bound (by positivity)
      _ = (11 / 10 : ℝ) * δ * (1 + vecInfNorm W_mid) := by ring
      _ ≤ (11 / 10 : ℝ) * δ * (1 + (vecInfNorm W + vecInfNorm D)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (11 / 10 : ℝ) * δ * (1 + vecInfNorm W + vecInfNorm D) := by ring
  have hD_nn : 0 ≤ vecInfNorm D := vecInfNorm_nonneg D
  have hδD : δ * vecInfNorm D ≤ (1 / 4 : ℝ) * vecInfNorm D :=
    mul_le_mul_of_nonneg_right hq_prec hD_nn
  have hD_bound : vecInfNorm D ≤ (44 / 29 : ℝ) * δ * (1 + vecInfNorm W) := by linarith
  have hδ_1W : δ * (1 + vecInfNorm W) ≤ (1 / 4 : ℝ) * (1 + vecInfNorm W) :=
    mul_le_mul_of_nonneg_right hq_prec (by positivity)
  have h1W_mid_le : 1 + vecInfNorm W_mid ≤ (40 / 29 : ℝ) * (1 + vecInfNorm W) := by linarith
  have hsweep_bound : ∀ u1 : Fin t1,
      ‖cyclicBidiagSolveQuantWithMantissa q a b B u1 - W_mid u1‖ ≤
        (2 : ℝ) ^ (-(q : ℤ)) +
          (1 / 16 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (1 + vecInfNorm W_mid) := by
    intro u1
    unfold cyclicBidiagSolveQuantWithMantissa
    dsimp only
    by_cases hba : b ≤ a
    · rw [if_pos hba]
      have hc_le : c1_q ≤ c0_q := by
        dsimp [c0_q, c1_q]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hba) (le_of_lt hzpow_pos)
      have hc0_pos : 0 < c0_q := by rwa [max_eq_left hc_le] at hmax_q_pos
      have hr_pow : (c1_q / c0_q) ^ t1 ≤ 4 / 5 := by
        rwa [min_eq_right hc_le, max_eq_left hc_le] at hq_q_le
      set W_seq : ℕ → ℂ := fun s => W_mid ⟨(t1 - s % t1) % t1, Nat.mod_lt _ ht1_pos⟩
      set B_seq : ℕ → ℂ := fun s => B_q ⟨(t1 - 1 - s % t1) % t1, Nat.mod_lt _ ht1_pos⟩
      set idx : Fin t1 → ℕ := fun v => (t1 - v.val) % t1
      have hW_per : W_seq t1 = W_seq 0 := by simp [W_seq]
      have hW_b : ∀ s : ℕ, ‖W_seq s‖ ≤ vecInfNorm W_mid := fun s => norm_le_vecInfNorm W_mid _
      have hW_rec : ∀ s < t1,
          W_seq (s + 1) = B_seq s / (c0_q : ℂ) + ((-c1_q / c0_q : ℝ) : ℂ) * W_seq s := by
        intro s hs
        set m : Fin t1 := ⟨t1 - 1 - s, by omega⟩
        have hspec := cyclicBidiagSolve_spec c0_q c1_q B_q hmax_q_pos hmin_q_nn hq_q_lt1 m
        have hB_eq : B_seq s = B_q m := by
          dsimp [B_seq, m]
          congr 1
          apply Fin.ext
          dsimp only
          rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (by omega)]
        have hWs1_eq : W_seq (s + 1) = W_mid m := by
          dsimp [W_seq, m]
          congr 1
          apply Fin.ext
          dsimp only
          by_cases hs1 : s + 1 = t1
          · rw [hs1, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
            omega
          · have hlt : s + 1 < t1 := by omega
            rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)]
            omega
        have hWs_eq : W_seq s = W_mid (cyclicNext m) := by
          dsimp [W_seq, cyclicNext, m]
          congr 1
          apply Fin.ext
          dsimp only
          rw [Nat.mod_eq_of_lt hs]
          congr 1
          omega
        rw [hB_eq, hWs1_eq, hWs_eq]
        have hc0_c_ne : (c0_q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc0_pos)
        apply mul_left_cancel₀ hc0_c_ne
        push_cast
        have h1 : (c0_q : ℂ) * (B_q m / (c0_q : ℂ) + (- (c1_q : ℂ) / (c0_q : ℂ)) * W_mid (cyclicNext m)) =
            B_q m - (c1_q : ℂ) * W_mid (cyclicNext m) := by
          field_simp
          ring
        rw [h1]
        linear_combination hspec
      have hidx_le : ∀ v : Fin t1, idx v ≤ t1 := fun v => le_of_lt (Nat.mod_lt _ ht1_pos)
      have hW_idx : W_seq (idx u1) = W_mid u1 := by
        dsimp [W_seq, idx]
        congr 1
        apply Fin.ext
        dsimp only
        by_cases hu0 : u1.val = 0
        · simp [hu0]
        · have hlt : t1 - u1.val < t1 := by omega
          have hsub : t1 - (t1 - u1.val) = u1.val := by omega
          rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, hsub, Nat.mod_eq_of_lt u1.isLt]
      rw [← hW_idx]
      exact norm_bidiagSweepQuant_sub_le ht1_ge1 a b hb_nn hc_le hc0_pos hc0q_le2 hr_pow ht1_q
        B_seq W_seq (vecInfNorm W_mid) hW_mid_nn hW_per hW_b
        (by simpa [c0_q, c1_q, neg_div] using hW_rec) idx hidx_le u1
    · rw [if_neg hba]
      have hab : a < b := not_le.mp hba
      have hc_le : c0_q ≤ c1_q := by
        dsimp [c0_q, c1_q]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (le_of_lt hab)) (le_of_lt hzpow_pos)
      have hc1_pos : 0 < c1_q := by rwa [max_eq_right hc_le] at hmax_q_pos
      have hr_pow : (c0_q / c1_q) ^ t1 ≤ 4 / 5 := by
        rwa [min_eq_left hc_le, max_eq_right hc_le] at hq_q_le
      set W_seq : ℕ → ℂ := fun s => W_mid ⟨s % t1, Nat.mod_lt _ ht1_pos⟩
      set B_seq : ℕ → ℂ := fun s => B_q ⟨s % t1, Nat.mod_lt _ ht1_pos⟩
      set idx : Fin t1 → ℕ := fun v => v.val
      have hW_per : W_seq t1 = W_seq 0 := by simp [W_seq]
      have hW_b : ∀ s : ℕ, ‖W_seq s‖ ≤ vecInfNorm W_mid := fun s => norm_le_vecInfNorm W_mid _
      have hW_rec : ∀ s < t1,
          W_seq (s + 1) = B_seq s / (c1_q : ℂ) + ((-c0_q / c1_q : ℝ) : ℂ) * W_seq s := by
        intro s hs
        set m : Fin t1 := ⟨s, hs⟩
        have hspec := cyclicBidiagSolve_spec c0_q c1_q B_q hmax_q_pos hmin_q_nn hq_q_lt1 m
        have hB_eq : B_seq s = B_q m := by
          dsimp [B_seq, m]
          congr 1
          ext
          exact Nat.mod_eq_of_lt hs
        have hWs_eq : W_seq s = W_mid m := by
          dsimp [W_seq, m]
          congr 1
          ext
          exact Nat.mod_eq_of_lt hs
        have hWs1_eq : W_seq (s + 1) = W_mid (cyclicNext m) := rfl
        rw [hB_eq, hWs_eq, hWs1_eq]
        have hc1_c_ne : (c1_q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc1_pos)
        apply mul_left_cancel₀ hc1_c_ne
        push_cast
        have h1 : (c1_q : ℂ) * (B_q m / (c1_q : ℂ) + (- (c0_q : ℂ) / (c1_q : ℂ)) * W_mid m) =
            B_q m - (c0_q : ℂ) * W_mid m := by
          field_simp
          ring
        rw [h1]
        linear_combination hspec
      have hidx_le : ∀ v : Fin t1, idx v ≤ t1 := fun v => le_of_lt v.isLt
      have hW_idx : W_seq (idx u1) = W_mid u1 := by
        dsimp [W_seq, idx]
        congr 1
        ext
        exact Nat.mod_eq_of_lt u1.isLt
      rw [← hW_idx]
      exact norm_bidiagSweepQuant_sub_le ht1_ge1 b a ha_nn hc_le hc1_pos hc1q_le2 hr_pow ht1_q
        B_seq W_seq (vecInfNorm W_mid) hW_mid_nn hW_per hW_b
        (by simpa [c0_q, c1_q, neg_div] using hW_rec) idx hidx_le u1
  rw [vecInfNorm_le_iff _ (by positivity)]
  intro u1
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (cyclicBidiagSolveQuantWithMantissa q a b B u1) (W_mid u1) (W u1)
  have hs_u1 := hsweep_bound u1
  have hD_u1 : ‖W_mid u1 - W u1‖ ≤ vecInfNorm D := norm_le_vecInfNorm D u1
  have hs_le_δ :
      (1 / 16 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (1 + vecInfNorm W_mid) ≤
        (1 / 30 : ℝ) * δ * (1 + vecInfNorm W_mid) := by
    dsimp [δ]
    nlinarith
  have hs_le_W :
      (1 / 30 : ℝ) * δ * (1 + vecInfNorm W_mid) ≤
        (4 / 87 : ℝ) * δ * (1 + vecInfNorm W) := by
    have hmul := mul_le_mul_of_nonneg_left h1W_mid_le (by positivity : (0 : ℝ) ≤ (1 / 30 : ℝ) * δ)
    linarith
  linarith

/-- **Quantized Step 3 Forward-Shift Solver Approximation Bound
(`vecInfNorm_cyclicBidiagSolveQuant_sub_le_of_bounds`, Section 5.2 (`sec:solvers`) and Lemma 5.2 (`lem:solver-err`))**:
Under the conditioning hypotheses of Theorem 5.1 (`thm:deconv`) (`hcmax`, `hcmax_le`, `hcmin`, `hq`)
and precision condition `hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4`, the
$q$-bit quantized solver `cyclicBidiagSolveQuant q c0 c1 B` approximates the exact solver
`cyclicBidiagSolve c0 c1 B` within:
$$\|\text{cyclicBidiagSolveQuant } q \, c_0 \, c_1 \, B - \text{cyclicBidiagSolve } c_0 \, c_1 \, B\|_\infty
\le 2^{-q} + 2 \cdot (2.36 \, t_1 \cdot 2^{-q}) \left(1 + \|\text{cyclicBidiagSolve } c_0 \, c_1 \, B\|_\infty\right).$$ -/
theorem vecInfNorm_cyclicBidiagSolveQuant_sub_le_of_bounds {t1 : ℕ} [NeZero t1] {q : ℕ} {c0 c1 : ℝ}
    (hcmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1)
    (hcmax_le : max c0 c1 ≤ 1)
    (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 ≤ 15 / 100)
    (hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4)
    (B : Fin t1 → ℂ) :
    vecInfNorm (fun u1 =>
      cyclicBidiagSolveQuant q c0 c1 B u1 - cyclicBidiagSolve c0 c1 B u1) ≤
      (2 : ℝ) ^ (-(q : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) *
          (1 + vecInfNorm (cyclicBidiagSolve c0 c1 B)) := by
  have hzpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have herr0 := abs_quantizeReal_sub_le_half_zpow q c0
  have herr1 := abs_quantizeReal_sub_le_half_zpow q c1
  have hc0_nn : 0 ≤ c0 := le_trans hcmin (min_le_left c0 c1)
  have hc1_nn : 0 ≤ c1 := le_trans hcmin (min_le_right c0 c1)
  exact vecInfNorm_cyclicBidiagSolveQuantWithMantissa_sub_le_of_bounds
    hcmax hcmax_le hcmin hq hq_prec
    (by change |quantizeReal q c0 - c0| ≤ _; linarith)
    (by change |quantizeReal q c1 - c1| ≤ _; linarith)
    (quantizeReal_nonneg q hc0_nn)
    (quantizeReal_nonneg q hc1_nn)
    B

/-- **Quantized Step 3 Backward-Shift Solver Approximation Bound with Mantissa Tolerance
(`vecInfNorm_cyclicBidiagPrevSolveQuantWithMantissa_sub_le_of_bounds`, Section 5.2 (`sec:solvers`)
and Lemma 5.2 (`lem:solver-err`))**:
Bounds the $\ell_\infty$ forward error of `cyclicBidiagPrevSolveQuantWithMantissa` relative to
`cyclicBidiagPrevSolve` under 1-ulp mantissa tolerances. -/
theorem vecInfNorm_cyclicBidiagPrevSolveQuantWithMantissa_sub_le_of_bounds
    {t1 : ℕ} [NeZero t1] {q : ℕ} {c0 c1 : ℝ} {a b : ℤ}
    (hcmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1)
    (hcmax_le : max c0 c1 ≤ 1)
    (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 ≤ 15 / 100)
    (hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4)
    (ha_err : |(a : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) - c0| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hb_err : |(b : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) - c1| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (ha_nn : 0 ≤ (a : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (hb_nn : 0 ≤ (b : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (B : Fin t1 → ℂ) :
    vecInfNorm (fun u1 =>
      cyclicBidiagPrevSolveQuantWithMantissa q a b B u1 - cyclicBidiagPrevSolve c0 c1 B u1) ≤
      (2 : ℝ) ^ (-(q : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) *
          (1 + vecInfNorm (cyclicBidiagPrevSolve c0 c1 B)) := by
  have hcmax' : (49999999 / 100000000 : ℝ) ≤ max c1 c0 := by rwa [max_comm]
  have hcmax_le' : max c1 c0 ≤ 1 := by rwa [max_comm]
  have hcmin' : 0 ≤ min c1 c0 := by rwa [min_comm]
  have hq' : (min c1 c0 / max c1 c0) ^ t1 ≤ 15 / 100 := by
    rwa [min_comm, max_comm]
  exact vecInfNorm_cyclicBidiagSolveQuantWithMantissa_sub_le_of_bounds
    hcmax' hcmax_le' hcmin' hq' hq_prec hb_err ha_err hb_nn ha_nn (fun m => B (cyclicNext m))

/-- **Quantized Step 3 Backward-Shift Solver Approximation Bound
(`vecInfNorm_cyclicBidiagPrevSolveQuant_sub_le_of_bounds`, Section 5.2 (`sec:solvers`) and
Lemma 5.2 (`lem:solver-err`))**:
Bounds the $\ell_\infty$ forward error of `cyclicBidiagPrevSolveQuant` relative to `cyclicBidiagPrevSolve`. -/
theorem vecInfNorm_cyclicBidiagPrevSolveQuant_sub_le_of_bounds {t1 : ℕ} [NeZero t1] {q : ℕ} {c0 c1 : ℝ}
    (hcmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1)
    (hcmax_le : max c0 c1 ≤ 1)
    (hcmin : 0 ≤ min c0 c1)
    (hq : (min c0 c1 / max c0 c1) ^ t1 ≤ 15 / 100)
    (hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4)
    (B : Fin t1 → ℂ) :
    vecInfNorm (fun u1 =>
      cyclicBidiagPrevSolveQuant q c0 c1 B u1 - cyclicBidiagPrevSolve c0 c1 B u1) ≤
      (2 : ℝ) ^ (-(q : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) *
          (1 + vecInfNorm (cyclicBidiagPrevSolve c0 c1 B)) := by
  have hcmax' : (49999999 / 100000000 : ℝ) ≤ max c1 c0 := by rwa [max_comm]
  have hcmax_le' : max c1 c0 ≤ 1 := by rwa [max_comm]
  have hcmin' : 0 ≤ min c1 c0 := by rwa [min_comm]
  have hq' : (min c1 c0 / max c1 c0) ^ t1 ≤ 15 / 100 := by
    rwa [min_comm, max_comm]
  exact vecInfNorm_cyclicBidiagSolveQuant_sub_le_of_bounds hcmax' hcmax_le' hcmin' hq' hq_prec
    (fun m => B (cyclicNext m))

/-- **Quantized Step 3 Nyquist Column Solver Approximation Bound with Mantissa Tolerance
(`vecInfNorm_nyquistColumnSolveQuantWithMantissa_sub_le_of_bounds`, Section 5.2 (`sec:solvers`) and
Lemma 5.2 (`lem:solver-err`))**:
Bounds the $\ell_\infty$ forward error of `nyquistColumnSolveQuantWithMantissa` relative to
`nyquistColumnSolve` under mantissa and right-hand-side quantization tolerances. -/
theorem vecInfNorm_nyquistColumnSolveQuantWithMantissa_sub_le_of_bounds
    {t1 : ℕ} [NeZero t1] {q : ℕ} {c0 : ℝ} {a : ℤ}
    (hc0 : (49999999 / 100000000 : ℝ) ≤ c0)
    (hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4)
    (ha_err : |(a : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) - c0| ≤ (11 / 20 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (B : Fin t1 → ℂ) (altTrue : ℂ) :
    vecInfNorm (fun u1 =>
      nyquistColumnSolveQuantWithMantissa q a B altTrue u1 - nyquistColumnSolve c0 B altTrue u1) ≤
      (2 : ℝ) ^ (-(q : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) *
          (1 + vecInfNorm B) := by
  have ht1_pos_nat : 1 ≤ t1 := NeZero.one_le
  have ht1_ge1 : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1_pos_nat
  have ht1_pos : (0 : ℝ) < (t1 : ℝ) := by linarith
  have hzpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have hB_nn : 0 ≤ vecInfNorm B := vecInfNorm_nonneg B
  have hq_base : (236 / 100 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4 := by
    have hle :
        (236 / 100 : ℝ) * 1 * (2 : ℝ) ^ (-(q : ℤ)) ≤
          (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hzpow_pos)
      linarith
    linarith
  set qWork : ℕ := q + 4
  have hzpow_w_eq : (2 : ℝ) ^ (-(qWork : ℤ)) = (1 / 16 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hexp : -(qWork : ℤ) = (-4 : ℤ) + -(q : ℤ) := by dsimp [qWork]; omega
    rw [hexp, zpow_add₀ (by norm_num)]
    norm_num
  set c0_q : ℝ := (a : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  set invC0_q : ℝ := quantizeReal qWork (c0_q⁻¹)
  set B_q : Fin t1 → ℂ := fun m => quantizeComplex q (B m)
  set B_scaled : Fin t1 → ℂ := fun m => quantizeComplex qWork ((invC0_q : ℂ) * B_q m)
  set alt_q : ℂ := quantizeComplex q altTrue
  set Z_mid : Fin t1 → ℂ := nyquistColumnSolve 1 B_scaled alt_q
  have herr0_bounds := abs_le.mp ha_err
  have hc0_pos : (0 : ℝ) < c0 := by linarith
  have hc0_q_ge : (44 / 100 : ℝ) ≤ c0_q := by linarith
  have hc0_q_pos : (0 : ℝ) < c0_q := by linarith
  have hc0_q_inv_le : c0_q⁻¹ ≤ (25 / 11 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀' hc0_q_pos]
    linarith
  have hprod_ge : (21 / 100 : ℝ) ≤ c0_q * c0 := by nlinarith
  have hprod_pos : (0 : ℝ) < c0_q * c0 := by linarith
  have hinv_diff_eq : c0_q⁻¹ - c0⁻¹ = (c0 - c0_q) / (c0_q * c0) :=
    inv_sub_inv (ne_of_gt hc0_q_pos) (ne_of_gt hc0_pos)
  have hinv_diff_le : |c0_q⁻¹ - c0⁻¹| ≤ (55 / 21 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rw [hinv_diff_eq, abs_div, abs_of_pos hprod_pos, abs_sub_comm]
    rw [div_le_iff₀ hprod_pos]
    have hmul2 :
        (55 / 21 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (21 / 100 : ℝ) ≤
          (55 / 21 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (c0_q * c0) :=
      mul_le_mul_of_nonneg_left hprod_ge (by positivity)
    linarith
  have hinv_q_err : |invC0_q - c0_q⁻¹| ≤ (1 / 32 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have h1 := abs_quantizeReal_sub_le_half_zpow qWork (c0_q⁻¹)
    rw [hzpow_w_eq] at h1
    linarith
  have hinv_q_bds := abs_le.mp hinv_q_err
  have hinv_q_nn : 0 ≤ invC0_q :=
    quantizeReal_nonneg qWork (le_of_lt (inv_pos.mpr hc0_q_pos))
  have hinv_q_le : invC0_q ≤ (5 / 2 : ℝ) := by linarith
  have hzpow_B_nn : 0 ≤ (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm B :=
    mul_nonneg (le_of_lt hzpow_pos) hB_nn
  set R_nyq : Fin t1 → ℂ := fun m => (1 : ℂ)⁻¹ * B_scaled m - (c0 : ℂ)⁻¹ * B m
  have hR_bound :
      vecInfNorm R_nyq ≤
        (13 / 5 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) +
          (27 / 10 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm B := by
    rw [vecInfNorm_le_iff _ (by positivity)]
    intro m
    have hsplit_m :
        R_nyq m =
          (B_scaled m - (invC0_q : ℂ) * B_q m) +
            (((invC0_q : ℝ) : ℂ) * (B_q m - B m) +
              (((invC0_q - c0_q⁻¹ : ℝ) : ℂ) * B m +
                ((c0_q⁻¹ - c0⁻¹ : ℝ) : ℂ) * B m)) := by
      simp only [R_nyq, inv_one, one_mul]
      push_cast
      ring
    rw [hsplit_m]
    have hBsc : ‖B_scaled m - (invC0_q : ℂ) * B_q m‖ ≤ (1 / 16 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
      have h1 := norm_quantizeComplex_sub_le_pow qWork ((invC0_q : ℂ) * B_q m)
      rwa [hzpow_w_eq] at h1
    have hBm : ‖B_q m - B m‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) :=
      norm_quantizeComplex_sub_le_pow q (B m)
    have hBm_norm : ‖B m‖ ≤ vecInfNorm B := norm_le_vecInfNorm B m
    have hterm1 :
        ‖((invC0_q : ℝ) : ℂ) * (B_q m - B m)‖ ≤
          (5 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hinv_q_nn]
      exact mul_le_mul hinv_q_le hBm (norm_nonneg _) (by norm_num)
    have hterm2 :
        ‖((invC0_q - c0_q⁻¹ : ℝ) : ℂ) * B m‖ ≤
          (1 / 32 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm B := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hinv_q_err hBm_norm (norm_nonneg _) (by positivity)
    have hterm3 :
        ‖((c0_q⁻¹ - c0⁻¹ : ℝ) : ℂ) * B m‖ ≤
          (55 / 21 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm B := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hinv_diff_le hBm_norm (norm_nonneg _) (by positivity)
    have htri1 := norm_add_le (B_scaled m - (invC0_q : ℂ) * B_q m)
      (((invC0_q : ℝ) : ℂ) * (B_q m - B m) +
        (((invC0_q - c0_q⁻¹ : ℝ) : ℂ) * B m + ((c0_q⁻¹ - c0⁻¹ : ℝ) : ℂ) * B m))
    have htri2 := norm_add_le (((invC0_q : ℝ) : ℂ) * (B_q m - B m))
      (((invC0_q - c0_q⁻¹ : ℝ) : ℂ) * B m + ((c0_q⁻¹ - c0⁻¹ : ℝ) : ℂ) * B m)
    have htri3 := norm_add_le (((invC0_q - c0_q⁻¹ : ℝ) : ℂ) * B m)
      (((c0_q⁻¹ - c0⁻¹ : ℝ) : ℂ) * B m)
    linarith
  have halt_err : ‖alt_q - altTrue‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) :=
    norm_quantizeComplex_sub_le_pow q altTrue
  have halt_div : ‖alt_q - altTrue‖ / (t1 : ℝ) ≤ (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have h1 : ‖alt_q - altTrue‖ / (t1 : ℝ) ≤ ‖alt_q - altTrue‖ / 1 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) ht1_ge1
    have h2 : (2 : ℝ) ^ (-(q : ℤ)) ≤ (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
      nlinarith
    linarith
  have hmid_diff_eq :
      (fun u1 => Z_mid u1 - nyquistColumnSolve c0 B altTrue u1) =
        nyquistColumnSolve 1 R_nyq (alt_q - altTrue) := by
    ext u1
    exact nyquistColumnSolve_sub_eq_one 1 c0 B_scaled B alt_q altTrue u1
  have hmid_le :
      vecInfNorm (fun u1 => Z_mid u1 - nyquistColumnSolve c0 B altTrue u1) ≤
        (18 / 5 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) +
          (27 / 10 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm B := by
    rw [hmid_diff_eq]
    have h1 := vecInfNorm_nyquistColumnSolve_le (by norm_num : (0 : ℝ) < 1) R_nyq (alt_q - altTrue)
    have h2 :
        ((t1 : ℝ) / 1) * vecInfNorm R_nyq ≤
          (t1 : ℝ) *
            ((13 / 5 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) +
              (27 / 10 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm B) := by
      rw [div_one]
      exact mul_le_mul_of_nonneg_left hR_bound (le_of_lt ht1_pos)
    linarith
  rw [vecInfNorm_le_iff _ (by positivity)]
  intro u1
  set altPart : ℂ := ∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticular 1 B_scaled m
  set corr : ℂ := quantizeComplex qWork ((alt_q - altPart) / (t1 : ℂ))
  set Z_tilde : ℂ := nyquistOpenChainParticular 1 B_scaled u1 + (-1 : ℂ) ^ u1.val * corr
  have hnyq_eq : nyquistColumnSolveQuantWithMantissa q a B altTrue u1 = quantizeComplex q Z_tilde :=
    nyquistColumnSolveQuantWithMantissa_eq q a B altTrue u1
  have hZ_tilde_sub :
      Z_tilde - Z_mid u1 =
        (-1 : ℂ) ^ u1.val *
          (quantizeComplex qWork ((alt_q - altPart) / (t1 : ℂ)) - (alt_q - altPart) / (t1 : ℂ)) := by
    dsimp [Z_tilde, Z_mid, nyquistColumnSolve, corr, altPart]
    ring
  have hZ_tilde_err : ‖Z_tilde - Z_mid u1‖ ≤ (1 / 16 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rw [hZ_tilde_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 := norm_quantizeComplex_sub_le_pow qWork ((alt_q - altPart) / (t1 : ℂ))
    rw [hzpow_w_eq] at h1
    have h2 : (2 : ℝ) ^ (-(q : ℤ)) ≤ (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
      have : 1 * (2 : ℝ) ^ (-(q : ℤ)) ≤ (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) :=
        mul_le_mul_of_nonneg_right ht1_ge1 (le_of_lt hzpow_pos)
      linarith
    linarith
  have hmid_u1 : ‖Z_mid u1 - nyquistColumnSolve c0 B altTrue u1‖ ≤
      (18 / 5 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) +
        (27 / 10 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm B :=
    (norm_le_vecInfNorm (fun v => Z_mid v - nyquistColumnSolve c0 B altTrue v) u1).trans hmid_le
  have hout_q : ‖quantizeComplex q Z_tilde - Z_tilde‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) :=
    norm_quantizeComplex_sub_le_pow q Z_tilde
  have htri1 := norm_sub_le_norm_sub_add_norm_sub
    (quantizeComplex q Z_tilde) Z_tilde (nyquistColumnSolve c0 B altTrue u1)
  have htri2 := norm_sub_le_norm_sub_add_norm_sub
    Z_tilde (Z_mid u1) (nyquistColumnSolve c0 B altTrue u1)
  rw [hnyq_eq]
  have hprod_pos_b : 0 ≤ (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * vecInfNorm B := by positivity
  have hprod_pos_1 : 0 ≤ (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by positivity
  linarith

/-- **Quantized Step 3 Nyquist Column Solver Approximation Bound
(`vecInfNorm_nyquistColumnSolveQuant_sub_le_of_bounds`, Section 5.2 (`sec:solvers`) and
Lemma 5.2 (`lem:solver-err`))**:
Bounds the $\ell_\infty$ forward error of `nyquistColumnSolveQuant` relative to `nyquistColumnSolve`. -/
theorem vecInfNorm_nyquistColumnSolveQuant_sub_le_of_bounds {t1 : ℕ} [NeZero t1] {q : ℕ} {c0 : ℝ}
    (hc0 : (49999999 / 100000000 : ℝ) ≤ c0)
    (hq_prec : (236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 4)
    (B : Fin t1 → ℂ) (altTrue : ℂ) :
    vecInfNorm (fun u1 =>
      nyquistColumnSolveQuant q c0 B altTrue u1 - nyquistColumnSolve c0 B altTrue u1) ≤
      (2 : ℝ) ^ (-(q : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) *
          (1 + vecInfNorm B) := by
  have hzpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have herr0 := abs_quantizeReal_sub_le_half_zpow q c0
  exact vecInfNorm_nyquistColumnSolveQuantWithMantissa_sub_le_of_bounds hc0 hq_prec
    (by change |quantizeReal q c0 - c0| ≤ _; linarith) B altTrue

/-- At any level $(K, p)$, the schedule precision $q_{\text{child}} = \text{qChildEll } K \, p$
unconditionally satisfies the Step 3 quantization precision requirement
$2.36 \, t_{1,\ell} \cdot 2^{-q_{\text{child}}} \le 1/4$. -/
theorem qChildEll_step3_precision_le_quarter (K p : ℕ) :
    (236 / 100 : ℝ) * (t1Ell K : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) ≤ 1 / 4 := by
  have ht1_le : (t1Ell K : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by
    unfold t1Ell
    have hk1 : k1Ell K ≤ K := by
      unfold k1Ell
      omega
    exact Nat.cast_le.mpr (Nat.pow_le_pow_right (by norm_num) hk1)
  have hq_ge : K + 14 ≤ qChildEll K p := by
    unfold qChildEll pChildEll pWorkEll
    omega
  have hzpow_le : (2 : ℝ) ^ (-(qChildEll K p : ℤ)) ≤ (2 : ℝ) ^ (-(K : ℤ) + (-14 : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hzpow_split :
      (2 : ℝ) ^ (-(K : ℤ) + (-14 : ℤ)) =
        (2 : ℝ) ^ (-(K : ℤ)) * (1 / 16384 : ℝ) := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
  have hprod :
      (t1Ell K : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) ≤ (1 / 16384 : ℝ) := by
    calc
      (t1Ell K : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))
        ≤ ((2 ^ K : ℕ) : ℝ) * ((2 : ℝ) ^ (-(K : ℤ)) * (1 / 16384 : ℝ)) := by
          rw [← hzpow_split]
          exact mul_le_mul ht1_le hzpow_le (by positivity) (by positivity)
      _ = (((2 : ℝ) ^ K) * (2 : ℝ) ^ (-(K : ℤ))) * (1 / 16384 : ℝ) := by
          push_cast
          ring
      _ = (1 / 16384 : ℝ) := by
          rw [two_pow_mul_two_zpow_neg K, one_mul]
  linarith

/-- Corollary: $2.36 \, t_{1,\ell} \cdot 2^{-q_{\text{child}}} \le 1/2$. -/
theorem qChildEll_step3_precision_le_half (K p : ℕ) :
    (236 / 100 : ℝ) * (t1Ell K : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) ≤ 1 / 2 := by
  have := qChildEll_step3_precision_le_quarter K p
  linarith

/-! ## 5. Inductive Precision Recurrence & Error Contraction (Lemma 6.5(1)–(2) (`lem:forward`), Section 6.3 (`sec:forward-error`)) -/

/-- Upper bound `t1Ell K ≤ 2 ^ K`. -/
theorem t1Ell_le_two_pow (K : ℕ) : t1Ell K ≤ 2 ^ K := by
  unfold t1Ell
  have hk1 : k1Ell K ≤ K := by
    unfold k1Ell
    omega
  exact Nat.pow_le_pow_right (by norm_num) hk1

/-- When $K \ge 1$, $t_{1,\ell} \cdot 2^{-K} \le 1/2$. -/
theorem t1Ell_mul_two_zpow_neg_K_le_half {K : ℕ} (hK : 1 ≤ K) :
    (t1Ell K : ℝ) * (2 : ℝ) ^ (-(K : ℤ)) ≤ (1 / 2 : ℝ) := by
  have hk2 : 1 ≤ k2Ell K := by
    unfold k2Ell
    omega
  have hr : 2 ≤ rEll K := by
    unfold rEll
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k2Ell K := Nat.pow_le_pow_right (by norm_num) hk2
  have hprod : 2 * t1Ell K ≤ 2 ^ K := by
    calc
      2 * t1Ell K = t1Ell K * 2 := mul_comm _ _
      _ ≤ t1Ell K * rEll K := Nat.mul_le_mul_left (t1Ell K) hr
      _ = 2 ^ K := t1Ell_mul_rEll K
  have hreal : 2 * (t1Ell K : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast hprod
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ (-(K : ℤ)) := zpow_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_right hreal (le_of_lt hzpos)
  rw [two_pow_mul_two_zpow_neg] at hmul
  linarith

/-- When $K \ge 1$, $t_{1,\ell} \cdot 2^{-p_{\text{work},\ell}} \le \frac{1}{128} 2^{-p_\ell}$. -/
theorem t1Ell_mul_two_zpow_neg_pWorkEll_le {K p : ℕ} (hK : 1 ≤ K) :
    (t1Ell K : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ)) ≤
      (1 / 128 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have hexp : -(pWorkEll K p : ℤ) = -(K : ℤ) + (-6 : ℤ) + -(p : ℤ) := by
    unfold pWorkEll
    push_cast
    ring
  have hzpow : (2 : ℝ) ^ (-(pWorkEll K p : ℤ)) =
      (2 : ℝ) ^ (-(K : ℤ)) * (1 / 64 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    norm_num
  rw [hzpow]
  have h1 := t1Ell_mul_two_zpow_neg_K_le_half hK
  have hp_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  calc
    (t1Ell K : ℝ) * ((2 : ℝ) ^ (-(K : ℤ)) * (1 / 64 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)))
      = ((t1Ell K : ℝ) * (2 : ℝ) ^ (-(K : ℤ))) * ((1 / 64 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) := by ring
    _ ≤ (1 / 2 : ℝ) * ((1 / 64 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (1 / 128 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by ring

/-- Exact exponent cancellation $(2^K)^2 \cdot 2^{-p_{\text{child}}} = \frac{1}{4096} 2^{-p}$. -/
theorem two_pow_sq_mul_two_zpow_neg_pChildEll (K p : ℕ) :
    ((2 ^ K : ℕ) : ℝ) * ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(pChildEll K p : ℤ)) =
      (1 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have hexp : -(pChildEll K p : ℤ) = -((2 * K : ℕ) : ℤ) + (-12 : ℤ) + -(p : ℤ) := by
    rw [pChildEll_eq]
    push_cast
    ring
  have hzpow : (2 : ℝ) ^ (-(pChildEll K p : ℤ)) =
      (2 : ℝ) ^ (-((2 * K : ℕ) : ℤ)) * (1 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    norm_num
  have hsq : ((2 ^ K : ℕ) : ℝ) * ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ (2 * K) := by
    push_cast
    rw [← pow_add, two_mul]
  rw [hzpow, hsq]
  calc
    (2 : ℝ) ^ (2 * K) * ((2 : ℝ) ^ (-((2 * K : ℕ) : ℤ)) * (1 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)))
      = ((2 : ℝ) ^ (2 * K) * (2 : ℝ) ^ (-((2 * K : ℕ) : ℤ))) *
          ((1 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) := by ring
    _ = (1 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
      rw [two_pow_mul_two_zpow_neg (2 * K), one_mul]

/-- At any level $(K, p)$, the window half-width $m_{1,\ell} = \lceil \alpha_\ell \sqrt{p_{\ell+1} \ln 2 / \pi} \rceil$
is at most the child precision $p_{\ell+1} = p + 2K + 12$. -/
theorem m1Ell_le_pChildEll (K p : ℕ) : m1Ell K p ≤ pChildEll K p := by
  unfold m1Ell m1FromPWorkPChild alphaFromPWork
  rw [Nat.ceil_le]
  set pW : ℕ := pWorkEll K p
  set pC : ℕ := pChildEll K p
  have hpW_le_pC : pW ≤ pC := by
    dsimp [pW, pC]
    unfold pChildEll pWorkEll
    omega
  have hlog_pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_lt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hpi_gt : 3 < Real.pi := Real.pi_gt_three
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hmono :
      Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) ≤
        Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) := by
    refine Real.sqrt_le_sqrt ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hpW_le_pC) hlog_pos.le) hpi_pos.le
  have hsq :
      Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) *
        Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) =
        ((pC : ℝ) * Real.log 2) / Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hprod_le :
      2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) *
        Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) ≤
        2 * (((pC : ℝ) * Real.log 2) / Real.pi) := by
    have hsqrt_nn : 0 ≤ Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) := Real.sqrt_nonneg _
    calc
      2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) *
          Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi)
        ≤ 2 * Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) *
            Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) := by nlinarith
      _ = 2 * (((pC : ℝ) * Real.log 2) / Real.pi) := by rw [mul_assoc, hsq]
  have hdiv_le : 2 * (((pC : ℝ) * Real.log 2) / Real.pi) ≤ (pC : ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ hpi_pos]
    have hpC_nn : (0 : ℝ) ≤ (pC : ℝ) := Nat.cast_nonneg pC
    nlinarith
  linarith

/-- At any level $(K, p)$, the untruncated window length $W_\ell = 2 m_{1,\ell} + 1$
satisfies $W_\ell \le 2 p_{\ell+1} + 1$. -/
theorem windowLengthEll_le_two_mul_pChildEll_add_one (K p : ℕ) :
    windowLengthEll K p ≤ 2 * pChildEll K p + 1 := by
  unfold windowLengthEll windowLength
  have h := m1Ell_le_pChildEll K p
  omega

/-- Under the non-leaf condition $4 p^2 < 2^K$ (Lemma 6.5(1) (`lem:forward`)), the child-precision terms satisfy
$t_{1,\ell} (2 W_\ell + 0.54 K_\ell + 11) 2^{-p_{\ell+1}} \le \frac{74}{4096} 2^{-p_\ell}$. -/
theorem child_terms_mul_two_zpow_neg_pChildEll_le {K p : ℕ}
    (hp : 1 ≤ p) (hleaf : 4 * p * p < 2 ^ K) :
    (t1Ell K : ℝ) *
      (2 * (windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 11) *
      (2 : ℝ) ^ (-(pChildEll K p : ℤ)) ≤
      (74 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have hp_le : p ≤ 2 ^ K := by nlinarith
  have hK_le : K ≤ 2 ^ K := le_of_lt (Nat.lt_two_pow_self)
  have h1_le : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  set R : ℝ := ((2 ^ K : ℕ) : ℝ)
  have hR_nn : 0 ≤ R := Nat.cast_nonneg _
  have ht1_le : (t1Ell K : ℝ) ≤ R := Nat.cast_le.mpr (t1Ell_le_two_pow K)
  have hp_cast : (p : ℝ) ≤ R := Nat.cast_le.mpr hp_le
  have hK_cast : (K : ℝ) ≤ R := Nat.cast_le.mpr hK_le
  have h1_cast : (1 : ℝ) ≤ R := by
    simpa [R] using (Nat.cast_le.mpr h1_le : ((1 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ))
  have hW_nat : windowLengthEll K p ≤ 2 * p + 4 * K + 25 := by
    have h1 := windowLengthEll_le_two_mul_pChildEll_add_one K p
    have h2 := pChildEll_eq K p
    omega
  have hW_cast : (windowLengthEll K p : ℝ) ≤ 2 * (p : ℝ) + 4 * (K : ℝ) + 25 := by
    exact_mod_cast hW_nat
  have hW_le_R : (windowLengthEll K p : ℝ) ≤ 31 * R := by linarith
  have hcoeff_bound :
      2 * (windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 11 ≤ 74 * R := by
    linarith
  have hprod_bound :
      (t1Ell K : ℝ) *
        (2 * (windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 11) ≤
      74 * (R * R) := by
    calc
      (t1Ell K : ℝ) *
          (2 * (windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 11)
        ≤ R * (74 * R) :=
          mul_le_mul ht1_le hcoeff_bound (by positivity) (by positivity)
      _ = 74 * (R * R) := by ring
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ (-(pChildEll K p : ℤ)) := zpow_pos (by norm_num) _
  calc
    (t1Ell K : ℝ) *
        (2 * (windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 11) *
        (2 : ℝ) ^ (-(pChildEll K p : ℤ))
      ≤ 74 * (((2 ^ K : ℕ) : ℝ) * ((2 ^ K : ℕ) : ℝ)) * (2 : ℝ) ^ (-(pChildEll K p : ℤ)) :=
        mul_le_mul_of_nonneg_right hprod_bound (le_of_lt hzpos)
    _ = 74 * (((2 ^ K : ℕ) : ℝ) * ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(pChildEll K p : ℤ))) := by
        ring
    _ = (74 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
        rw [two_pow_sq_mul_two_zpow_neg_pChildEll]
        ring

/-- **Per-Level Error Budget Contraction (`level_error_budget_le`, Lemma 6.5(1)–(2) (`lem:forward`),
equations (35) (`eq:forward-split`) and (36) (`eq:inductive-bound`))**:
For any non-leaf level $(K, p)$ with $1 \le K$, $1 \le p$, and $4 p^2 < 2^K$, the combined
four-source error amplified by $2.36 \, t_{1,\ell}$ plus final $(p + 2)$-bit output quantization
is strictly bounded by $0.43 \cdot 2^{-p} \le 2^{-p}$:
$$2.36 \, t_1 \left( (W_\ell + 4) 2^{-p_{\text{child}}} + (W_\ell + 0.54 K + 7) 2^{-p_{\text{child}}} + 0.91 \cdot 2^{-p_{\text{work}}} \right) + \frac{\sqrt{2}}{4} 2^{-p} \le 2^{-p}.$$ -/
theorem level_error_budget_le {K p : ℕ}
    (hK : 1 ≤ K) (hp : 1 ≤ p) (hleaf : 4 * p * p < 2 ^ K) :
    (236 / 100 : ℝ) * (t1Ell K : ℝ) *
      ((((windowLengthEll K p : ℝ) + 4) * (2 : ℝ) ^ (-(pChildEll K p : ℤ))) +
        ((windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 7) *
          (2 : ℝ) ^ (-(pChildEll K p : ℤ)) +
        (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ))) +
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) ≤
      (2 : ℝ) ^ (-(p : ℤ)) := by
  have hwork := t1Ell_mul_two_zpow_neg_pWorkEll_le (p := p) hK
  have hchild := child_terms_mul_two_zpow_neg_pChildEll_le hp hleaf
  have hquant := sqrt_two_div_four_le
  have hp_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hexpand :
      (236 / 100 : ℝ) * (t1Ell K : ℝ) *
        ((((windowLengthEll K p : ℝ) + 4) * (2 : ℝ) ^ (-(pChildEll K p : ℤ))) +
          ((windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 7) *
            (2 : ℝ) ^ (-(pChildEll K p : ℤ)) +
          (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ))) =
      (236 / 100 : ℝ) * (91 / 100 : ℝ) * ((t1Ell K : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ))) +
        (236 / 100 : ℝ) *
          ((t1Ell K : ℝ) *
            (2 * (windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 11) *
            (2 : ℝ) ^ (-(pChildEll K p : ℤ))) := by ring
  rw [hexpand]
  have hterm1 :
      (236 / 100 : ℝ) * (91 / 100 : ℝ) * ((t1Ell K : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ))) ≤
      (236 / 100 : ℝ) * (91 / 100 : ℝ) * ((1 / 128 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) :=
    mul_le_mul_of_nonneg_left hwork (by norm_num)
  have hterm2 :
      (236 / 100 : ℝ) *
        ((t1Ell K : ℝ) *
          (2 * (windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 11) *
          (2 : ℝ) ^ (-(pChildEll K p : ℤ))) ≤
      (236 / 100 : ℝ) * ((74 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) :=
    mul_le_mul_of_nonneg_left hchild (by norm_num)
  have hterm3 :
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) ≤ (18 / 50 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) :=
    mul_le_mul_of_nonneg_right hquant (le_of_lt hp_pos)
  linarith

/-- Corollary of `level_error_budget_le` for the 4-component error decomposition without $W_\ell$:
$$2.36 \, t_1 \left( (0.76 + 0.15) 2^{-p_{\text{work}}} + (p_{\text{work}} + 0.54 K) 2^{-p_{\text{child}}} \right) + \frac{\sqrt{2}}{4} 2^{-p} \le 2^{-p}.$$ -/
theorem level_error_budget_four_source_le {K p : ℕ}
    (hK : 1 ≤ K) (hp : 1 ≤ p) (hleaf : 4 * p * p < 2 ^ K) :
    (236 / 100 : ℝ) * (t1Ell K : ℝ) *
      (((76 / 100 : ℝ) + (15 / 100 : ℝ)) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ)) +
        ((pWorkEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ)) *
          (2 : ℝ) ^ (-(pChildEll K p : ℤ))) +
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) ≤
      (2 : ℝ) ^ (-(p : ℤ)) := by
  have hfull := level_error_budget_le hK hp hleaf
  set pW : ℕ := pWorkEll K p
  set pC : ℕ := pChildEll K p
  have hpW_le_pC : pW ≤ pC := by
    dsimp [pW, pC]
    unfold pChildEll pWorkEll
    omega
  have hlog_gt : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpi_lt : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hmono :
      Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) ≤
        Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) := by
    refine Real.sqrt_le_sqrt ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hpW_le_pC) (by linarith)) hpi_pos.le
  have hceil :
      2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) *
        Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) ≤ (m1Ell K p : ℝ) :=
    Nat.le_ceil _
  have hsq :
      Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) *
        Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) =
        ((pW : ℝ) * Real.log 2) / Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hm1_ge : 2 * (((pW : ℝ) * Real.log 2) / Real.pi) ≤ (m1Ell K p : ℝ) := by
    have h1 :
        2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) *
          Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) ≤
        2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) *
          Real.sqrt (((pC : ℝ) * Real.log 2) / Real.pi) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    have h2 :
        2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) *
          Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi) =
        2 * (((pW : ℝ) * Real.log 2) / Real.pi) := by
      rw [mul_assoc, hsq]
    linarith
  have hW_cast : (pWorkEll K p : ℝ) ≤ 2 * (windowLengthEll K p : ℝ) + 11 := by
    have hWin : (windowLengthEll K p : ℝ) = 2 * (m1Ell K p : ℝ) + 1 := by
      unfold windowLengthEll windowLength
      push_cast
      ring
    rw [hWin]
    have hmul := mul_le_mul_of_nonneg_left hm1_ge hpi_pos.le
    have hcancel :
        Real.pi * (2 * (((pW : ℝ) * Real.log 2) / Real.pi)) =
          2 * (pW : ℝ) * Real.log 2 := by
      field_simp [hpi_pos.ne']
    rw [hcancel] at hmul
    have hpW_nn : (0 : ℝ) ≤ (pW : ℝ) := Nat.cast_nonneg pW
    have hm1_nn : (0 : ℝ) ≤ (m1Ell K p : ℝ) := Nat.cast_nonneg _
    dsimp [pW] at hmul hpW_nn ⊢
    nlinarith
  have hz_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(pChildEll K p : ℤ)) := le_of_lt (zpow_pos (by norm_num) _)
  have ht1_nn : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1Ell K : ℝ) := by positivity
  have hdiff_nn :
      (0 : ℝ) ≤ (2 * (windowLengthEll K p : ℝ) + 11 - (pWorkEll K p : ℝ)) *
        (2 : ℝ) ^ (-(pChildEll K p : ℤ)) :=
    mul_nonneg (by linarith) hz_nn
  have hextra := mul_nonneg ht1_nn hdiff_nn
  linarith

/-- Base-case leaf FFT internal precision $q_{\text{base}} = p + K + 4$
(Algorithm 1 (`alg:main`), Lemma 6.5(2) (`lem:forward`)). -/
def qBaseEll (K p : ℕ) : ℕ :=
  p + K + 4

/-- Base-case leaf error budget ($R_\ell \le 4 p_\ell^2$): direct schoolbook evaluation at precision
$q_{\text{base}} = p_\ell + K_\ell + 4$ plus final $(p_\ell + 2)$-bit quantization has total error
$\le (\frac{\sqrt{2}}{16} + \frac{\sqrt{2}}{4}) 2^{-p_\ell} \le 0.45 \cdot 2^{-p_\ell} \le 2^{-p_\ell}$. -/
theorem base_leaf_error_budget_le (K p : ℕ) :
    ((2 ^ K : ℕ) : ℝ) * Real.sqrt 2 * (2 : ℝ) ^ (-(qBaseEll K p : ℤ)) +
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) ≤
      (2 : ℝ) ^ (-(p : ℤ)) := by
  have hexp : -(qBaseEll K p : ℤ) = -(K : ℤ) + (-4 : ℤ) + -(p : ℤ) := by
    unfold qBaseEll
    push_cast
    ring
  have hzpow : (2 : ℝ) ^ (-(qBaseEll K p : ℤ)) =
      (2 : ℝ) ^ (-(K : ℤ)) * (1 / 16 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    norm_num
  have hcancel : ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(K : ℤ)) = 1 := by
    push_cast
    exact two_pow_mul_two_zpow_neg K
  have hrew :
      ((2 ^ K : ℕ) : ℝ) * Real.sqrt 2 * (2 : ℝ) ^ (-(qBaseEll K p : ℤ)) =
      (Real.sqrt 2 / 16) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [hzpow]
    calc
      ((2 ^ K : ℕ) : ℝ) * Real.sqrt 2 *
          ((2 : ℝ) ^ (-(K : ℤ)) * (1 / 16 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)))
        = (((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(K : ℤ))) *
            ((Real.sqrt 2 / 16) * (2 : ℝ) ^ (-(p : ℤ))) := by ring
      _ = (Real.sqrt 2 / 16) * (2 : ℝ) ^ (-(p : ℤ)) := by rw [hcancel, one_mul]
  rw [hrew]
  have hsqrt := sqrt_two_le
  have hp_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hsum : (Real.sqrt 2 / 16 + Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) ≤
      1 * (2 : ℝ) ^ (-(p : ℤ)) := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hp_pos)
    linarith
  linarith

/-- Predicate capturing a valid multi-level recursive DFT error propagation family
from `L = recursionDepth K0 p0` down to the root $\ell = 0$, including the four-source
non-leaf error recurrence with $W_\ell$ (Lemma 6.5(1)–(2) (`lem:forward`), Section 6.3 (`sec:forward-error`)). -/
def ValidLevelErrorRecurrence (K0 p0 : ℕ) (err : ℕ → ℝ) : Prop :=
  err (recursionDepth K0 p0) ≤
    (2 : ℝ) ^ (-(levelP K0 p0 (recursionDepth K0 p0) : ℤ)) ∧
  ∀ ell < recursionDepth K0 p0,
    err ell ≤
      (236 / 100 : ℝ) * (t1Ell (levelK K0 ell) : ℝ) *
        ((((windowLengthEll (levelK K0 ell) (levelP K0 p0 ell) : ℝ) + 4) * err (ell + 1)) +
          ((windowLengthEll (levelK K0 ell) (levelP K0 p0 ell) : ℝ) +
            (54 / 100 : ℝ) * (levelK K0 ell : ℝ) + 7) *
            (2 : ℝ) ^ (-(pChildEll (levelK K0 ell) (levelP K0 p0 ell) : ℤ)) +
          (91 / 100 : ℝ) *
            (2 : ℝ) ^ (-(pWorkEll (levelK K0 ell) (levelP K0 p0 ell) : ℤ))) +
        (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(levelP K0 p0 ell : ℤ))

/-- At any non-leaf level $\ell < \text{recursionDepth } K_0 \, p_0$ with $p_0 \ge 1$,
the log-length satisfies $2 \le K_\ell$ (since $K_\ell \le 1 \implies R_\ell \le 2 < 4 \le 4 p_\ell^2$). -/
theorem two_le_levelK_of_lt_recursionDepth {K0 p0 ell : ℕ} (hp0 : 1 ≤ p0)
    (hlt : ell < recursionDepth K0 p0) : 2 ≤ levelK K0 ell := by
  have hleaf := four_mul_sq_lt_levelR_of_lt_recursionDepth K0 p0 ell hlt
  unfold levelR at hleaf
  have hp_cur : 1 ≤ levelP K0 p0 ell := le_trans hp0 (levelP_ge_p0 K0 p0 ell)
  have h4 : 4 < 2 ^ levelK K0 ell := by nlinarith
  by_contra hK
  have hK_le : levelK K0 ell ≤ 1 := by omega
  have hpow : 2 ^ levelK K0 ell ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hK_le
  omega

/-- At any non-leaf level $\ell < \text{recursionDepth } K_0 \, p_0$ with $p_0 \ge 1$,
the log-length satisfies $1 \le K_\ell$ (since $K_\ell = 0 \implies R_\ell = 1 \le 4 p_\ell^2$). -/
theorem one_le_levelK_of_lt_recursionDepth {K0 p0 ell : ℕ} (hp0 : 1 ≤ p0)
    (hlt : ell < recursionDepth K0 p0) : 1 ≤ levelK K0 ell :=
  le_trans (by norm_num) (two_le_levelK_of_lt_recursionDepth hp0 hlt)

/-- Concrete multi-level recursive DFT error schedule (`concreteLevelError`,
Lemma 6.5(1)–(2) (`lem:forward`), Section 6.3 (`sec:forward-error`)):
- For $\ell \ge \text{recursionDepth } K_0 \, p_0$, equals the positive base-leaf
  error budget $R_\ell \sqrt{2} \cdot 2^{-q_{\text{base},\ell}} + \frac{\sqrt{2}}{4} 2^{-p_\ell}$.
- For $\ell < \text{recursionDepth } K_0 \, p_0$, equals the 4-source deconvolution
  error recurrence from `concreteLevelError K0 p0 (ell + 1)`. -/
noncomputable def concreteLevelError (K0 p0 : ℕ) (ell : ℕ) : ℝ :=
  if ell < recursionDepth K0 p0 then
    (236 / 100 : ℝ) * (t1Ell (levelK K0 ell) : ℝ) *
      ((((windowLengthEll (levelK K0 ell) (levelP K0 p0 ell) : ℝ) + 4) *
          concreteLevelError K0 p0 (ell + 1)) +
        ((windowLengthEll (levelK K0 ell) (levelP K0 p0 ell) : ℝ) +
          (54 / 100 : ℝ) * (levelK K0 ell : ℝ) + 7) *
          (2 : ℝ) ^ (-(pChildEll (levelK K0 ell) (levelP K0 p0 ell) : ℤ)) +
        (91 / 100 : ℝ) *
          (2 : ℝ) ^ (-(pWorkEll (levelK K0 ell) (levelP K0 p0 ell) : ℤ))) +
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(levelP K0 p0 ell : ℤ))
  else
    ((2 ^ levelK K0 ell : ℕ) : ℝ) * Real.sqrt 2 *
      (2 : ℝ) ^ (-(qBaseEll (levelK K0 ell) (levelP K0 p0 ell) : ℤ)) +
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(levelP K0 p0 ell : ℤ))
termination_by recursionDepth K0 p0 - ell

/-- Unfolding equation for `concreteLevelError` at leaf levels $\ell \ge \text{recursionDepth } K_0 \, p_0$. -/
theorem concreteLevelError_of_ge {K0 p0 ell : ℕ} (h : recursionDepth K0 p0 ≤ ell) :
    concreteLevelError K0 p0 ell =
      ((2 ^ levelK K0 ell : ℕ) : ℝ) * Real.sqrt 2 *
        (2 : ℝ) ^ (-(qBaseEll (levelK K0 ell) (levelP K0 p0 ell) : ℤ)) +
        (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(levelP K0 p0 ell : ℤ)) := by
  rw [concreteLevelError]
  simp [not_lt.mpr h]

/-- Unfolding equation for `concreteLevelError` at internal levels $\ell < \text{recursionDepth } K_0 \, p_0$. -/
theorem concreteLevelError_of_lt {K0 p0 ell : ℕ} (h : ell < recursionDepth K0 p0) :
    concreteLevelError K0 p0 ell =
      (236 / 100 : ℝ) * (t1Ell (levelK K0 ell) : ℝ) *
        ((((windowLengthEll (levelK K0 ell) (levelP K0 p0 ell) : ℝ) + 4) *
            concreteLevelError K0 p0 (ell + 1)) +
          ((windowLengthEll (levelK K0 ell) (levelP K0 p0 ell) : ℝ) +
            (54 / 100 : ℝ) * (levelK K0 ell : ℝ) + 7) *
            (2 : ℝ) ^ (-(pChildEll (levelK K0 ell) (levelP K0 p0 ell) : ℤ)) +
          (91 / 100 : ℝ) *
            (2 : ℝ) ^ (-(pWorkEll (levelK K0 ell) (levelP K0 p0 ell) : ℤ))) +
        (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(levelP K0 p0 ell : ℤ)) := by
  rw [concreteLevelError]
  simp [h]

/-- Every level of `concreteLevelError` is strictly positive (`0 < concreteLevelError K0 p0 ell`). -/
theorem concreteLevelError_pos (K0 p0 ell : ℕ) : 0 < concreteLevelError K0 p0 ell := by
  by_cases h : ell < recursionDepth K0 p0
  · rw [concreteLevelError_of_lt h]
    have hchild : 0 < concreteLevelError K0 p0 (ell + 1) := concreteLevelError_pos K0 p0 (ell + 1)
    positivity
  · rw [concreteLevelError_of_ge (not_lt.mp h)]
    positivity
termination_by recursionDepth K0 p0 - ell

/-- Proof that the concrete multi-level error schedule `concreteLevelError K0 p0` satisfies
`ValidLevelErrorRecurrence K0 p0` for all $K_0, p_0 \ge 1$. -/
theorem validLevelErrorRecurrence_concreteLevelError (K0 p0 : ℕ)
    (hK0 : 1 ≤ K0) (hp0 : 1 ≤ p0) :
    ValidLevelErrorRecurrence K0 p0 (concreteLevelError K0 p0) := by
  have _ := hK0
  have _ := hp0
  refine ⟨?_, ?_⟩
  · rw [concreteLevelError_of_ge (le_refl _)]
    exact base_leaf_error_budget_le _ _
  · intro ell hell
    rw [concreteLevelError_of_lt hell]

/-- **Conditional Inductive Accuracy Closure (`inductive_accuracy_closure_of_validLevelErrorRecurrence`,
Lemma 6.5(2) (`lem:forward`), equation (36) (`eq:inductive-bound`))**:
Whenever `hp0 : 1 ≤ p0` and `err : ℕ → ℝ` satisfies `hrec : ValidLevelErrorRecurrence K0 p0 err`
(the base-case leaf bound at $L = \text{recursionDepth } K_0 \, p_0$ and the 4-source
per-level deconvolution error recurrence for all $\ell < L$), every level $\ell \le L$ satisfies:
$$\text{err}(\ell) \le 2^{-p_\ell}.$$ -/
theorem inductive_accuracy_closure_of_validLevelErrorRecurrence {K0 p0 : ℕ} (hp0 : 1 ≤ p0)
    {err : ℕ → ℝ} (hrec : ValidLevelErrorRecurrence K0 p0 err) :
    ∀ ell ≤ recursionDepth K0 p0,
      err ell ≤ (2 : ℝ) ^ (-(levelP K0 p0 ell : ℤ)) := by
  have hmain : ∀ d ≤ recursionDepth K0 p0,
      err (recursionDepth K0 p0 - d) ≤
        (2 : ℝ) ^ (-(levelP K0 p0 (recursionDepth K0 p0 - d) : ℤ)) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      exact hrec.1
    | succ d ih =>
      intro hd
      set cur : ℕ := recursionDepth K0 p0 - (d + 1)
      have hcur_lt : cur < recursionDepth K0 p0 := by omega
      have hcur_succ : cur + 1 = recursionDepth K0 p0 - d := by omega
      have hchild : err (cur + 1) ≤ (2 : ℝ) ^ (-(levelP K0 p0 (cur + 1) : ℤ)) := by
        rw [hcur_succ]
        exact ih (by omega)
      have hstep := hrec.2 cur hcur_lt
      have hleaf := four_mul_sq_lt_levelR_of_lt_recursionDepth K0 p0 cur hcur_lt
      unfold levelR at hleaf
      have hp_cur : 1 ≤ levelP K0 p0 cur := le_trans hp0 (levelP_ge_p0 K0 p0 cur)
      have hK_cur : 1 ≤ levelK K0 cur := one_le_levelK_of_lt_recursionDepth hp0 hcur_lt
      have hp_child_eq : levelP K0 p0 (cur + 1) = pChildEll (levelK K0 cur) (levelP K0 p0 cur) := rfl
      rw [hp_child_eq] at hchild
      have hmono :
          (236 / 100 : ℝ) * (t1Ell (levelK K0 cur) : ℝ) *
            ((((windowLengthEll (levelK K0 cur) (levelP K0 p0 cur) : ℝ) + 4) * err (cur + 1)) +
              ((windowLengthEll (levelK K0 cur) (levelP K0 p0 cur) : ℝ) +
                (54 / 100 : ℝ) * (levelK K0 cur : ℝ) + 7) *
                (2 : ℝ) ^ (-(pChildEll (levelK K0 cur) (levelP K0 p0 cur) : ℤ)) +
              (91 / 100 : ℝ) *
                (2 : ℝ) ^ (-(pWorkEll (levelK K0 cur) (levelP K0 p0 cur) : ℤ))) +
            (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(levelP K0 p0 cur : ℤ)) ≤
          (236 / 100 : ℝ) * (t1Ell (levelK K0 cur) : ℝ) *
            ((((windowLengthEll (levelK K0 cur) (levelP K0 p0 cur) : ℝ) + 4) *
                (2 : ℝ) ^ (-(pChildEll (levelK K0 cur) (levelP K0 p0 cur) : ℤ))) +
              ((windowLengthEll (levelK K0 cur) (levelP K0 p0 cur) : ℝ) +
                (54 / 100 : ℝ) * (levelK K0 cur : ℝ) + 7) *
                (2 : ℝ) ^ (-(pChildEll (levelK K0 cur) (levelP K0 p0 cur) : ℤ)) +
              (91 / 100 : ℝ) *
                (2 : ℝ) ^ (-(pWorkEll (levelK K0 cur) (levelP K0 p0 cur) : ℤ))) +
            (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(levelP K0 p0 cur : ℤ)) := by
        have hcoeff_nn : (0 : ℝ) ≤
            (windowLengthEll (levelK K0 cur) (levelP K0 p0 cur) : ℝ) + 4 := by positivity
        have ht1_nn : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1Ell (levelK K0 cur) : ℝ) := by positivity
        have hmul_child := mul_le_mul_of_nonneg_left hchild hcoeff_nn
        nlinarith
      exact le_trans hstep
        (le_trans hmono (level_error_budget_le hK_cur hp_cur hleaf))
  intro ell hell
  have hsub := hmain (recursionDepth K0 p0 - ell) (Nat.sub_le _ _)
  have heq : recursionDepth K0 p0 - (recursionDepth K0 p0 - ell) = ell := by omega
  rwa [heq] at hsub

/-- **Inductive Accuracy Closure Across All Levels (`inductive_accuracy_closure`,
Lemma 6.5(2) (`lem:forward`), equation (36) (`eq:inductive-bound`))**:
For all $K_0 \ge 1$, $p_0 \ge 1$, and every recursion level $\ell \le \text{recursionDepth } K_0 \, p_0$,
the concrete multi-level recursive DFT error schedule `concreteLevelError K0 p0 ell` satisfies:
$$\text{concreteLevelError } K_0 \, p_0 \, \ell \le 2^{-p_\ell}.$$ -/
theorem inductive_accuracy_closure (K0 p0 : ℕ) (hK0 : 1 ≤ K0) (hp0 : 1 ≤ p0)
    (ell : ℕ) (hell : ell ≤ recursionDepth K0 p0) :
    concreteLevelError K0 p0 ell ≤ (2 : ℝ) ^ (-(levelP K0 p0 ell : ℤ)) :=
  inductive_accuracy_closure_of_validLevelErrorRecurrence hp0
    (validLevelErrorRecurrence_concreteLevelError K0 p0 hK0 hp0) ell hell

/-- Conditional vector-norm corollary (`vecInfNorm_sub_normDFT1D_le_of_approx`):
at every level $\ell \le \text{recursionDepth } K_0 \, p_0$, under `hp0 : 1 ≤ p0`,
`hrec : ValidLevelErrorRecurrence K0 p0 err`, and the conditional approximation hypothesis
`happrox : vecInfNorm (fun u => approx u - normDFT1D x u) ≤ err ell * vecInfNorm x`, we have:
$$\|\widehat{F_{R_\ell} x} - F_{R_\ell} x\|_\infty \le 2^{-p_\ell} \|x\|_\infty.$$ -/
theorem vecInfNorm_sub_normDFT1D_le_of_approx {K0 p0 : ℕ} (hp0 : 1 ≤ p0)
    {err : ℕ → ℝ} (hrec : ValidLevelErrorRecurrence K0 p0 err)
    (ell : ℕ) (hell : ell ≤ recursionDepth K0 p0)
    (x approx : Fin (levelR K0 ell) → ℂ)
    (happrox : vecInfNorm (fun u => approx u - normDFT1D x u) ≤ err ell * vecInfNorm x) :
    vecInfNorm (fun u => approx u - normDFT1D x u) ≤
      (2 : ℝ) ^ (-(levelP K0 p0 ell : ℤ)) * vecInfNorm x :=
  le_trans happrox
    (mul_le_mul_of_nonneg_right
      (inductive_accuracy_closure_of_validLevelErrorRecurrence hp0 hrec ell hell)
      (vecInfNorm_nonneg x))

/-! ## 6. Root Convolution Rounding & Carry-Propagation Integer Reconstruction (Theorem 1 (`thm:main`), Section 7.1 (`sec:alg-spec`) and Section 7.2 (`sec:cost-proof`), Part 1) -/

/-- Every base-$2^b$ chunk is strictly less than $2^b$. -/
theorem natChunk_lt (b A i : ℕ) : natChunk b A i < 2 ^ b := by
  unfold natChunk
  exact Nat.mod_lt _ (by positivity)

/-- Every base-$2^b$ chunk is at most $2^b - 1$. -/
theorem natChunk_le_sub_one (b A i : ℕ) : natChunk b A i ≤ 2 ^ b - 1 := by
  have h := natChunk_lt b A i
  omega

/-- For $i \ge N$ when $A < (2^b)^N$, the $i$-th chunk is zero. -/
theorem natChunk_eq_zero_of_lt {b A N i : ℕ} (hA : A < (2 ^ b) ^ N) (hi : N ≤ i) :
    natChunk b A i = 0 := by
  unfold natChunk
  have hpow : (2 ^ b) ^ N ≤ (2 ^ b) ^ i := Nat.pow_le_pow_right (by positivity) hi
  have hdiv : A / (2 ^ b) ^ i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hA hpow)
  simp [hdiv]

/-- Base-$2^b$ partial sum identity: $\sum_{i < M} a_i (2^b)^i = A \bmod (2^b)^M$. -/
theorem sum_natChunk_mul_pow_eq_mod (b M A : ℕ) :
    (∑ i ∈ Finset.range M, natChunk b A i * (2 ^ b) ^ i) = A % (2 ^ b) ^ M := by
  induction M with
  | zero =>
    simp [Nat.mod_one]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    unfold natChunk
    set P : ℕ := (2 ^ b) ^ M
    set B : ℕ := 2 ^ b
    have hP_pos : 0 < P := by positivity
    have hB_pos : 0 < B := by positivity
    have hpow_succ : (2 ^ b) ^ (M + 1) = P * B := by
      rw [pow_succ]
    rw [hpow_succ]
    have h1 := Nat.div_add_mod A P
    have h2 := Nat.div_add_mod (A / P) B
    have hmodP : A % P < P := Nat.mod_lt A hP_pos
    have hmodB : (A / P) % B < B := Nat.mod_lt (A / P) hB_pos
    have hlt : A % P + ((A / P) % B) * P < P * B := by nlinarith
    have hA_eq : A = (A % P + ((A / P) % B) * P) + (P * B) * ((A / P) / B) := by
      calc
        A = P * (A / P) + A % P := h1.symm
        _ = P * (B * ((A / P) / B) + (A / P) % B) + A % P := by rw [h2]
        _ = (A % P + ((A / P) % B) * P) + (P * B) * ((A / P) / B) := by ring
    conv_rhs => rw [hA_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Exact base-$2^b$ reconstruction when $A < (2^b)^M$: $\sum_{i < M} a_i (2^b)^i = A$. -/
theorem sum_natChunk_mul_pow_eq {b M A : ℕ} (hA : A < (2 ^ b) ^ M) :
    (∑ i ∈ Finset.range M, natChunk b A i * (2 ^ b) ^ i) = A := by
  rw [sum_natChunk_mul_pow_eq_mod, Nat.mod_eq_of_lt hA]

/-- Any $n$-bit integer $A < 2^n$ satisfies $A < (2^b)^N$ for $b = \text{chunkBits } n$ and $N = \text{numChunks } n$. -/
theorem lt_chunk_pow_of_lt_two_pow {n A : ℕ} (hA : A < 2 ^ n) :
    A < (2 ^ chunkBits n) ^ numChunks n := by
  rw [← pow_mul, mul_comm]
  exact lt_of_lt_of_le hA
    (Nat.pow_le_pow_right (by norm_num) (n_le_numChunks_mul_chunkBits n))

/-- Exact base-$2^b$ chunk reconstruction for any $n$-bit integer $A < 2^n$ (Section 7.1 (`sec:alg-spec`)). -/
theorem sum_natChunk_root_eq {n A : ℕ} (hA : A < 2 ^ n) :
    (∑ i ∈ Finset.range (numChunks n),
      natChunk (chunkBits n) A i * (2 ^ chunkBits n) ^ i) = A :=
  sum_natChunk_mul_pow_eq (lt_chunk_pow_of_lt_two_pow hA)

/-- True linear convolution coefficient $C_k = \sum_{i+j=k} a_i b_j$ of the base-$2^b$ chunks of $A$ and $B$ (Section 7.2 (`sec:cost-proof`)). -/
def linearConvCoeff (b N A B k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    if i + j = k then natChunk b A i * natChunk b B j else 0

/-- For $k \ge 2 N$, the linear convolution coefficient $C_k$ is zero. -/
theorem linearConvCoeff_eq_zero_of_ge {b N A B k : ℕ} (hk : 2 * N ≤ k) :
    linearConvCoeff b N A B k = 0 := by
  unfold linearConvCoeff
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hi hj
  have hne : i + j ≠ k := by omega
  simp [hne]

/-- Upper bound $C_k \le N (2^b - 1)^2$ on every linear convolution coefficient (Section 7.2 (`sec:cost-proof`)). -/
theorem linearConvCoeff_le (b N A B k : ℕ) :
    linearConvCoeff b N A B k ≤ N * (2 ^ b - 1) ^ 2 := by
  unfold linearConvCoeff
  have hinner : ∀ i ∈ Finset.range N,
      (∑ j ∈ Finset.range N, if i + j = k then natChunk b A i * natChunk b B j else 0) ≤
        (2 ^ b - 1) ^ 2 := by
    intro i _
    have hsub :
        (∑ j ∈ Finset.range N, if i + j = k then natChunk b A i * natChunk b B j else 0) ≤
        ∑ j ∈ Finset.range N, if j = k - i then (2 ^ b - 1) ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h1 h2
      · rw [sq]
        exact Nat.mul_le_mul (natChunk_le_sub_one b A i) (natChunk_le_sub_one b B j)
      · omega
      · exact Nat.zero_le _
      · exact Nat.zero_le _
    refine le_trans hsub ?_
    rw [Finset.sum_ite_eq']
    split_ifs <;> omega
  calc
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        if i + j = k then natChunk b A i * natChunk b B j else 0)
      ≤ ∑ _i ∈ Finset.range N, (2 ^ b - 1) ^ 2 := Finset.sum_le_sum hinner
    _ = N * (2 ^ b - 1) ^ 2 := by simp

/-- Root coefficient magnitude bound $C_k < R_0 2^{2b} = 2^{2b + K_0}$ (Section 7.2 (`sec:cost-proof`)). -/
theorem linearConvCoeff_lt_two_pow_root (n A B k : ℕ) :
    linearConvCoeff (chunkBits n) (numChunks n) A B k <
      2 ^ (2 * chunkBits n + rootK0 n) := by
  have hle := linearConvCoeff_le (chunkBits n) (numChunks n) A B k
  have h2N := two_mul_numChunks_le_rootR0 n
  have hR0_pos : 4 ≤ rootR0 n := rootR0_ge_four n
  have hN_lt : numChunks n < rootR0 n := by omega
  have hsub_le : (2 ^ chunkBits n - 1) ^ 2 ≤ (2 ^ chunkBits n) ^ 2 :=
    Nat.pow_le_pow_left (Nat.sub_le _ 1) 2
  have hprod : numChunks n * (2 ^ chunkBits n - 1) ^ 2 <
      rootR0 n * (2 ^ chunkBits n) ^ 2 := by
    have hpow_pos : 0 < (2 ^ chunkBits n) ^ 2 := by positivity
    calc
      numChunks n * (2 ^ chunkBits n - 1) ^ 2
        ≤ numChunks n * (2 ^ chunkBits n) ^ 2 :=
          Nat.mul_le_mul_left (numChunks n) hsub_le
      _ < rootR0 n * (2 ^ chunkBits n) ^ 2 :=
          (Nat.mul_lt_mul_right hpow_pos).mpr hN_lt
  have heq : rootR0 n * (2 ^ chunkBits n) ^ 2 = 2 ^ (2 * chunkBits n + rootK0 n) := by
    unfold rootR0
    rw [ ← pow_mul, ← pow_add, add_comm, mul_comm (chunkBits n) 2]
  omega

/-- Nearest-integer rounding $\lfloor y + 1/2 \rfloor$ recovers any integer $M \in \mathbb{Z}$
whenever $|y - M| < 1/2$ (Section 7.2 (`sec:cost-proof`), Part 1). -/
theorem floor_add_half_eq_of_abs_sub_lt_half {M : ℤ} {y : ℝ}
    (h : |y - (M : ℝ)| < (1 / 2 : ℝ)) :
    ⌊y + (1 / 2 : ℝ)⌋ = M := by
  rw [abs_lt] at h
  rw [Int.floor_eq_iff]
  constructor <;> linarith

/-- **Unconditional Root Precision Error Budget Identity (`root_conv_error_budget_lt_half`,
Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`), Part 1)**:
For every input bit-length $n$, under the schedule parameters $R_0 = \text{rootR0 } n = 2^{K_0}$ and
$p_0 = \text{rootP0 } n = 2b + 2K_0 + 6$, the root convolution error budget equals $1/8 < 1/2$
unconditionally:
$$8 R_0 \cdot 2^{-p_0} \cdot 2^{2b + K_0} = \frac{1}{8} < \frac{1}{2}.$$ -/
theorem root_conv_error_budget_lt_half (n : ℕ) :
    8 * (rootR0 n : ℝ) * (2 : ℝ) ^ (-(rootP0 n : ℤ)) * (2 : ℝ) ^ (2 * chunkBits n + rootK0 n) =
      (1 / 8 : ℝ) ∧ (1 / 8 : ℝ) < 1 / 2 := by
  refine ⟨?_, by norm_num⟩
  unfold rootR0 rootP0
  set M : ℕ := 2 * chunkBits n + 2 * rootK0 n
  have hexp : -((2 * chunkBits n + 2 * rootK0 n + 6 : ℕ) : ℤ) =
      -(M : ℤ) + (-6 : ℤ) := by
    simp only [M]
    push_cast
    ring
  have hzpow : (2 : ℝ) ^ (-((2 * chunkBits n + 2 * rootK0 n + 6 : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-(M : ℤ)) * (1 / 64 : ℝ) := by
    rw [hexp, zpow_add₀ (by norm_num)]
    norm_num
  have hpow_comb : ((2 ^ rootK0 n : ℕ) : ℝ) * (2 : ℝ) ^ (2 * chunkBits n + rootK0 n) =
      (2 : ℝ) ^ M := by
    push_cast
    rw [← pow_add]
    congr 1
    simp only [M]
    ring
  rw [hzpow]
  calc
    8 * ((2 ^ rootK0 n : ℕ) : ℝ) *
        ((2 : ℝ) ^ (-(M : ℤ)) * (1 / 64 : ℝ)) *
        (2 : ℝ) ^ (2 * chunkBits n + rootK0 n)
      = (((2 ^ rootK0 n : ℕ) : ℝ) * (2 : ℝ) ^ (2 * chunkBits n + rootK0 n)) *
          (2 : ℝ) ^ (-(M : ℤ)) * (1 / 8 : ℝ) := by ring
    _ = (2 : ℝ) ^ M * (2 : ℝ) ^ (-(M : ℤ)) * (1 / 8 : ℝ) := by rw [hpow_comb]
    _ = (1 / 8 : ℝ) := by rw [two_pow_mul_two_zpow_neg M, one_mul]

/-- **Conditional Root Convolution Rounding Recovery (`root_conv_rounding_exact_of_approx`,
Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`), Part 1)**:
Under the root precision $p_0 = \text{rootP0 } n = 2b + 2K_0 + 6$ and
$R_0 = \text{rootR0 } n = 2^{K_0}$, given the conditional approximation hypothesis
`herr : |cHat - (Ck : ℝ) / (rootR0 n : ℝ)| ≤ 8 * (2 : ℝ) ^ (-(rootP0 n : ℤ)) * (2 : ℝ) ^ (2 * chunkBits n + rootK0 n)`
on a normalized cyclic convolution approximation $\hat{c}_k$ to $c_k = C_k / R_0$,
the scaled output $R_0 \hat{c}_k$ satisfies:
$$|R_0 \hat{c}_k - C_k| \le \frac{1}{8} < \frac{1}{2},$$
and nearest-integer rounding $\lfloor R_0 \hat{c}_k + 1/2 \rfloor$ recovers $C_k$ bit-exactly. -/
theorem root_conv_rounding_exact_of_approx (n : ℕ) (Ck : ℕ) (cHat : ℝ)
    (herr : |cHat - (Ck : ℝ) / (rootR0 n : ℝ)| ≤
      8 * (2 : ℝ) ^ (-(rootP0 n : ℤ)) * (2 : ℝ) ^ (2 * chunkBits n + rootK0 n)) :
    |(rootR0 n : ℝ) * cHat - (Ck : ℝ)| ≤ (1 / 8 : ℝ) ∧
      |(rootR0 n : ℝ) * cHat - (Ck : ℝ)| < (1 / 2 : ℝ) ∧
      ⌊(rootR0 n : ℝ) * cHat + (1 / 2 : ℝ)⌋ = (Ck : ℤ) := by
  have hR0_pos : (0 : ℝ) < (rootR0 n : ℝ) := by
    unfold rootR0
    positivity
  have hdiff : (rootR0 n : ℝ) * cHat - (Ck : ℝ) =
      (rootR0 n : ℝ) * (cHat - (Ck : ℝ) / (rootR0 n : ℝ)) := by
    have hne : (rootR0 n : ℝ) ≠ 0 := ne_of_gt hR0_pos
    field_simp
  have hscale :
      (rootR0 n : ℝ) * (8 * (2 : ℝ) ^ (-(rootP0 n : ℤ)) *
        (2 : ℝ) ^ (2 * chunkBits n + rootK0 n)) = (1 / 8 : ℝ) := by
    calc
      (rootR0 n : ℝ) * (8 * (2 : ℝ) ^ (-(rootP0 n : ℤ)) *
          (2 : ℝ) ^ (2 * chunkBits n + rootK0 n))
        = 8 * (rootR0 n : ℝ) * (2 : ℝ) ^ (-(rootP0 n : ℤ)) *
            (2 : ℝ) ^ (2 * chunkBits n + rootK0 n) := by ring
      _ = (1 / 8 : ℝ) := (root_conv_error_budget_lt_half n).1
  have habs_le : |(rootR0 n : ℝ) * cHat - (Ck : ℝ)| ≤ (1 / 8 : ℝ) := by
    rw [hdiff, abs_mul, abs_of_pos hR0_pos, ← hscale]
    exact mul_le_mul_of_nonneg_left herr (le_of_lt hR0_pos)
  have habs_lt : |(rootR0 n : ℝ) * cHat - (Ck : ℝ)| < (1 / 2 : ℝ) := by linarith
  have hfloor : ⌊(rootR0 n : ℝ) * cHat + (1 / 2 : ℝ)⌋ = (Ck : ℤ) :=
    floor_add_half_eq_of_abs_sub_lt_half (M := (Ck : ℤ)) (by simpa using habs_lt)
  exact ⟨habs_le, habs_lt, hfloor⟩

/-- Polynomial product identity for base-$2^b$ linear convolution coefficients:
for any $M \ge 2 N - 1$ (in particular $M = 2 N$ or $M = R_0$),
$$\sum_{k < M} C_k (2^b)^k = \left(\sum_{i < N} a_i (2^b)^i\right) \left(\sum_{j < N} b_j (2^b)^j\right).$$ -/
theorem sum_linearConvCoeff_mul_pow_eq {b N A B M : ℕ} (hM : 2 * N ≤ M) :
    (∑ k ∈ Finset.range M, linearConvCoeff b N A B k * (2 ^ b) ^ k) =
      (∑ i ∈ Finset.range N, natChunk b A i * (2 ^ b) ^ i) *
        (∑ j ∈ Finset.range N, natChunk b B j * (2 ^ b) ^ j) := by
  unfold linearConvCoeff
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hi hj
  have hij_lt : i + j < M := by omega
  have hite : ∀ k ∈ Finset.range M,
      (if i + j = k then natChunk b A i * natChunk b B j else 0) * (2 ^ b) ^ k =
      if k = i + j then (natChunk b A i * (2 ^ b) ^ i) * (natChunk b B j * (2 ^ b) ^ j) else 0 := by
    intro k _
    split_ifs with h1 h2
    · subst h1
      rw [pow_add]
      ring
    · omega
    · omega
    · simp
  rw [Finset.sum_congr rfl hite]
  simp [Finset.sum_ite_eq', hij_lt]

/-- **Bit-Exact Carry-Propagation Reconstruction (`carry_propagation_eq_mul`,
Theorem 1 (`thm:main`), Section 7.1 (`sec:alg-spec`) and Section 7.2 (`sec:cost-proof`), Part 1)**:
For any two $n$-bit non-negative integers $A, B < 2^n$, the base-$2^b$ evaluation of the
linear convolution coefficients $C_k = \text{linearConvCoeff } b \, N \, A \, B \, k$
over $k \in \{0, \dots, 2N - 1\}$ (and over $k \in \{0, \dots, R_0 - 1\}$) equals $A \cdot B$
bit-exactly. -/
theorem carry_propagation_eq_mul {n A B : ℕ} (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    (∑ k ∈ Finset.range (2 * numChunks n),
      linearConvCoeff (chunkBits n) (numChunks n) A B k * (2 ^ chunkBits n) ^ k) = A * B := by
  rw [sum_linearConvCoeff_mul_pow_eq (le_refl (2 * numChunks n)),
    sum_natChunk_root_eq hA, sum_natChunk_root_eq hB]

/-- Root-$R_0$ carry-propagation reconstruction: summing over all $R_0 = \text{rootR0 } n$ slots
also equals $A \cdot B$ bit-exactly (Section 7.1 (`sec:alg-spec`) and Section 7.2 (`sec:cost-proof`), Part 1). -/
theorem carry_propagation_rootR0_eq_mul {n A B : ℕ} (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    (∑ k ∈ Finset.range (rootR0 n),
      linearConvCoeff (chunkBits n) (numChunks n) A B k * (2 ^ chunkBits n) ^ k) = A * B := by
  rw [sum_linearConvCoeff_mul_pow_eq (two_mul_numChunks_le_rootR0 n),
    sum_natChunk_root_eq hA, sum_natChunk_root_eq hB]

end IntMul

#print axioms IntMul.cyclicBidiagSolve_spec
#print axioms IntMul.cyclicBidiagSolve_of_spec
#print axioms IntMul.vecInfNorm_cyclicBidiagSolve_le
#print axioms IntMul.deconvolution_conditioning_le_236_t1_of_bounds
#print axioms IntMul.cyclicBidiagPrevSolve_spec
#print axioms IntMul.cyclicBidiagPrevSolve_of_spec
#print axioms IntMul.vecInfNorm_cyclicBidiagPrevSolve_le
#print axioms IntMul.deconvolution_prev_conditioning_le_236_t1_of_bounds
#print axioms IntMul.gHat_cyclicBidiagSolve_spec
#print axioms IntMul.gHat_cyclicBidiagPrevSolve_spec
#print axioms IntMul.gHat_deconvolution_conditioning_le_236_t1
#print axioms IntMul.gHat_deconvolution_prev_conditioning_le_236_t1
#print axioms IntMul.gHat_stopband_alias_lt_level
#print axioms IntMul.nyquist_alternating_sum_eq
#print axioms IntMul.nyquistOpenChainParticular_recurrence
#print axioms IntMul.nyquistColumnSolve_alternating_sum
#print axioms IntMul.nyquistColumnSolve_spec
#print axioms IntMul.vecInfNorm_nyquistColumnSolve_le
#print axioms IntMul.nyquist_conditioning_le_236_t1_of_bounds
#print axioms IntMul.vecInfNorm_cyclicBidiagSolveQuant_sub_le_of_bounds
#print axioms IntMul.vecInfNorm_cyclicBidiagPrevSolveQuant_sub_le_of_bounds
#print axioms IntMul.vecInfNorm_nyquistColumnSolveQuant_sub_le_of_bounds
#print axioms IntMul.qChildEll_step3_precision_le_half
#print axioms IntMul.level_error_budget_le
#print axioms IntMul.validLevelErrorRecurrence_concreteLevelError
#print axioms IntMul.inductive_accuracy_closure_of_validLevelErrorRecurrence
#print axioms IntMul.inductive_accuracy_closure
#print axioms IntMul.vecInfNorm_sub_normDFT1D_le_of_approx
#print axioms IntMul.root_conv_error_budget_lt_half
#print axioms IntMul.root_conv_rounding_exact_of_approx
#print axioms IntMul.carry_propagation_eq_mul
