import IntMul.ExecutableAlgorithm.ChunkingAndSyntheticFFT

namespace IntMul

/-! ## Exact-Arithmetic Idealized 2-Term-Passband Recursive `fastDFT` & `fastIDFT` -/

open scoped BigOperators

/-- Multiplication-free midpoint-row alternating sum for the Nyquist frequency `2 * u_2 = r` (`[MS]` §5.1):
`nyquistAltSum t1 r x = (i / r) * ∑_{j_2 < r} (-1)^{j_2} x(t_1 / 2 + t_1 * j_2)`. -/
noncomputable def nyquistAltSum (t1 r : ℕ) (x : ℕ → ℂ) : ℂ :=
  (Complex.I / (r : ℂ)) * ∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)

/-- **Nyquist Alternating-Sum Character Orthogonality Identity (`[MS]` §5.1, Theorem 5.1(3), eq. (25))**:
When `t_1 > 0` is even (`t1 % 2 = 0`), `r > 0`, and `2 * u_2 = r` (the Nyquist frequency `u_2 = r / 2`),
the alternating sum of the true 1D DFT modes `dft1DGrid t1 r x u2 u1` equals the multiplication-free
midpoint-row alternating sum `nyquistAltSum t1 r x`. -/
theorem dft1DGrid_alternating_sum_nyquist_eq
    (t1 r u2 : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (heven : t1 % 2 = 0) (hnyq : 2 * u2 = r)
    (x : ℕ → ℂ) :
    (∑ u1 ∈ Finset.range t1, (-1 : ℂ) ^ u1 * dft1DGrid t1 r x u2 u1) =
      nyquistAltSum t1 r x := by
  rw [dft1DGrid_alternating_sum_eq_midpoint t1 r ht1 hr heven x u2]
  unfold nyquistAltSum
  have hdiv : 2 * (t1 / 2) = t1 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)
  have hm_pos : 0 < t1 / 2 := by omega
  have hu2_pos : 0 < u2 := by omega
  have hphase_eq : ∀ j2 : ℕ,
      x (t1 / 2 + t1 * j2) *
        stdChar ((((t1 / 2 + t1 * j2 : ℕ) : ℝ) * (u2 : ℝ)) / ((t1 * r : ℕ) : ℝ)) =
      Complex.I * ((-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)) := by
    intro j2
    have hphase := theorem3_nyquist_midpoint_phase (t1 / 2) u2 hm_pos hu2_pos j2
    rw [hdiv, hnyq] at hphase
    rw [hphase]
    ring
  simp_rw [hphase_eq, ← Finset.mul_sum]
  ring

/-- Multi-level recursion specification for the exact-arithmetic, idealized 2-term-passband
Fractional-Shift Synthetic FFT (`fastDFT`). -/
inductive FastDFTSpec where
  | base (R : ℕ) : FastDFTSpec
  | step (t1 r c1 : ℕ) (c0 c1_pass : ℕ → ℂ) (v1Of : ℕ → ℕ → ℕ)
      (child : FastDFTSpec) : FastDFTSpec

/-- Transform length `R` associated with a `FastDFTSpec`. -/
def FastDFTSpec.size : FastDFTSpec → ℕ
  | .base R => R
  | .step t1 r _ _ _ _ _ => t1 * r

/-- **Exact-Arithmetic Idealized 2-Term-Passband Recursive `fastDFT`**:
Recursively computes the 1D DFT of length `spec.size` by:
1. Idealized 2-term-passband fractional-shift spreading (`spreadArray2Tap`),
2. Pre-twisting by `zetaRoot r k2`,
3. Multiplication-free Synthetic FFT `syntheticDFT t1 r` over `ℂ[y]/(y^r + 1)` (`negacyclicShiftIter`),
4. Post-twisting by `zetaRoot r (-k2)`,
5. `t_1` recursive child calls to `fastDFT child` of length `r`,
6. Odd-stride column permutation `v1Of u2 u1`, and
7. Direction-switched passband deconvolution at `(u % r, u / r)` across all three regimes (`[MS]` §5.1):
   - Forward bidiagonal sweep `solveBidiagonalFwd` for `2 * u2 < r`,
   - Nyquist solver `solveNyquist` with midpoint alternating sum `nyquistAltSum t1 r x` for `2 * u2 = r`,
   - Backward bidiagonal sweep `solveBidiagonalBwd` for `2 * u2 > r`. -/
noncomputable def fastDFT : FastDFTSpec → (ℕ → ℂ) → ℕ → ℂ
  | .base R, x, u => dft1D R x u
  | .step t1 r _c1 c0 c1_pass v1Of child, x, u =>
    let U := spreadArray2Tap t1 r c0 c1_pass x
    let P : ℕ → ℕ → ℂ := fun j1 k2 => zetaRoot r (k2 : ℝ) * U j1 k2
    let Q : ℕ → ℕ → ℂ := syntheticDFT t1 r P
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 => zetaRoot r (-(k2 : ℝ)) * Q v1 k2
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => fastDFT child (qPost v1) u2
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => qHat (v1Of u2 u1) u2
    let u2 := u % r
    let u1_tilde := u / r
    if 2 * u2 < r then
      solveBidiagonalFwd t1 (c0 u2) (c1_pass u2) (Y u2) u1_tilde
    else if 2 * u2 = r then
      solveNyquist t1 (c0 u2) (Y u2) (nyquistAltSum t1 r x) u1_tilde
    else
      solveBidiagonalBwd t1 (c0 u2) (c1_pass u2) (Y u2) u1_tilde

/-- Structural validity predicate for a multi-level `FastDFTSpec`:
at each recursive step `(t1, r, c1)`:
- `t1 > 0`, `r > 0`, `c1 * t1 = r`, `child.size = r`, `child.Valid`,
- `c0 u2 ≠ 0 ∧ c1_pass u2 ≠ 0` for all `u2 < r`,
- `c0 u2 + c1_pass u2 * zHomFwd (c0 u2) (c1_pass u2) (t1 - 1) ≠ 0` for all `2 * u2 < r`,
- `t1 % 2 = 0` and `c1_pass u2 = c0 u2` at the Nyquist column `2 * u2 = r`,
- `c1_pass u2 + c0 u2 * zHomBwd (c0 u2) (c1_pass u2) (t1 - 1) ≠ 0` for all `r < 2 * u2` (`u2 < r`),
- `v1Of u2 u1` satisfies the odd-stride congruence `(2 * u2 - 1) * v1Of u2 u1 ≡ u1 (mod t1)`. -/
inductive FastDFTSpec.Valid : FastDFTSpec → Prop where
  | base (R : ℕ) : FastDFTSpec.Valid (.base R)
  | step {t1 r c1 : ℕ} {c0 c1_pass : ℕ → ℂ} {v1Of : ℕ → ℕ → ℕ} {child : FastDFTSpec}
      (ht1 : 0 < t1) (hr : 0 < r) (hc1 : c1 * t1 = r)
      (hchild_size : child.size = r)
      (hchild : child.Valid)
      (hc0 : ∀ u2 < r, c0 u2 ≠ 0 ∧ c1_pass u2 ≠ 0)
      (hdenom_fwd : ∀ u2 < r, 2 * u2 < r →
        c0 u2 + c1_pass u2 * zHomFwd (c0 u2) (c1_pass u2) (t1 - 1) ≠ 0)
      (hnyq : ∀ u2 < r, 2 * u2 = r → t1 % 2 = 0 ∧ c1_pass u2 = c0 u2)
      (hdenom_bwd : ∀ u2 < r, r < 2 * u2 →
        c1_pass u2 + c0 u2 * zHomBwd (c0 u2) (c1_pass u2) (t1 - 1) ≠ 0)
      (hv1 : ∀ u2 < r, ∀ u1 < t1, ∃ q : ℤ,
        (2 * (u2 : ℤ) - 1) * (v1Of u2 u1 : ℤ) = (u1 : ℤ) + q * (t1 : ℤ)) :
      FastDFTSpec.Valid (.step t1 r c1 c0 c1_pass v1Of child)

/-- **Exact-Arithmetic Correctness of Idealized 2-Term-Passband Recursive `fastDFT`**:
For any valid multi-level recursion tree `spec : FastDFTSpec` (`hvalid : spec.Valid`),
any input vector `x : ℕ → ℂ`, and any frequency index `u < spec.size`,
`fastDFT spec x u` equals the exact 1D DFT `dft1D spec.size x u` across all three deconvolution
regimes (`2 * u2 < r` forward sweep, `2 * u2 = r` Nyquist solver, and `2 * u2 > r` backward sweep). -/
theorem fastDFT_eq_dft1D (spec : FastDFTSpec) (hvalid : spec.Valid)
    (x : ℕ → ℂ) (u : ℕ) (hu : u < spec.size) :
    fastDFT spec x u = dft1D spec.size x u := by
  induction hvalid generalizing x u with
  | base R =>
    rfl
  | @step t1 r c1 c0 c1_pass v1Of child ht1 hr hc1 hchild_size hchild hc0 hdenom_fwd hnyq hdenom_bwd hv1 ih =>
    dsimp only [fastDFT, FastDFTSpec.size] at hu ⊢
    set u2 := u % r
    set u1_tilde := u / r
    have hu2 : u2 < r := Nat.mod_lt u hr
    have hu1_tilde : u1_tilde < t1 := by
      rw [mul_comm] at hu
      exact Nat.div_lt_of_lt_mul hu
    let U := spreadArray2Tap t1 r c0 c1_pass x
    let P : ℕ → ℕ → ℂ := fun j1 k2 => zetaRoot r (k2 : ℝ) * U j1 k2
    let Q : ℕ → ℕ → ℂ := syntheticDFT t1 r P
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 => zetaRoot r (-(k2 : ℝ)) * Q v1 k2
    let Y : ℕ → ℂ := fun u1 => fastDFT child (qPost (v1Of u2 u1)) u2
    have hY_eq_dft2D : ∀ u1 < t1, Y u1 = dft2D t1 r U u1 u2 := by
      intro u1 hu1
      dsimp [Y]
      rw [ih (qPost (v1Of u2 u1)) u2 (by rw [hchild_size]; exact hu2), hchild_size]
      rcases hv1 u2 hu2 u1 hu1 with ⟨q, hq⟩
      exact theorem1_pipeline_computes_dft2D t1 r c1 ht1 hr hc1 U (v1Of u2 u1) u1 u2 q hq
    have h_bnd : Y 0 = c0 u2 * dft1DGrid t1 r x u2 0 + c1_pass u2 * dft1DGrid t1 r x u2 (t1 - 1) := by
      rw [hY_eq_dft2D 0 ht1, dft2D_spreadArray2Tap_eq t1 r ht1 hr c0 c1_pass x 0 u2 hu2]
      simp
    have h_int : ∀ u1 : ℕ, u1 + 1 < t1 →
        Y (u1 + 1) = c0 u2 * dft1DGrid t1 r x u2 (u1 + 1) + c1_pass u2 * dft1DGrid t1 r x u2 u1 := by
      intro u1 hu1_succ
      rw [hY_eq_dft2D (u1 + 1) hu1_succ,
          dft2D_spreadArray2Tap_eq t1 r ht1 hr c0 c1_pass x (u1 + 1) u2 hu2]
      simp
    split_ifs with h_fwd h_is_nyq
    · have h_solve_fwd := solveBidiagonalFwd_recover_exact t1 (c0 u2) (c1_pass u2) ht1
        (hc0 u2 hu2).1 (hdenom_fwd u2 hu2 h_fwd) (fun u1 => dft1DGrid t1 r x u2 u1) Y h_bnd h_int
        u1_tilde hu1_tilde
      rw [h_solve_fwd]
      exact dft1DGrid_eq_dft1D t1 r x u
    · rcases hnyq u2 hu2 h_is_nyq with ⟨heven, hc1_eq⟩
      have h_int_nyq : ∀ u1 : ℕ, u1 + 1 < t1 →
          Y (u1 + 1) = c0 u2 * dft1DGrid t1 r x u2 (u1 + 1) + c0 u2 * dft1DGrid t1 r x u2 u1 := by
        intro u1 hu1_succ
        rw [h_int u1 hu1_succ, hc1_eq]
      have h_alt := (dft1DGrid_alternating_sum_nyquist_eq t1 r u2 ht1 hr heven h_is_nyq x).symm
      have h_solve_nyq := solveNyquist_recover_exact t1 ht1 (c0 u2) (hc0 u2 hu2).1
        (fun u1 => dft1DGrid t1 r x u2 u1) Y h_int_nyq (nyquistAltSum t1 r x) h_alt
        u1_tilde hu1_tilde
      rw [h_solve_nyq]
      exact dft1DGrid_eq_dft1D t1 r x u
    · have h_bwd : r < 2 * u2 := by omega
      have h_solve_bwd := solveBidiagonalBwd_recover_exact t1 (c0 u2) (c1_pass u2) ht1
        (hc0 u2 hu2).2 (hdenom_bwd u2 hu2 h_bwd) (fun u1 => dft1DGrid t1 r x u2 u1) Y h_bnd h_int
        u1_tilde hu1_tilde
      rw [h_solve_bwd]
      exact dft1DGrid_eq_dft1D t1 r x u

/-- Complex conjugation of `stdChar x` negates the phase: `star (stdChar x) = stdChar (-x)`. -/
theorem star_stdChar (x : ℝ) : star (stdChar x) = stdChar (-x) := by
  unfold stdChar
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **1D DFT Conjugate-Inversion Identity**:
For `0 < R` and `j < R`, `R * conj(dft1D R (conj (dft1D R x)) j) = x j`. -/
theorem dft1D_conjugate_inversion (R : ℕ) (hR : 0 < R) (x : ℕ → ℂ) (j : ℕ) (hj : j < R) :
    (R : ℂ) * star (dft1D R (fun u => star (dft1D R x u)) j) = x j := by
  have hR_ne : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have houter : star (dft1D R (fun u => star (dft1D R x u)) j) =
      (1 / (R : ℂ)) * ∑ u ∈ Finset.range R,
        dft1D R x u * stdChar (-(((u * j : ℕ) : ℝ) / (R : ℝ))) := by
    change star ((1 / (R : ℂ)) * ∑ u ∈ Finset.range R,
      star (dft1D R x u) * stdChar (((u * j : ℕ) : ℝ) / (R : ℝ))) = _
    simp only [star_mul, star_div₀, star_one, star_natCast, star_sum, star_star, star_stdChar]
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun u _ => mul_comm _ _
  rw [houter]
  unfold dft1D
  have hswap :
      (∑ u ∈ Finset.range R,
        ((1 / (R : ℂ)) * ∑ k ∈ Finset.range R, x k * stdChar (((k * u : ℕ) : ℝ) / (R : ℝ))) *
          stdChar (-(((u * j : ℕ) : ℝ) / (R : ℝ)))) =
      (1 / (R : ℂ)) * ∑ k ∈ Finset.range R, x k *
        ∑ u ∈ Finset.range R,
          stdChar (-(((u : ℝ) * (j : ℝ)) / (R : ℝ))) *
            stdChar (((u * k : ℕ) : ℝ) / (R : ℝ)) := by
    rw [Finset.mul_sum]
    trans (∑ u ∈ Finset.range R, ∑ k ∈ Finset.range R,
      (1 / (R : ℂ)) * (x k *
        (stdChar (-(((u : ℝ) * (j : ℝ)) / (R : ℝ))) *
          stdChar (((u * k : ℕ) : ℝ) / (R : ℝ)))))
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hcast1 : ((u * j : ℕ) : ℝ) = (u : ℝ) * (j : ℝ) := by push_cast; ring
      have hcast2 : (k * u : ℕ) = u * k := Nat.mul_comm k u
      rw [hcast1, hcast2]
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hswap]
  have horth :
      (∑ k ∈ Finset.range R, x k *
        ∑ u ∈ Finset.range R,
          stdChar (-(((u : ℝ) * (j : ℝ)) / (R : ℝ))) *
            stdChar (((u * k : ℕ) : ℝ) / (R : ℝ))) =
      ∑ k ∈ Finset.range R, if j = k then x k * (R : ℂ) else 0 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [stdChar_orthogonality_range R hR j k hj (Finset.mem_range.mp hk)]
    split_ifs <;> ring
  rw [horth, Finset.sum_ite_eq (Finset.range R) j, if_pos (Finset.mem_range.mpr hj)]
  field_simp [hR_ne]

/-- Exact-arithmetic recursive Inverse Fast DFT (`fastIDFT`), computed via `fastDFT`
using the paper's conjugate-DFT identity (`[MS]` §3.5):
`fastIDFT spec X j = spec.size * conj(fastDFT spec (conj X) j)`. -/
noncomputable def fastIDFT (spec : FastDFTSpec) (X : ℕ → ℂ) (j : ℕ) : ℂ :=
  (spec.size : ℂ) * star (fastDFT spec (fun u => star (X u)) j)

/-- **Exact Inversion of Recursive `fastDFT` by `fastIDFT`**:
For any valid recursion tree `spec : FastDFTSpec` (`hvalid : spec.Valid`) with `0 < spec.size`,
any input vector `x : ℕ → ℂ`, and any index `j < spec.size`,
`fastIDFT spec (fastDFT spec x) j = x j`. -/
theorem fastIDFT_inverts_fastDFT (spec : FastDFTSpec) (hvalid : spec.Valid)
    (hR : 0 < spec.size) (x : ℕ → ℂ) (j : ℕ) (hj : j < spec.size) :
    fastIDFT spec (fastDFT spec x) j = x j := by
  unfold fastIDFT
  rw [fastDFT_eq_dft1D spec hvalid _ j hj]
  have hcongr : dft1D spec.size (fun u => star (fastDFT spec x u)) j =
      dft1D spec.size (fun u => star (dft1D spec.size x u)) j := by
    refine congrArg (fun (S : ℂ) => (1 / (spec.size : ℂ)) * S) ?_
    refine Finset.sum_congr rfl fun u hu => ?_
    dsimp only
    rw [fastDFT_eq_dft1D spec hvalid x u (Finset.mem_range.mp hu)]
  rw [hcongr]
  exact dft1D_conjugate_inversion spec.size hR x j hj

/-- Concrete `FastDFTSpec.step` instantiated with the paper's Box-Gaussian passband coefficients
`c_0(u_2) = c0Coeff (realErfScaled α) (u_2 / 2^{k_2})` and
`c_1(u_2) = c1Coeff (realErfScaled α) (u_2 / 2^{k_2})` and the power-of-two odd-stride inverse
`oddStrideInvPow2 k1` (`t_1 = 2^{k_1}`, `r = 2^{k_2}`). -/
noncomputable def boxGaussianStepSpec (k1 k2 : ℕ) (α : ℝ) (child : FastDFTSpec) : FastDFTSpec :=
  .step (2 ^ k1) (2 ^ k2) (2 ^ (k2 - k1))
    (fun u2 => (c0Coeff (realErfScaled α) ((u2 : ℝ) / ((2 ^ k2 : ℕ) : ℝ)) : ℂ))
    (fun u2 => (c1Coeff (realErfScaled α) ((u2 : ℝ) / ((2 ^ k2 : ℕ) : ℝ)) : ℂ))
    (oddStrideInvPow2 k1)
    child

/-- **Validity of `boxGaussianStepSpec` for the Paper's Box-Gaussian Passband Coefficients**:
For any `1 ≤ k1 ≤ k2`, `α > 0`, and valid `child` with `child.size = 2^{k_2}`,
`boxGaussianStepSpec k1 k2 α child` satisfies `FastDFTSpec.Valid` at all columns `u_2 < 2^{k_2}`
across all three regimes (`2 u_2 < 2^{k_2}` via `c0_c1_realErfScaled_denom_ne_zero`,
`2 u_2 = 2^{k_2}` via `theorem3_nyquist_passband_eq`, and `2 u_2 > 2^{k_2}` via
`c0_c1_realErfScaled_bwd_denom_ne_zero`). -/
theorem boxGaussianStepSpec_valid (k1 k2 : ℕ) (hk1 : 1 ≤ k1) (hk12 : k1 ≤ k2)
    (α : ℝ) (hα : 0 < α) (child : FastDFTSpec)
    (hchild_size : child.size = 2 ^ k2) (hchild : child.Valid) :
    (boxGaussianStepSpec k1 k2 α child).Valid := by
  have ht1 : 0 < 2 ^ k1 := pow_pos zero_lt_two k1
  have hr : 0 < 2 ^ k2 := pow_pos zero_lt_two k2
  have hr_real : (0 : ℝ) < ((2 ^ k2 : ℕ) : ℝ) := by exact_mod_cast hr
  have hc1 : 2 ^ (k2 - k1) * 2 ^ k1 = 2 ^ k2 := by
    rw [← pow_add, Nat.sub_add_cancel hk12]
  refine FastDFTSpec.Valid.step ht1 hr hc1 hchild_size hchild ?_ ?_ ?_ ?_ ?_
  · intro u2 _
    exact ⟨Complex.ofReal_ne_zero.mpr
        (c0Coeff_realErfScaled_pos α ((u2 : ℝ) / ((2 ^ k2 : ℕ) : ℝ)) hα).ne',
      Complex.ofReal_ne_zero.mpr
        (c1Coeff_realErfScaled_pos α ((u2 : ℝ) / ((2 ^ k2 : ℕ) : ℝ)) hα).ne'⟩
  · intro u2 hu2 h_fwd
    set y : ℝ := (u2 : ℝ) / ((2 ^ k2 : ℕ) : ℝ)
    have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) hr_real.le
    have hy1 : y ≤ 1 := by
      rw [div_le_one hr_real]
      exact_mod_cast hu2.le
    have hy_ne : y ≠ 1 / 2 := by
      intro hy_eq
      have hmul : (2 : ℝ) * (u2 : ℝ) = ((2 ^ k2 : ℕ) : ℝ) := by
        dsimp [y] at hy_eq
        have := (div_eq_iff hr_real.ne').mp hy_eq
        linarith
      have hmul_nat : 2 * u2 = 2 ^ k2 := by exact_mod_cast hmul
      omega
    exact c0_c1_realErfScaled_denom_ne_zero α y (2 ^ k1) hα ht1 hy0 hy1 hy_ne
  · intro u2 _ h_is_nyq
    refine ⟨?_, ?_⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k1 ≠ 0)
      rw [pow_succ']
      exact Nat.mul_mod_right 2 (2 ^ m)
    · have hy_eq : (u2 : ℝ) / ((2 ^ k2 : ℕ) : ℝ) = 1 / 2 := by
        rw [div_eq_iff hr_real.ne']
        have h_real : (2 : ℝ) * (u2 : ℝ) = ((2 ^ k2 : ℕ) : ℝ) := by exact_mod_cast h_is_nyq
        linarith
      rw [hy_eq]
      have hnyq_eq := theorem3_nyquist_passband_eq (realErfScaled α) (by simp [realErfScaled, realErf])
      rw [hnyq_eq.1, hnyq_eq.2]
  · intro u2 hu2 h_bwd
    set y : ℝ := (u2 : ℝ) / ((2 ^ k2 : ℕ) : ℝ)
    have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) hr_real.le
    have hy1 : y ≤ 1 := by
      rw [div_le_one hr_real]
      exact_mod_cast hu2.le
    have hy_ne : y ≠ 1 / 2 := by
      intro hy_eq
      have hmul : (2 : ℝ) * (u2 : ℝ) = ((2 ^ k2 : ℕ) : ℝ) := by
        dsimp [y] at hy_eq
        have := (div_eq_iff hr_real.ne').mp hy_eq
        linarith
      have hmul_nat : 2 * u2 = 2 ^ k2 := by exact_mod_cast hmul
      omega
    exact c0_c1_realErfScaled_bwd_denom_ne_zero α y (2 ^ k1) hα ht1 hy0 hy1 hy_ne
  · intro u2 _ u1 _
    exact oddStrideInvPow2_congr k1 u2 u1

/-- **Corollary: `fastDFT` with the Paper's Box-Gaussian Passband Schedule Equals `dft1D`**:
For any `1 ≤ k1 ≤ k2`, `α > 0`, and valid `child` of size `2^{k_2}`,
`fastDFT (boxGaussianStepSpec k1 k2 α child) x u = dft1D (2^{k_1} * 2^{k_2}) x u`
for all `u < 2^{k_1} * 2^{k_2}`. -/
theorem fastDFT_boxGaussianStepSpec_eq_dft1D
    (k1 k2 : ℕ) (hk1 : 1 ≤ k1) (hk12 : k1 ≤ k2)
    (α : ℝ) (hα : 0 < α) (child : FastDFTSpec)
    (hchild_size : child.size = 2 ^ k2) (hchild : child.Valid)
    (x : ℕ → ℂ) (u : ℕ) (hu : u < 2 ^ k1 * 2 ^ k2) :
    fastDFT (boxGaussianStepSpec k1 k2 α child) x u = dft1D (2 ^ k1 * 2 ^ k2) x u :=
  fastDFT_eq_dft1D (boxGaussianStepSpec k1 k2 α child)
    (boxGaussianStepSpec_valid k1 k2 hk1 hk12 α hα child hchild_size hchild) x u hu

/-! ## Discrete Cyclic Convolution Theorem for `dft1D` and `fastDFT` / `fastIDFT` -/

/-- Discrete cyclic convolution of length `R`:
`(a ⊛ b)_k = ∑_{j=0}^{R-1} a_j * b_{(k + R - j mod R) mod R}`. -/
noncomputable def cyclicConv (R : ℕ) (a b : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range R, a j * b ((k + R - j % R) % R)

/-- Cyclic index-shift invariance on `Finset.range R`:
for `j < R`, summing `g k` over `k ∈ Finset.range R` equals summing `g ((m + j) % R)`
over `m ∈ Finset.range R`. -/
theorem sum_range_add_mod (R j : ℕ) (hj : j < R) (g : ℕ → ℂ) :
    (∑ k ∈ Finset.range R, g k) = ∑ m ∈ Finset.range R, g ((m + j) % R) := by
  have hR1 : j + (R - j) = R := Nat.add_sub_of_le hj.le
  have hR2 : (R - j) + j = R := Nat.sub_add_cancel hj.le
  have hlhs := Finset.sum_range_add g j (R - j)
  rw [hR1] at hlhs
  have hrhs := Finset.sum_range_add (fun m => g ((m + j) % R)) (R - j) j
  rw [hR2] at hrhs
  have h1 : (∑ m ∈ Finset.range (R - j), g ((m + j) % R)) =
      ∑ m ∈ Finset.range (R - j), g (j + m) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_lt : m < R - j := Finset.mem_range.mp hm
    rw [Nat.mod_eq_of_lt (by omega), add_comm]
  have h2 : (∑ m ∈ Finset.range j, g (((R - j + m) + j) % R)) =
      ∑ k ∈ Finset.range j, g k := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_lt : m < j := Finset.mem_range.mp hm
    have heq : (R - j + m) + j = m + R := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hlhs, hrhs, h1, h2, add_comm]

/-- Modular subtraction cancels modular addition on `Finset.range R`:
for `m < R` and `j < R`, `((m + j) % R + R - j % R) % R = m`. -/
theorem add_mod_sub_mod_eq (R m j : ℕ) (hm : m < R) (hj : j < R) :
    (((m + j) % R + R - j % R) % R) = m := by
  rw [Nat.mod_eq_of_lt hj]
  by_cases hlt : m + j < R
  · rw [Nat.mod_eq_of_lt hlt]
    have heq : m + j + R - j = m + R := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
  · have hsub_lt : m + j - R < R := by omega
    have hmod : (m + j) % R = m + j - R := by
      calc (m + j) % R
          = ((m + j - R) + R) % R := congrArg (· % R) (by omega)
        _ = (m + j - R) % R := Nat.add_mod_right (m + j - R) R
        _ = m + j - R := Nat.mod_eq_of_lt hsub_lt
    rw [hmod]
    have heq2 : m + j - R + R - j = m := by omega
    rw [heq2, Nat.mod_eq_of_lt hm]

/-- Character multiplicativity under modular index addition `(m + j) % R`:
for `R > 0`, `stdChar (((((m + j) % R) * u) : ℝ) / R) = stdChar (j u / R) * stdChar (m u / R)`. -/
theorem stdChar_add_mod_mul_div (R : ℕ) (hR : 0 < R) (m j u : ℕ) :
    stdChar (((((m + j) % R) * u : ℕ) : ℝ) / (R : ℝ)) =
      stdChar (((j * u : ℕ) : ℝ) / (R : ℝ)) *
        stdChar (((m * u : ℕ) : ℝ) / (R : ℝ)) := by
  have hR_ne : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  set q : ℕ := (m + j) / R
  have hdiv : (m + j) % R + R * q = m + j := Nat.mod_add_div (m + j) R
  have hdiv_real : (((m + j) % R : ℕ) : ℝ) =
      (m : ℝ) + (j : ℝ) - (R : ℝ) * (q : ℝ) := by
    have hcast : (((m + j) % R + R * q : ℕ) : ℝ) = ((m + j : ℕ) : ℝ) :=
      congrArg Nat.cast hdiv
    push_cast at hcast
    linarith
  have harg : ((((m + j) % R) * u : ℕ) : ℝ) / (R : ℝ) =
      (((j * u : ℕ) : ℝ) / (R : ℝ) + ((m * u : ℕ) : ℝ) / (R : ℝ)) +
        ((-(q : ℤ) * (u : ℤ) : ℤ) : ℝ) := by
    push_cast
    rw [hdiv_real]
    field_simp [hR_ne]
    ring
  rw [harg, stdChar_add_int, stdChar_add]

/-- **1D DFT Cyclic Convolution Theorem (`[MS]` §3.5)**:
For `0 < R`, the normalized 1D DFT of the cyclic convolution `cyclicConv R a b` satisfies
`dft1D R (cyclicConv R a b) u = R * dft1D R a u * dft1D R b u` for all `u : ℕ`. -/
theorem dft1D_cyclicConv (R : ℕ) (hR : 0 < R) (a b : ℕ → ℂ) (u : ℕ) :
    dft1D R (cyclicConv R a b) u = (R : ℂ) * dft1D R a u * dft1D R b u := by
  have hR_ne : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  unfold dft1D cyclicConv
  have hswap :
      (∑ k ∈ Finset.range R,
        (∑ j ∈ Finset.range R, a j * b ((k + R - j % R) % R)) *
          stdChar (((k * u : ℕ) : ℝ) / (R : ℝ))) =
      ∑ j ∈ Finset.range R,
        ∑ k ∈ Finset.range R,
          a j * b ((k + R - j % R) % R) * stdChar (((k * u : ℕ) : ℝ) / (R : ℝ)) := by
    trans (∑ k ∈ Finset.range R, ∑ j ∈ Finset.range R,
      a j * b ((k + R - j % R) % R) * stdChar (((k * u : ℕ) : ℝ) / (R : ℝ)))
    · refine Finset.sum_congr rfl fun k _ => Finset.sum_mul _ _ _
    · exact Finset.sum_comm
  rw [hswap]
  have hinner :
      (∑ j ∈ Finset.range R,
        ∑ k ∈ Finset.range R,
          a j * b ((k + R - j % R) % R) * stdChar (((k * u : ℕ) : ℝ) / (R : ℝ))) =
      (∑ j ∈ Finset.range R, a j * stdChar (((j * u : ℕ) : ℝ) / (R : ℝ))) *
        (∑ m ∈ Finset.range R, b m * stdChar (((m * u : ℕ) : ℝ) / (R : ℝ))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < R := Finset.mem_range.mp hj
    rw [sum_range_add_mod R j hj_lt
      (fun k => a j * b ((k + R - j % R) % R) * stdChar (((k * u : ℕ) : ℝ) / (R : ℝ)))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_lt : m < R := Finset.mem_range.mp hm
    rw [add_mod_sub_mod_eq R m j hm_lt hj_lt, stdChar_add_mod_mul_div R hR m j u]
    ring
  rw [hinner]
  field_simp [hR_ne]

/-- **End-to-End Recursive `fastDFT` / `fastIDFT` Cyclic Convolution Theorem**:
For any valid multi-level recursion tree `spec : FastDFTSpec` (`hvalid : spec.Valid`) with
`0 < spec.size`, any input sequences `a, b : ℕ → ℂ`, and any index `k < spec.size`,
applying `fastIDFT spec` to the scaled pointwise product `u ↦ spec.size * fastDFT spec a u * fastDFT spec b u`
recovers the exact cyclic convolution `cyclicConv spec.size a b k`. -/
theorem fastIDFT_pointwiseMul_fastDFT_eq_cyclicConv
    (spec : FastDFTSpec) (hvalid : spec.Valid) (hR : 0 < spec.size)
    (a b : ℕ → ℂ) (k : ℕ) (hk : k < spec.size) :
    fastIDFT spec (fun u => (spec.size : ℂ) * fastDFT spec a u * fastDFT spec b u) k =
      cyclicConv spec.size a b k := by
  have hcongr :
      fastIDFT spec (fun u => (spec.size : ℂ) * fastDFT spec a u * fastDFT spec b u) k =
        fastIDFT spec (fastDFT spec (cyclicConv spec.size a b)) k := by
    unfold fastIDFT
    rw [fastDFT_eq_dft1D spec hvalid _ k hk, fastDFT_eq_dft1D spec hvalid _ k hk]
    congr 2
    unfold dft1D
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu_lt : u < spec.size := Finset.mem_range.mp hu
    dsimp only
    rw [fastDFT_eq_dft1D spec hvalid a u hu_lt,
        fastDFT_eq_dft1D spec hvalid b u hu_lt,
        fastDFT_eq_dft1D spec hvalid (cyclicConv spec.size a b) u hu_lt,
        dft1D_cyclicConv spec.size hR a b u]
  rw [hcongr]
  exact fastIDFT_inverts_fastDFT spec hvalid hR (cyclicConv spec.size a b) k hk

/-! ## End-to-End Exact-Arithmetic Integer Multiplication via Recursive `fastDFT` / `fastIDFT` -/

/-- Coefficient extraction for `polyAddList`. -/
theorem polyAddList_getD (as bs : List ℕ) (k : ℕ) :
    (polyAddList as bs).getD k 0 = as.getD k 0 + bs.getD k 0 := by
  induction as generalizing bs k with
  | nil => simp [polyAddList]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAddList]
    | cons b bs =>
      cases k with
      | zero => simp [polyAddList]
      | succ k => exact ih bs k

/-- Coefficient extraction for `polyScaleList`. -/
theorem polyScaleList_getD (c : ℕ) (ys : List ℕ) (k : ℕ) :
    (polyScaleList c ys).getD k 0 = c * ys.getD k 0 := by
  induction ys generalizing k with
  | nil => simp [polyScaleList]
  | cons y ys ih =>
    cases k with
    | zero => simp [polyScaleList]
    | succ k => exact ih k

/-- **Cauchy Convolution Coefficient Identity for `polyMulList`**:
The `k`-th coefficient of `polyMulList xs ys` equals the discrete Cauchy product
`∑_{j=0}^k xs[j] * ys[k - j]`. -/
theorem polyMulList_getD (xs ys : List ℕ) (k : ℕ) :
    (polyMulList xs ys).getD k 0 =
      ∑ j ∈ Finset.range (k + 1), xs.getD j 0 * ys.getD (k - j) 0 := by
  induction xs generalizing k with
  | nil => simp [polyMulList]
  | cons x xs ih =>
    rw [polyMulList, polyAddList_getD, polyScaleList_getD, Finset.sum_range_succ']
    cases k with
    | zero => simp
    | succ k =>
      simp only [getD_cons_zero, getD_cons_succ, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, ih k]
      ring

/-- Length of `polyAddList as bs` is `max as.length bs.length`. -/
theorem length_polyAddList (as bs : List ℕ) :
    (polyAddList as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [polyAddList]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAddList]
    | cons b bs =>
      simp only [polyAddList, List.length_cons, ih]
      omega

/-- Length of `polyScaleList c ys` is `ys.length`. -/
theorem length_polyScaleList (c : ℕ) (ys : List ℕ) :
    (polyScaleList c ys).length = ys.length := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [polyScaleList, ih]

/-- Length of `polyMulList xs ys` is bounded by `xs.length + ys.length`. -/
theorem length_polyMulList_le (xs ys : List ℕ) :
    (polyMulList xs ys).length ≤ xs.length + ys.length := by
  induction xs with
  | nil => simp [polyMulList]
  | cons x xs ih =>
    simp only [polyMulList, length_polyAddList, length_polyScaleList, List.length_cons]
    omega

/-- **Zero-Padded Cyclic Convolution Equals Acyclic Polynomial Multiplication (`polyMulList`)**:
When `xs.length + ys.length ≤ R`, the length-`R` cyclic convolution `cyclicConv R` of the
zero-padded sequences `j ↦ xs[j]` and `j ↦ ys[j]` has no wrap-around aliasing and equals
`((polyMulList xs ys).getD k 0 : ℂ)` for every `k < R`. -/
theorem cyclicConv_getD_eq_polyMulList_getD
    (R : ℕ) (xs ys : List ℕ) (hR : xs.length + ys.length ≤ R) (k : ℕ) (hk : k < R) :
    cyclicConv R (fun j => (xs.getD j 0 : ℂ)) (fun j => (ys.getD j 0 : ℂ)) k =
      ((polyMulList xs ys).getD k 0 : ℂ) := by
  unfold cyclicConv
  rw [polyMulList_getD, Nat.cast_sum]
  have hsplit : (k + 1) + (R - (k + 1)) = R := Nat.add_sub_of_le hk
  have hsum := Finset.sum_range_add
    (fun j => (xs.getD j 0 : ℂ) * (ys.getD ((k + R - j % R) % R) 0 : ℂ))
    (k + 1) (R - (k + 1))
  rw [hsplit] at hsum
  rw [hsum]
  have hhead :
      (∑ j ∈ Finset.range (k + 1),
        (xs.getD j 0 : ℂ) * (ys.getD ((k + R - j % R) % R) 0 : ℂ)) =
      ∑ j ∈ Finset.range (k + 1),
        ((xs.getD j 0 * ys.getD (k - j) 0 : ℕ) : ℂ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < k + 1 := Finset.mem_range.mp hj
    have hj_R : j % R = j := Nat.mod_eq_of_lt (by omega)
    have hsub : k + R - j = (k - j) + R := by omega
    have hmod : ((k - j) + R) % R = k - j := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hj_R, hsub, hmod, Nat.cast_mul]
  have htail :
      (∑ m ∈ Finset.range (R - (k + 1)),
        (xs.getD (k + 1 + m) 0 : ℂ) *
          (ys.getD ((k + R - (k + 1 + m) % R) % R) 0 : ℂ)) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm_lt : m < R - (k + 1) := Finset.mem_range.mp hm
    set j := k + 1 + m
    by_cases hj_xs : xs.length ≤ j
    · rw [getD_eq_default_of_le xs j 0 hj_xs, Nat.cast_zero, zero_mul]
    · have hj_R : j % R = j := Nat.mod_eq_of_lt (by omega)
      have hmod : (k + R - j) % R = k + R - j := Nat.mod_eq_of_lt (by omega)
      have hys : ys.length ≤ k + R - j := by omega
      rw [hj_R, hmod, getD_eq_default_of_le ys (k + R - j) 0 hys, Nat.cast_zero, mul_zero]
  rw [hhead, htail, add_zero]

/-- Evaluating the first `M ≥ cs.length` coefficients `(List.range M).map (fun k => cs.getD k 0)`
in radix `B` equals `evalRadix B cs`. -/
theorem evalRadix_range_getD (B : ℕ) (cs : List ℕ) (M : ℕ) (hM : cs.length ≤ M) :
    evalRadix B ((List.range M).map (fun k => cs.getD k 0)) = evalRadix B cs := by
  induction M generalizing cs with
  | zero =>
    cases cs with
    | nil => rfl
    | cons c cs => simp at hM
  | succ M ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    cases cs with
    | nil =>
      have h0 := ih [] (Nat.zero_le M)
      simp only [List.getD_nil, evalRadix] at h0 ⊢
      have hfun : ((fun _ : ℕ => (0 : ℕ)) ∘ Nat.succ) = fun _ => 0 := rfl
      rw [hfun, h0, mul_zero, add_zero]
    | cons c cs =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hM
      have hfun : ((fun k => (c :: cs).getD k 0) ∘ Nat.succ) = fun k => cs.getD k 0 := rfl
      rw [getD_cons_zero, hfun, evalRadix, ih cs hM, evalRadix]

/-- Nearest-integer rounding `⌊Re(n) + 1/2⌋.toNat` on an exact natural-number complex cast `(n : ℂ)`
recovers `n` identically. -/
theorem floor_natCast_add_half_toNat (n : ℕ) :
    ⌊((n : ℂ).re) + (1 / 2 : ℝ)⌋.toNat = n := by
  have hre : ((n : ℂ).re) = (n : ℝ) := Complex.natCast_re n
  rw [hre]
  have hfl : ⌊(n : ℝ) + (1 / 2 : ℝ)⌋ = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  rw [hfl]
  exact Int.toNat_natCast n

/-- **End-to-End Exact-Arithmetic Integer Multiplication via Recursive `fastDFT` / `fastIDFT`**:
Splits `A` and `B` into radix-`2^b` chunk lists of lengths `k1` and `k2`, zero-pads to
`spec.size`, transforms via `fastDFT spec`, multiplies pointwise by `spec.size`, inverts via
`fastIDFT spec`, rounds each real part to the nearest integer `⌊Re(·) + 1/2⌋.toNat`, and
propagates carries via `reconstructChunks b`. -/
noncomputable def fastDFTMultiply (spec : FastDFTSpec) (b k1 k2 : ℕ) (A B : ℕ) : ℕ :=
  let xs := splitChunks b k1 A
  let ys := splitChunks b k2 B
  let a : ℕ → ℂ := fun j => (xs.getD j 0 : ℂ)
  let g : ℕ → ℂ := fun j => (ys.getD j 0 : ℂ)
  let convC : ℕ → ℂ :=
    fastIDFT spec (fun u => (spec.size : ℂ) * fastDFT spec a u * fastDFT spec g u)
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun k => ⌊(convC k).re + (1 / 2 : ℝ)⌋.toNat)
  reconstructChunks b convNat

/-- **Master Correctness Theorem for `fastDFTMultiply`**:
For any valid multi-level recursion tree `spec : FastDFTSpec` (`hvalid : spec.Valid`),
any chunk width `b`, any chunk counts `k1, k2` with `k1 + k2 ≤ spec.size`, and any natural
numbers `A < (2^b)^{k_1}` and `B < (2^b)^{k_2}`, the recursive Fractional-Shift Synthetic FFT
integer multiplication pipeline `fastDFTMultiply spec b k1 k2 A B` computes the exact integer
product `A * B`. -/
theorem fastDFTMultiply_eq_mul
    (spec : FastDFTSpec) (hvalid : spec.Valid)
    (b k1 k2 : ℕ) (hk : k1 + k2 ≤ spec.size)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    fastDFTMultiply spec b k1 k2 A B = A * B := by
  unfold fastDFTMultiply
  set xs := splitChunks b k1 A
  set ys := splitChunks b k2 B
  have hlen : xs.length + ys.length ≤ spec.size := by
    rw [length_splitChunks, length_splitChunks]
    exact hk
  have hmap :
      (List.range (k1 + k2)).map
        (fun k => ⌊(fastIDFT spec
          (fun u => (spec.size : ℂ) * fastDFT spec (fun j => (xs.getD j 0 : ℂ)) u *
            fastDFT spec (fun j => (ys.getD j 0 : ℂ)) u) k).re + (1 / 2 : ℝ)⌋.toNat) =
      (List.range (k1 + k2)).map (fun k => (polyMulList xs ys).getD k 0) := by
    refine List.map_congr_left fun k hk_mem => ?_
    have hk_lt : k < k1 + k2 := List.mem_range.mp hk_mem
    have hk_R : k < spec.size := by omega
    have hR_pos : 0 < spec.size := by omega
    rw [fastIDFT_pointwiseMul_fastDFT_eq_cyclicConv spec hvalid hR_pos _ _ k hk_R,
        cyclicConv_getD_eq_polyMulList_getD spec.size xs ys hlen k hk_R,
        floor_natCast_add_half_toNat]
  have hpoly_len : (polyMulList xs ys).length ≤ k1 + k2 := by
    have := length_polyMulList_le xs ys
    rw [length_splitChunks, length_splitChunks] at this
    exact this
  dsimp only
  rw [hmap, reconstructChunks_eq_evalRadix, evalRadix_range_getD (2 ^ b) _ (k1 + k2) hpoly_len,
      ← reconstructChunks_eq_evalRadix]
  exact reconstructChunks_polyMulList_splitChunks b k1 k2 A B hA hB

/-- **Concrete Instantiation: `fastDFTMultiply` with the Paper's Box-Gaussian Passband Schedule**:
For any `1 ≤ m1 ≤ m2`, Gaussian shape parameter `α > 0`, valid child recursion `child` of size
`2^{m_2}`, chunk width `b`, and operands `A < (2^b)^{k_1}`, `B < (2^b)^{k_2}` with
`k1 + k2 ≤ 2^{m_1} * 2^{m_2}`, `fastDFTMultiply (boxGaussianStepSpec m1 m2 α child) b k1 k2 A B = A * B`. -/
theorem fastDFTMultiply_boxGaussianStepSpec_eq_mul
    (m1 m2 : ℕ) (hm1 : 1 ≤ m1) (hm12 : m1 ≤ m2)
    (α : ℝ) (hα : 0 < α) (child : FastDFTSpec)
    (hchild_size : child.size = 2 ^ m2) (hchild : child.Valid)
    (b k1 k2 : ℕ) (hk : k1 + k2 ≤ 2 ^ m1 * 2 ^ m2)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    fastDFTMultiply (boxGaussianStepSpec m1 m2 α child) b k1 k2 A B = A * B :=
  fastDFTMultiply_eq_mul (boxGaussianStepSpec m1 m2 α child)
    (boxGaussianStepSpec_valid m1 m2 hm1 hm12 α hα child hchild_size hchild)
    b k1 k2 hk A B hA hB

/-! ## Concrete Fixed-Point Quantization, Constructive Root Input Norm Bound, and Executable Bridges -/

/-! Note: `realQuantize`, `complexQuantize`, `abs_realQuantize_sub_le`,
`norm_complexQuantize_sub_le_nearest`, and `norm_complexQuantize_sub_le` are defined and proved in
`IntMul/Preliminaries.lean` (`[MS]` §3.2, Definition 3.1). -/

/-- Normalized complex-packed root input vector for two natural numbers `A, B` split into
radix-`2^b` chunks of lengths `k1` and `k2` (`[MS]` §3.5, Lemma 3.4 & §7.1):
`x_AB(j) = (A_j / 2^b) + i * (B_j / 2^b)`. -/
noncomputable def packNormalizedChunks (b k1 k2 : ℕ) (A B : ℕ) (j : ℕ) : ℂ :=
  ((((splitChunks b k1 A).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ)) : ℂ) +
    Complex.I * ((((splitChunks b k2 B).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ)) : ℂ)

/-- Every chunk extracted from `splitChunks b k A` (with default `0` out of bounds) is strictly
less than `2 ^ b`. -/
theorem splitChunks_getD_lt_two_pow (b k A j : ℕ) :
    (splitChunks b k A).getD j 0 < 2 ^ b := by
  have hb : 0 < 2 ^ b := pow_pos zero_lt_two b
  induction k generalizing A j with
  | zero =>
    simp [splitChunks, hb]
  | succ k ih =>
    cases j with
    | zero =>
      simp only [splitChunks, getD_cons_zero]
      exact Nat.mod_lt A hb
    | succ j =>
      simp only [splitChunks, getD_cons_succ]
      exact ih (A / 2 ^ b) j

/-- Every normalized chunk `(splitChunks b k A).getD j 0 / 2^b` lies in `[0, 1)`, so its
absolute value is at most `1`. -/
theorem abs_splitChunks_getD_div_le_one (b k A j : ℕ) :
    |(((splitChunks b k A).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ))| ≤ 1 := by
  have hb_nat : 0 < 2 ^ b := pow_pos zero_lt_two b
  have hb_real : (0 : ℝ) < ((2 ^ b : ℕ) : ℝ) := by exact_mod_cast hb_nat
  have hlt : ((splitChunks b k A).getD j 0 : ℝ) < ((2 ^ b : ℕ) : ℝ) := by
    exact_mod_cast splitChunks_getD_lt_two_pow b k A j
  have hnonneg : (0 : ℝ) ≤ ((splitChunks b k A).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hb_real.le
  have hle_one : ((splitChunks b k A).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ) ≤ 1 :=
    (div_lt_one hb_real).mpr hlt |>.le
  rw [abs_of_nonneg hnonneg]
  exact hle_one

/-- **Pointwise Euclidean Norm Bound for `packNormalizedChunks` (`[MS]` §7.1)**:
Since both the real part `A_j / 2^b` and imaginary part `B_j / 2^b` lie in `[0, 1)`, the complex
packed input satisfies `‖packNormalizedChunks b k1 k2 A B j‖ ≤ √2` for all `j : ℕ`. -/
theorem norm_packNormalizedChunks_le_sqrt_two (b k1 k2 A B j : ℕ) :
    ‖packNormalizedChunks b k1 k2 A B j‖ ≤ Real.sqrt 2 := by
  have hnorm : ‖packNormalizedChunks b k1 k2 A B j‖ =
      Real.sqrt ((packNormalizedChunks b k1 k2 A B j).re ^ 2 +
        (packNormalizedChunks b k1 k2 A B j).im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    ring_nf
  have hre : (packNormalizedChunks b k1 k2 A B j).re =
      ((splitChunks b k1 A).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ) := by
    unfold packNormalizedChunks
    simp only [← Complex.ofReal_div, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : (packNormalizedChunks b k1 k2 A B j).im =
      ((splitChunks b k2 B).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ) := by
    unfold packNormalizedChunks
    simp only [← Complex.ofReal_div, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hnorm, hre, him]
  have hbound := complex_rounding_norm_le
    (((splitChunks b k1 A).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ))
    (((splitChunks b k2 B).getD j 0 : ℝ) / ((2 ^ b : ℕ) : ℝ))
    1 (by norm_num)
    (abs_splitChunks_getD_div_le_one b k1 A j)
    (abs_splitChunks_getD_div_le_one b k2 B j)
  simpa using hbound

/-- **Constructive Root Forward-DFT Norm Bound (`hw` in `[MS]` Theorem 1, §7.2)**:
For any root transform length `R0 > 0`, any chunk width `b`, any chunk counts `k1, k2`, any
natural numbers `A, B`, and any frequency index `u : ℕ`, the exact 1D DFT mode of the normalized
complex-packed input `packNormalizedChunks b k1 k2 A B` satisfies
`‖dft1D R0 (packNormalizedChunks b k1 k2 A B) u‖ ≤ √2`. -/
theorem dft1D_packNormalizedChunks_norm_le_sqrt_two
    (R0 : ℕ) (hR0 : 0 < R0) (b k1 k2 A B u : ℕ) :
    ‖dft1D R0 (packNormalizedChunks b k1 k2 A B) u‖ ≤ Real.sqrt 2 :=
  dft1D_norm_le R0 hR0 (packNormalizedChunks b k1 k2 A B) (Real.sqrt 2)
    (fun j _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B j) u

/-- **Concrete Instantiation of `theorem5_root_pipeline_exact_int_recovery` with `packNormalizedChunks` and `complexQuantize`**:
At the root level (`R0 > 0`, `p_0 = rootPrecision b K0`), using the concrete normalized input
`w = dft1D R0 (packNormalizedChunks b k1 k2 A B) u` and the concrete fixed-point rounding operator
`S_tilde = complexQuantize (rootPrecision b K0) (y ^ 2)` constructively discharges both `hw` and `hS`
in `theorem5_root_pipeline_exact_int_recovery`. -/
theorem theorem5_root_pipeline_concrete_quantize_and_pack
    (R0 : ℕ) (hR0 : 0 < R0) (b K0 k1 k2 A B u : ℕ)
    (y : ℂ) (err_inv C_approx : ℝ) (C : ℤ)
    (hy : ‖y - dft1D R0 (packNormalizedChunks b k1 k2 A B) u‖ ≤
      Real.sqrt 2 * (2 : ℝ) ^ (-(rootPrecision b K0 : ℤ)))
    (hinv : err_inv ≤
      ‖complexQuantize (rootPrecision b K0) (y ^ 2) -
        (dft1D R0 (packNormalizedChunks b k1 k2 A B) u) ^ 2‖ +
        3 * (2 : ℝ) ^ (-(rootPrecision b K0 : ℤ)))
    (hC : |C_approx - (C : ℝ)| ≤ err_inv * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)) :
    ⌊C_approx + (1 / 2 : ℝ)⌋ = C :=
  theorem5_root_pipeline_exact_int_recovery b K0
    (dft1D R0 (packNormalizedChunks b k1 k2 A B) u)
    y
    (complexQuantize (rootPrecision b K0) (y ^ 2))
    err_inv C_approx C
    (dft1D_packNormalizedChunks_norm_le_sqrt_two R0 hR0 b k1 k2 A B u)
    hy
    (norm_complexQuantize_sub_le (rootPrecision b K0) (y ^ 2))
    hinv hC

/-- Single-step bridge between executable `negacyclicShiftInt 1` on `Fin r → ℤ` and complex
`negacyclicShiftStep r` on `ℕ → ℂ`:
whenever `P : Fin r → ℤ` and `B : ℕ → ℂ` agree on `0 .. r - 1` (`∀ m : Fin r, (P m : ℂ) = B m.val`),
`negacyclicShiftInt 1 P` and `negacyclicShiftStep r B` agree on `0 .. r - 1`. -/
theorem negacyclicShiftInt_one_cast_eq_negacyclicShiftStep {r : ℕ}
    (P : Fin r → ℤ) (B : ℕ → ℂ) (hPB : ∀ m : Fin r, (P m : ℂ) = B m.val) (m : Fin r) :
    (negacyclicShiftInt 1 P m : ℂ) = negacyclicShiftStep r B m.val := by
  have hr : 0 < r := Nat.pos_of_ne_zero (by have := m.isLt; omega)
  have hm : m.val < r := m.isLt
  dsimp only [negacyclicShiftInt, negacyclicShiftStep]
  have hs1 : 1 % (2 * r) = 1 := Nat.mod_eq_of_lt (by omega)
  by_cases hm0 : m.val = 0
  · have hraw : m.val + 2 * r - 1 % (2 * r) = (r - 1) + r * 1 := by omega
    have hdiv : (m.val + 2 * r - 1 % (2 * r)) / r = 1 := by
      rw [hraw, Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt (by omega)]
    have hmod : (m.val + 2 * r - 1 % (2 * r)) % r = r - 1 := by
      rw [hraw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hpar : ¬(((m.val + 2 * r - 1 % (2 * r)) / r) % 2 = 0) := by omega
    rw [if_neg hpar, if_pos hm0, Int.cast_neg]
    congr 1
    have hfin := hPB ⟨(m.val + 2 * r - 1 % (2 * r)) % r, Nat.mod_lt _ hr⟩
    simpa [hmod] using hfin
  · have hraw : m.val + 2 * r - 1 % (2 * r) = (m.val - 1) + r * 2 := by omega
    have hdiv : (m.val + 2 * r - 1 % (2 * r)) / r = 2 := by
      rw [hraw, Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt (by omega)]
    have hmod : (m.val + 2 * r - 1 % (2 * r)) % r = m.val - 1 := by
      rw [hraw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hpar : ((m.val + 2 * r - 1 % (2 * r)) / r) % 2 = 0 := by omega
    rw [if_pos hpar, if_neg hm0]
    have hfin := hPB ⟨(m.val + 2 * r - 1 % (2 * r)) % r, Nat.mod_lt _ hr⟩
    simpa [hmod] using hfin

/-- Multi-step bridge between executable `negacyclicShiftInt s` on `Fin r → ℤ` and complex
`negacyclicShiftIter r s` on `ℕ → ℂ` for any `P` and `B` agreeing on `0 .. r - 1`. -/
theorem negacyclicShiftInt_cast_eq_negacyclicShiftIter_of_eq {r : ℕ} (s : ℕ)
    (P : Fin r → ℤ) (B : ℕ → ℂ) (hPB : ∀ m : Fin r, (P m : ℂ) = B m.val) (m : Fin r) :
    (negacyclicShiftInt s P m : ℂ) = negacyclicShiftIter r s B m.val := by
  induction s generalizing P B m with
  | zero =>
    rw [negacyclicShiftInt_zero, hPB m]
    rfl
  | succ s ih =>
    have hadd := negacyclicShiftInt_add_steps 1 s P m
    rw [Nat.add_comm 1 s] at hadd
    rw [hadd, negacyclicShiftInt_one_cast_eq_negacyclicShiftStep
      (negacyclicShiftInt s P) (negacyclicShiftIter r s B)
      (fun m' => ih P B hPB m') m]
    unfold negacyclicShiftIter
    rw [Function.iterate_succ_apply']

/-- **Bridge Between Executable `negacyclicShiftInt` and Complex `negacyclicShiftIter` (`[MS]` §3.5, Lemma 3.5)**:
For any `r`, shift `s : ℕ`, integer polynomial `P : Fin r → ℤ`, and coefficient index `m : Fin r`,
casting `negacyclicShiftInt s P m` to `ℂ` equals the complex iterated negacyclic shift
`negacyclicShiftIter r s (fun k2 => if hk2 : k2 < r then (P ⟨k2, hk2⟩ : ℂ) else 0) m.val`. -/
theorem negacyclicShiftInt_cast_eq_negacyclicShiftIter {r : ℕ} (s : ℕ)
    (P : Fin r → ℤ) (m : Fin r) :
    (negacyclicShiftInt s P m : ℂ) =
      negacyclicShiftIter r s (fun k2 => if hk2 : k2 < r then (P ⟨k2, hk2⟩ : ℂ) else 0) m.val :=
  negacyclicShiftInt_cast_eq_negacyclicShiftIter_of_eq s P
    (fun k2 => if hk2 : k2 < r then (P ⟨k2, hk2⟩ : ℂ) else 0)
    (fun m' => by simp [m'.isLt]) m

/-- **Bridge Between Executable `FFTVec` `syntheticFFTRadix2` and Complex `syntheticFFTRadix2C` (`[MS]` §3.5, Lemma 3.5)**:
When `c1 * 2 ^ k = r`, running the executable `k`-stage addition-only Radix-2 Cooley-Tukey
transform `syntheticFFTRadix2 k (cooleyTukeyTwiddle k c1) (ofFnFFTVec k P)` over `ℤ[y]/(y^r + 1)`
and casting the `v`-th output slot (`v < 2^k`) to `ℂ` equals `(2 ^ k : ℂ)` times the complex
Radix-2 Cooley-Tukey Synthetic FFT `syntheticFFTRadix2C r k c1` at frequency `bitRev k v`. -/
theorem getFFTVec_syntheticFFTRadix2_cast_eq_syntheticFFTRadix2C {r : ℕ}
    (k c1 : ℕ) (hc1 : c1 * 2 ^ k = r) (P : ℕ → Fin r → ℤ)
    (v : ℕ) (hv : v < 2 ^ k) (m : Fin r) :
    (getFFTVec k (syntheticFFTRadix2 k (cooleyTukeyTwiddle k c1) (ofFnFFTVec k P)) v m : ℂ) =
      ((2 : ℂ) ^ k) *
        syntheticFFTRadix2C r k c1
          (fun j1 k2 => if hk2 : k2 < r then (P j1 ⟨k2, hk2⟩ : ℂ) else 0)
          (bitRev k v) m.val := by
  rw [syntheticFFTRadix2_eq_direct k c1 hc1 P v hv m, Int.cast_sum]
  rw [syntheticFFTRadix2C_eq_syntheticDFTWithStride]
  unfold syntheticDFTWithStride
  have hpow_ne : ((2 ^ k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero k (by decide))
  have hcast_pow : ((2 : ℂ) ^ k) = ((2 ^ k : ℕ) : ℂ) := by push_cast; rfl
  rw [hcast_pow, ← mul_assoc, mul_one_div_cancel hpow_ne, one_mul]
  refine Finset.sum_congr rfl fun j1 _ => ?_
  exact negacyclicShiftInt_cast_eq_negacyclicShiftIter (2 * c1 * j1 * bitRev k v) (P j1) m

/-- **Bridge Between Executable `FFTVec` `syntheticFFTRadix2` and Complex `syntheticDFT` (`[MS]` §3.5, Lemma 3.5)**:
When `c1 * 2 ^ k = r`, casting the `v`-th output slot (`v < 2^k`) of
`syntheticFFTRadix2 k (cooleyTukeyTwiddle k c1) (ofFnFFTVec k P)` to `ℂ` equals `(2 ^ k : ℂ)`
times `syntheticDFT (2 ^ k) r` at frequency `bitRev k v`. -/
theorem getFFTVec_syntheticFFTRadix2_cast_eq_syntheticDFT {r : ℕ}
    (k c1 : ℕ) (hc1 : c1 * 2 ^ k = r) (P : ℕ → Fin r → ℤ)
    (v : ℕ) (hv : v < 2 ^ k) (m : Fin r) :
    (getFFTVec k (syntheticFFTRadix2 k (cooleyTukeyTwiddle k c1) (ofFnFFTVec k P)) v m : ℂ) =
      ((2 : ℂ) ^ k) *
        syntheticDFT (2 ^ k) r
          (fun j1 k2 => if hk2 : k2 < r then (P j1 ⟨k2, hk2⟩ : ℂ) else 0)
          (bitRev k v) m.val := by
  rw [getFFTVec_syntheticFFTRadix2_cast_eq_syntheticFFTRadix2C k c1 hc1 P v hv m]
  have hdiv : r / 2 ^ k = c1 := by
    rw [← hc1, Nat.mul_div_cancel c1 (pow_pos zero_lt_two k)]
  rw [← syntheticFFTRadix2C_eq_syntheticDFT, hdiv]

/-! Note: `length_polyAddInt`, `length_polyScaleInt`, `length_polyMulInt_of_ne_nil`,
`length_polyMulInt_nil_right`, `length_polyMulInt_eq`, `length_polyMulInt_le`, `polyAddInt_getD`,
`polyScaleInt_getD`, `polyMulInt_getD`, `getD_natAbs_le_listMaxNatAbs`,
`abs_getD_le_listMaxNatAbs`, `exists_getD_of_mem`, `kroneckerHeadroom_pos`,
`polyMulInt_mem_bounds_kroneckerHeadroom`, `kroneckerHeadroom_le_two_pow_kroneckerBitStride`,
`polyMulKroneckerSignedH_eq_polyMulInt`, `polyMulKroneckerSignedH_kroneckerHeadroom_eq`,
`polyMulKroneckerSigned_eq_polyMulInt`, `polyMulKroneckerSigned_eq_polyMulInt_of_ne_nil`,
`polyMulKroneckerSigned_kroneckerHeadroom_eq`, and `polyMulKroneckerSigned_kroneckerBitStride_eq`
are proved in `IntMul/Theorem4KroneckerSpread.lean`. -/

/-! ## Instrumented Recursive `fastDFTWithCost` & `fastDFTMultiplyWithCost` and `O(n log n)` Cost Bridges -/

/-- Instrumented multi-level recursive `fastDFT`:
returns `(out, totalCost)`, where `out` is the transformed vector `ℕ → ℂ` and `totalCost : ℝ`
is the exact recursive cost accumulated by adding `localSyn l + localOvh l` at depth `l` to the
sum `∑ v1 ∈ Finset.range t1, (childRes v1).2` across all `t1` recursive child calls at depth `l + 1`
(and `localBase l` at a leaf `.base R` at depth `l`). -/
noncomputable def fastDFTWithCost :
    FastDFTSpec → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → (ℕ → ℂ) → (ℕ → ℂ) × ℝ
  | .base R, _, _, localBase, l, x =>
    (dft1D R x, localBase l)
  | .step t1 r _c1 c0 c1_pass v1Of child, localSyn, localOvh, localBase, l, x =>
    let U := spreadArray2Tap t1 r c0 c1_pass x
    let P : ℕ → ℕ → ℂ := fun j1 k2 => zetaRoot r (k2 : ℝ) * U j1 k2
    let Q : ℕ → ℕ → ℂ := syntheticDFT t1 r P
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 => zetaRoot r (-(k2 : ℝ)) * Q v1 k2
    let childRes := fun v1 => fastDFTWithCost child localSyn localOvh localBase (l + 1) (qPost v1)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => (childRes v1).1 u2
    let childCostSum : ℝ := ∑ v1 ∈ Finset.range t1, (childRes v1).2
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => qHat (v1Of u2 u1) u2
    let out : ℕ → ℂ := fun u =>
      let u2 := u % r
      let u1_tilde := u / r
      if 2 * u2 < r then
        solveBidiagonalFwd t1 (c0 u2) (c1_pass u2) (Y u2) u1_tilde
      else if 2 * u2 = r then
        solveNyquist t1 (c0 u2) (Y u2) (nyquistAltSum t1 r x) u1_tilde
      else
        solveBidiagonalBwd t1 (c0 u2) (c1_pass u2) (Y u2) u1_tilde
    (out, localSyn l + localOvh l + childCostSum)

/-- **First-Projection Equivalence (`fastDFTWithCost` computes `fastDFT`)**:
For any `spec : FastDFTSpec`, cost functions `localSyn localOvh localBase : ℕ → ℝ`, depth `l : ℕ`,
and input `x : ℕ → ℂ`, the first component of `fastDFTWithCost spec localSyn localOvh localBase l x`
is identically equal to `fastDFT spec x`. -/
theorem fastDFTWithCost_fst_eq
    (spec : FastDFTSpec) (localSyn localOvh localBase : ℕ → ℝ) (l : ℕ) (x : ℕ → ℂ) :
    (fastDFTWithCost spec localSyn localOvh localBase l x).1 = fastDFT spec x := by
  induction spec generalizing l x with
  | base R => rfl
  | step t1 r c1 c0 c1_pass v1Of child ih =>
    funext u
    dsimp only [fastDFTWithCost, fastDFT]
    simp only [ih]

/-- Predicate stating that a `FastDFTSpec` tree matches a dimension schedule `(t1, R : ℕ → ℕ)`
with `rem` levels remaining starting at recursion depth `l`:
- At `rem = 0`, the spec is `.base (R l)`.
- At `rem + 1`, the spec is `.step (t1 l) (R (l + 1)) c1 c0 c1_pass v1Of child` where `child`
  matches `(t1, R)` with `rem` levels remaining at depth `l + 1`. -/
inductive FastDFTSpec.MatchesSchedule (t1 R : ℕ → ℕ) : ℕ → ℕ → FastDFTSpec → Prop where
  | base (l : ℕ) : FastDFTSpec.MatchesSchedule t1 R 0 l (.base (R l))
  | step {rem l : ℕ} (c1 : ℕ) (c0 c1_pass : ℕ → ℂ) (v1Of : ℕ → ℕ → ℕ) (child : FastDFTSpec)
      (hchild : FastDFTSpec.MatchesSchedule t1 R rem (l + 1) child) :
      FastDFTSpec.MatchesSchedule t1 R (rem + 1) l
        (.step (t1 l) (R (l + 1)) c1 c0 c1_pass v1Of child)

/-- **Exact Cost-Recurrence Bridge (`fastDFTWithCost` Accumulates `fastDFTBranchingCost`)**:
Whenever `spec : FastDFTSpec` matches a dimension schedule `(t1, R)` of remaining depth `rem`
starting at level `l` (`FastDFTSpec.MatchesSchedule t1 R rem l spec`), the accumulated cost
`(fastDFTWithCost spec localSyn localOvh localBase l x).2` across all `∑ v1 ∈ Finset.range (t1 l)`
recursive child calls is **identically equal** to
`fastDFTBranchingCost t1 localSyn localOvh localBase rem l`. -/
theorem fastDFTWithCost_snd_eq_branchingCost
    (t1 R : ℕ → ℕ) (localSyn localOvh localBase : ℕ → ℝ)
    (rem l : ℕ) (spec : FastDFTSpec)
    (hsched : FastDFTSpec.MatchesSchedule t1 R rem l spec) (x : ℕ → ℂ) :
    (fastDFTWithCost spec localSyn localOvh localBase l x).2 =
      fastDFTBranchingCost t1 localSyn localOvh localBase rem l := by
  induction hsched generalizing x with
  | base l =>
    rfl
  | @step rem l c1 c0 c1_pass v1Of child hchild ih =>
    dsimp only [fastDFTWithCost, fastDFTBranchingCost]
    have hsum :
        (∑ v1 ∈ Finset.range (t1 l),
          (fastDFTWithCost child localSyn localOvh localBase (l + 1)
            (fun k2 => zetaRoot (R (l + 1)) (-(k2 : ℝ)) *
              syntheticDFT (t1 l) (R (l + 1))
                (fun j1 k2 => zetaRoot (R (l + 1)) (k2 : ℝ) *
                  spreadArray2Tap (t1 l) (R (l + 1)) c0 c1_pass x j1 k2) v1 k2)).2) =
        (t1 l : ℝ) * fastDFTBranchingCost t1 localSyn localOvh localBase rem (l + 1) := by
      calc _ = ∑ _v1 ∈ Finset.range (t1 l),
            fastDFTBranchingCost t1 localSyn localOvh localBase rem (l + 1) :=
            Finset.sum_congr rfl fun v1 _ => ih _
        _ = (t1 l : ℝ) * fastDFTBranchingCost t1 localSyn localOvh localBase rem (l + 1) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]

/-- Instrumented recursive Inverse Fast DFT (`fastIDFTWithCost`), computed via `fastDFTWithCost`
using the conjugate-DFT identity: returns `(fastIDFT spec X, cost)`. -/
noncomputable def fastIDFTWithCost
    (spec : FastDFTSpec) (localSyn localOvh localBase : ℕ → ℝ) (l : ℕ) (X : ℕ → ℂ) :
    (ℕ → ℂ) × ℝ :=
  let res := fastDFTWithCost spec localSyn localOvh localBase l (fun u => star (X u))
  (fun j => (spec.size : ℂ) * star (res.1 j), res.2)

/-- **First-Projection Equivalence (`fastIDFTWithCost` computes `fastIDFT`)**:
For any `spec : FastDFTSpec`, cost functions `localSyn localOvh localBase : ℕ → ℝ`, depth `l : ℕ`,
and input `X : ℕ → ℂ`, `(fastIDFTWithCost spec localSyn localOvh localBase l X).1 = fastIDFT spec X`. -/
theorem fastIDFTWithCost_fst_eq
    (spec : FastDFTSpec) (localSyn localOvh localBase : ℕ → ℝ) (l : ℕ) (X : ℕ → ℂ) :
    (fastIDFTWithCost spec localSyn localOvh localBase l X).1 = fastIDFT spec X := by
  funext j
  dsimp only [fastIDFTWithCost, fastIDFT]
  rw [fastDFTWithCost_fst_eq]

/-- **Exact Cost-Recurrence Bridge (`fastIDFTWithCost` Accumulates `fastDFTBranchingCost`)**:
Whenever `FastDFTSpec.MatchesSchedule t1 R rem l spec`, the accumulated cost of `fastIDFTWithCost`
equals `fastDFTBranchingCost t1 localSyn localOvh localBase rem l`. -/
theorem fastIDFTWithCost_snd_eq_branchingCost
    (t1 R : ℕ → ℕ) (localSyn localOvh localBase : ℕ → ℝ)
    (rem l : ℕ) (spec : FastDFTSpec)
    (hsched : FastDFTSpec.MatchesSchedule t1 R rem l spec) (X : ℕ → ℂ) :
    (fastIDFTWithCost spec localSyn localOvh localBase l X).2 =
      fastDFTBranchingCost t1 localSyn localOvh localBase rem l := by
  dsimp only [fastIDFTWithCost]
  exact fastDFTWithCost_snd_eq_branchingCost t1 R localSyn localOvh localBase rem l spec hsched _

/-- Instrumented end-to-end integer multiplication pipeline (`fastDFTMultiplyWithCost`):
executes two forward `fastDFTWithCost` transforms on the radix-`2^b` chunk vectors of `A` and `B`,
multiplies the frequency-domain outputs pointwise by `spec.size`, executes one inverse
`fastIDFTWithCost` transform, rounds and propagates carries via `reconstructChunks b`, and
accumulates the total transform cost `fwdA.2 + fwdB.2 + invC.2`. -/
noncomputable def fastDFTMultiplyWithCost
    (spec : FastDFTSpec) (localSyn localOvh localBase : ℕ → ℝ)
    (b k1 k2 : ℕ) (A B : ℕ) : ℕ × ℝ :=
  let xs := splitChunks b k1 A
  let ys := splitChunks b k2 B
  let a : ℕ → ℂ := fun j => (xs.getD j 0 : ℂ)
  let g : ℕ → ℂ := fun j => (ys.getD j 0 : ℂ)
  let fwdA := fastDFTWithCost spec localSyn localOvh localBase 0 a
  let fwdB := fastDFTWithCost spec localSyn localOvh localBase 0 g
  let invC := fastIDFTWithCost spec localSyn localOvh localBase 0
    (fun u => (spec.size : ℂ) * fwdA.1 u * fwdB.1 u)
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun k => ⌊(invC.1 k).re + (1 / 2 : ℝ)⌋.toNat)
  (reconstructChunks b convNat, fwdA.2 + fwdB.2 + invC.2)

/-- **First-Projection Equivalence (`fastDFTMultiplyWithCost` computes `fastDFTMultiply`)**:
For any `spec : FastDFTSpec`, cost functions `localSyn localOvh localBase : ℕ → ℝ`, chunk width `b`,
chunk counts `k1, k2`, and operands `A, B : ℕ`,
`(fastDFTMultiplyWithCost spec localSyn localOvh localBase b k1 k2 A B).1 = fastDFTMultiply spec b k1 k2 A B`. -/
theorem fastDFTMultiplyWithCost_fst_eq
    (spec : FastDFTSpec) (localSyn localOvh localBase : ℕ → ℝ)
    (b k1 k2 : ℕ) (A B : ℕ) :
    (fastDFTMultiplyWithCost spec localSyn localOvh localBase b k1 k2 A B).1 =
      fastDFTMultiply spec b k1 k2 A B := by
  dsimp only [fastDFTMultiplyWithCost, fastDFTMultiply]
  rw [fastIDFTWithCost_fst_eq, fastDFTWithCost_fst_eq, fastDFTWithCost_fst_eq]

/-- **Exact Product Correctness of `fastDFTMultiplyWithCost`**:
For any valid multi-level recursion tree `spec : FastDFTSpec` (`hvalid : spec.Valid`),
any chunk width `b`, any chunk counts `k1, k2` with `k1 + k2 ≤ spec.size`, and any natural
numbers `A < (2^b)^{k_1}` and `B < (2^b)^{k_2}`, the first component of
`fastDFTMultiplyWithCost spec localSyn localOvh localBase b k1 k2 A B` equals the exact integer
product `A * B`. -/
theorem fastDFTMultiplyWithCost_fst_eq_mul
    (spec : FastDFTSpec) (hvalid : spec.Valid)
    (localSyn localOvh localBase : ℕ → ℝ)
    (b k1 k2 : ℕ) (hk : k1 + k2 ≤ spec.size)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    (fastDFTMultiplyWithCost spec localSyn localOvh localBase b k1 k2 A B).1 = A * B := by
  rw [fastDFTMultiplyWithCost_fst_eq]
  exact fastDFTMultiply_eq_mul spec hvalid b k1 k2 hk A B hA hB

/-- **Exact Cost-Recurrence Bridge for `fastDFTMultiplyWithCost`**:
Whenever `FastDFTSpec.MatchesSchedule t1 R L 0 spec`, the accumulated cost of the two forward
`fastDFTWithCost` transforms and one inverse `fastIDFTWithCost` transform in
`fastDFTMultiplyWithCost` equals `3 * fastDFTBranchingCost t1 localSyn localOvh localBase L 0`. -/
theorem fastDFTMultiplyWithCost_snd_eq_branchingCost
    (t1 R : ℕ → ℕ) (localSyn localOvh localBase : ℕ → ℝ)
    (L : ℕ) (spec : FastDFTSpec)
    (hsched : FastDFTSpec.MatchesSchedule t1 R L 0 spec)
    (b k1 k2 : ℕ) (A B : ℕ) :
    (fastDFTMultiplyWithCost spec localSyn localOvh localBase b k1 k2 A B).2 =
      3 * fastDFTBranchingCost t1 localSyn localOvh localBase L 0 := by
  dsimp only [fastDFTMultiplyWithCost]
  rw [fastDFTWithCost_snd_eq_branchingCost t1 R localSyn localOvh localBase L 0 spec hsched,
      fastDFTWithCost_snd_eq_branchingCost t1 R localSyn localOvh localBase L 0 spec hsched,
      fastIDFTWithCost_snd_eq_branchingCost t1 R localSyn localOvh localBase L 0 spec hsched]
  ring

/-- Concrete level-`d` Synthetic FFT real bit-operation count derived from the instrumented
operation counter `syntheticFFTRadix2WithCost`:
`2 * syntheticFFTRadix2AddOps (R (d + 1)) (k1 d)` real `P`-bit additions/subtractions
(one real and one imaginary `P`-bit addition/subtraction per complex ring operation, with
`syntheticFFTRadix2MulOps (R (d + 1)) (k1 d) = 0` multiplications). -/
def concreteLocalSynBitOps (R k1 : ℕ → ℕ) (P : ℝ) (d : ℕ) : ℝ :=
  ((2 * syntheticFFTRadix2AddOps (R (d + 1)) (k1 d) : ℕ) : ℝ) * P

/-- **Bridge from Instrumented `syntheticFFTRadix2WithCost` to Per-Element Synthetic FFT Work**:
Under unit expansion `R d = 2 ^ (k1 d) * R (d + 1)`, for any twiddle schedule `tw` and input
`X : FFTVec (R (d + 1)) (k1 d)`, the operation count `(syntheticFFTRadix2WithCost (k1 d) tw X).2`
has `0` multiplications and `syntheticFFTRadix2AddOps (R (d + 1)) (k1 d)` complex additions, so the
corresponding real `P`-bit operation count `concreteLocalSynBitOps R k1 P d` factors as
`(R d : ℝ) * (2 * (k1 d : ℝ) * P)`. -/
theorem concreteLocalSynBitOps_eq_of_syntheticFFTRadix2WithCost
    (R k1 : ℕ → ℕ) (P : ℝ) (d : ℕ)
    (hR : R d = 2 ^ (k1 d) * R (d + 1))
    (tw : ℕ → ℕ → ℕ) (X : FFTVec (R (d + 1)) (k1 d)) :
    (syntheticFFTRadix2WithCost (k1 d) tw X).2.2 = 0 ∧
    (((2 * (syntheticFFTRadix2WithCost (k1 d) tw X).2.1 : ℕ) : ℝ) * P) =
      concreteLocalSynBitOps R k1 P d ∧
    concreteLocalSynBitOps R k1 P d = (R d : ℝ) * (2 * (k1 d : ℝ) * P) := by
  have hcost := syntheticFFTRadix2WithCost_eq (k1 d) tw X
  have h1 : (syntheticFFTRadix2WithCost (k1 d) tw X).2.1 =
      syntheticFFTRadix2AddOps (R (d + 1)) (k1 d) := by
    rw [hcost]
  have h2 : (syntheticFFTRadix2WithCost (k1 d) tw X).2.2 =
      syntheticFFTRadix2MulOps (R (d + 1)) (k1 d) := by
    rw [hcost]
  have hclosed := syntheticFFTRadix2Ops_closed_form (R (d + 1)) (k1 d)
  refine ⟨by rw [h2, hclosed.1], by rw [h1]; rfl, ?_⟩
  unfold concreteLocalSynBitOps
  rw [hclosed.2.1, ← hR]
  push_cast
  ring

/-- Concrete level-`d` Overlap-Add Kronecker spreading + twist + bidiagonal solve bit-operation
count across `R d / W_eff d` Overlap-Add blocks of window width `W_eff d > 0` (`[MS]` §6.2, Theorem 6.3):
`C_oa * ((R d / W_eff d) * ((W_eff d * B_slot) * logFactor))` for the Kronecker block
multiplications plus `C_bid * R d * (B_slot * logFactor)` for the pre/post twists and bidiagonal
deconvolution sweep. -/
noncomputable def concreteLocalOvhBitOps
    (R : ℕ → ℕ) (W_eff : ℕ → ℝ) (C_oa C_bid B_slot logFactor : ℝ) (d : ℕ) : ℝ :=
  C_oa * (((R d : ℝ) / W_eff d) * ((W_eff d * B_slot) * logFactor)) +
    C_bid * (R d : ℝ) * (B_slot * logFactor)

/-- **Bridge from `theorem4_window_width_cancellation` to Per-Element Overlap-Add Overhead**:
Whenever `W_eff d ≠ 0`, `theorem4_window_width_cancellation` cancels the window width `W_eff d`
between the block count `R d / W_eff d` and the block bit-length `W_eff d * B_slot`, so
`concreteLocalOvhBitOps R W_eff C_oa C_bid B_slot logFactor d` factors identically as
`(R d : ℝ) * ((C_oa + C_bid) * (B_slot * logFactor))`. -/
theorem concreteLocalOvhBitOps_eq_of_window_width_cancellation
    (R : ℕ → ℕ) (W_eff : ℕ → ℝ) (C_oa C_bid B_slot logFactor : ℝ) (d : ℕ)
    (hW : W_eff d ≠ 0) :
    concreteLocalOvhBitOps R W_eff C_oa C_bid B_slot logFactor d =
      (R d : ℝ) * ((C_oa + C_bid) * (B_slot * logFactor)) := by
  unfold concreteLocalOvhBitOps
  rw [theorem4_window_width_cancellation (R d : ℝ) (W_eff d) B_slot logFactor hW]
  ring

/-- **Instrumented `fastDFTWithCost` Root Complexity Bound (`fastDFTWithCost_snd_le_multiplyBitComplexityBound`)**:
When `spec : FastDFTSpec` matches a unit-expansion schedule `(t1, R)` of depth `L`
(`FastDFTSpec.MatchesSchedule t1 R L 0 spec`, `∀ d, R d = t1 d * R (d + 1)`), the accumulated
cost `(fastDFTWithCost spec localSyn localOvh localBase 0 x).2` is bounded above by
`multiplyBitComplexityBound C_syn C_ovh C_base n`. -/
theorem fastDFTWithCost_snd_le_multiplyBitComplexityBound
    (L n : ℕ) (t1 R : ℕ → ℕ)
    (localSyn localOvh localBase perElemSyn perElemOvh perElemBase : ℕ → ℝ)
    (C_syn C_ovh C_base K0_P P_log_P : ℝ)
    (spec : FastDFTSpec) (hsched : FastDFTSpec.MatchesSchedule t1 R L 0 spec)
    (hR : ∀ d, R d = t1 d * R (d + 1))
    (hSyn : ∀ d, localSyn d = (R d : ℝ) * perElemSyn d)
    (hOvh : ∀ d, localOvh d = (R d : ℝ) * perElemOvh d)
    (hBase : ∀ d, localBase d = (R d : ℝ) * perElemBase d)
    (hC_syn : 0 ≤ C_syn) (hC_ovh_base : 0 ≤ C_ovh + C_base) (hK0_P : 0 ≤ K0_P)
    (h_syn : ∀ d ∈ Finset.range L, perElemSyn d ≤ C_syn * ((1 / 2 : ℝ) ^ d) * K0_P)
    (h_ovh : ∀ d ∈ Finset.range L, perElemOvh d ≤ C_ovh * P_log_P)
    (h_base : perElemBase L ≤ C_base * (L : ℝ) * P_log_P)
    (h_scale_syn : (R 0 : ℝ) * K0_P ≤ (n : ℝ) * Real.log (n : ℝ))
    (h_scale_ovh : (L : ℝ) * ((R 0 : ℝ) * P_log_P) ≤
      (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2)
    (x : ℕ → ℂ) :
    (fastDFTWithCost spec localSyn localOvh localBase 0 x).2 ≤
      multiplyBitComplexityBound C_syn C_ovh C_base n := by
  rw [fastDFTWithCost_snd_eq_branchingCost t1 R localSyn localOvh localBase L 0 spec hsched x]
  exact fastDFTBranchingCost_le_multiplyBitComplexityBound L n t1 R
    localSyn localOvh localBase perElemSyn perElemOvh perElemBase
    C_syn C_ovh C_base K0_P P_log_P
    hR hSyn hOvh hBase hC_syn hC_ovh_base hK0_P h_syn h_ovh h_base h_scale_syn h_scale_ovh

/-- **Instrumented `fastDFTMultiplyWithCost` Complexity Bound (`fastDFTMultiplyWithCost_snd_le_three_mul_multiplyBitComplexityBound`)**:
When `spec : FastDFTSpec` matches a unit-expansion schedule `(t1, R)` of depth `L`
(`FastDFTSpec.MatchesSchedule t1 R L 0 spec`, `∀ d, R d = t1 d * R (d + 1)`), the accumulated
cost `(fastDFTMultiplyWithCost spec localSyn localOvh localBase b k1 k2 A B).2` is bounded above
by `3 * multiplyBitComplexityBound C_syn C_ovh C_base n`. -/
theorem fastDFTMultiplyWithCost_snd_le_three_mul_multiplyBitComplexityBound
    (L n : ℕ) (t1 R : ℕ → ℕ)
    (localSyn localOvh localBase perElemSyn perElemOvh perElemBase : ℕ → ℝ)
    (C_syn C_ovh C_base K0_P P_log_P : ℝ)
    (spec : FastDFTSpec) (hsched : FastDFTSpec.MatchesSchedule t1 R L 0 spec)
    (hR : ∀ d, R d = t1 d * R (d + 1))
    (hSyn : ∀ d, localSyn d = (R d : ℝ) * perElemSyn d)
    (hOvh : ∀ d, localOvh d = (R d : ℝ) * perElemOvh d)
    (hBase : ∀ d, localBase d = (R d : ℝ) * perElemBase d)
    (hC_syn : 0 ≤ C_syn) (hC_ovh_base : 0 ≤ C_ovh + C_base) (hK0_P : 0 ≤ K0_P)
    (h_syn : ∀ d ∈ Finset.range L, perElemSyn d ≤ C_syn * ((1 / 2 : ℝ) ^ d) * K0_P)
    (h_ovh : ∀ d ∈ Finset.range L, perElemOvh d ≤ C_ovh * P_log_P)
    (h_base : perElemBase L ≤ C_base * (L : ℝ) * P_log_P)
    (h_scale_syn : (R 0 : ℝ) * K0_P ≤ (n : ℝ) * Real.log (n : ℝ))
    (h_scale_ovh : (L : ℝ) * ((R 0 : ℝ) * P_log_P) ≤
      (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2)
    (b k1 k2 A B : ℕ) :
    (fastDFTMultiplyWithCost spec localSyn localOvh localBase b k1 k2 A B).2 ≤
      3 * multiplyBitComplexityBound C_syn C_ovh C_base n := by
  rw [fastDFTMultiplyWithCost_snd_eq_branchingCost t1 R localSyn localOvh localBase L spec hsched]
  have hbound := fastDFTBranchingCost_le_multiplyBitComplexityBound L n t1 R
    localSyn localOvh localBase perElemSyn perElemOvh perElemBase
    C_syn C_ovh C_base K0_P P_log_P
    hR hSyn hOvh hBase hC_syn hC_ovh_base hK0_P h_syn h_ovh h_base h_scale_syn h_scale_ovh
  linarith

/-- **Concrete End-to-End Correctness and Complexity Bridge for `fastDFTMultiplyWithCost`**:
Instantiating `fastDFTMultiplyWithCost` with:
- `localSyn = concreteLocalSynBitOps R k1_stage P` (derived from `syntheticFFTRadix2WithCost`), and
- `localOvh = concreteLocalOvhBitOps R W_eff C_oa C_bid B_slot logFactor` (derived from
  `theorem4_window_width_cancellation`),
under unit expansion `∀ d, R d = 2 ^ (k1_stage d) * R (d + 1)` and `∀ d, W_eff d ≠ 0`, proves both:
1. `(fastDFTMultiplyWithCost ...).1 = A * B`, and
2. `(fastDFTMultiplyWithCost ...).2 ≤ 3 * multiplyBitComplexityBound C_syn (C_oa + C_bid) C_base n`. -/
theorem fastDFTMultiplyWithCost_concrete_ops_bound
    (L n : ℕ) (k1_stage R : ℕ → ℕ) (W_eff localBase perElemBase : ℕ → ℝ)
    (P C_syn C_oa C_bid C_base K0_P B_slot logFactor : ℝ)
    (spec : FastDFTSpec)
    (hvalid : spec.Valid)
    (hsched : FastDFTSpec.MatchesSchedule (fun d => 2 ^ (k1_stage d)) R L 0 spec)
    (hR : ∀ d, R d = 2 ^ (k1_stage d) * R (d + 1))
    (hW : ∀ d, W_eff d ≠ 0)
    (hBase : ∀ d, localBase d = (R d : ℝ) * perElemBase d)
    (hC_syn : 0 ≤ C_syn) (hC_ovh_base : 0 ≤ (C_oa + C_bid) + C_base) (hK0_P : 0 ≤ K0_P)
    (h_syn : ∀ d ∈ Finset.range L, 2 * (k1_stage d : ℝ) * P ≤ C_syn * ((1 / 2 : ℝ) ^ d) * K0_P)
    (h_base : perElemBase L ≤ C_base * (L : ℝ) * (B_slot * logFactor))
    (h_scale_syn : (R 0 : ℝ) * K0_P ≤ (n : ℝ) * Real.log (n : ℝ))
    (h_scale_ovh : (L : ℝ) * ((R 0 : ℝ) * (B_slot * logFactor)) ≤
      (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2)
    (b k1 k2 A B : ℕ) (hk : k1 + k2 ≤ spec.size)
    (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    (fastDFTMultiplyWithCost spec
      (concreteLocalSynBitOps R k1_stage P)
      (concreteLocalOvhBitOps R W_eff C_oa C_bid B_slot logFactor)
      localBase b k1 k2 A B).1 = A * B ∧
    (fastDFTMultiplyWithCost spec
      (concreteLocalSynBitOps R k1_stage P)
      (concreteLocalOvhBitOps R W_eff C_oa C_bid B_slot logFactor)
      localBase b k1 k2 A B).2 ≤
      3 * multiplyBitComplexityBound C_syn (C_oa + C_bid) C_base n := by
  refine ⟨fastDFTMultiplyWithCost_fst_eq_mul spec hvalid _ _ _ b k1 k2 hk A B hA hB, ?_⟩
  have hSyn : ∀ d, concreteLocalSynBitOps R k1_stage P d =
      (R d : ℝ) * (2 * (k1_stage d : ℝ) * P) := by
    intro d
    unfold concreteLocalSynBitOps
    rw [(syntheticFFTRadix2Ops_closed_form (R (d + 1)) (k1_stage d)).2.1, ← hR d]
    push_cast
    ring
  have hOvh : ∀ d, concreteLocalOvhBitOps R W_eff C_oa C_bid B_slot logFactor d =
      (R d : ℝ) * ((C_oa + C_bid) * (B_slot * logFactor)) := fun d =>
    concreteLocalOvhBitOps_eq_of_window_width_cancellation R W_eff C_oa C_bid B_slot logFactor d (hW d)
  exact fastDFTMultiplyWithCost_snd_le_three_mul_multiplyBitComplexityBound
    L n (fun d => 2 ^ (k1_stage d)) R
    (concreteLocalSynBitOps R k1_stage P)
    (concreteLocalOvhBitOps R W_eff C_oa C_bid B_slot logFactor)
    localBase
    (fun d => 2 * (k1_stage d : ℝ) * P)
    (fun _ => (C_oa + C_bid) * (B_slot * logFactor))
    perElemBase
    C_syn (C_oa + C_bid) C_base K0_P (B_slot * logFactor)
    spec hsched hR hSyn hOvh hBase hC_syn hC_ovh_base hK0_P
    h_syn (fun _ _ => le_rfl) h_base h_scale_syn h_scale_ovh b k1 k2 A B

/-- **Conditional Asymptotic `O(n log n)` Bit Complexity of Instrumented `fastDFTMultiplyWithCost` Given `h_bound`**:
For any family of recursion specifications `spec : ℕ → FastDFTSpec`, local cost schedules
`localSyn localOvh localBase : ℕ → ℕ → ℝ`, and inputs `b k1 k2 A B : ℕ → ℕ` whose accumulated
cost `(fastDFTMultiplyWithCost (spec n) ...).2` is non-negative and bounded by
`3 * multiplyBitComplexityBound C_syn C_ovh C_base n` for all `n ≥ 3` (as established by
`fastDFTMultiplyWithCost_snd_le_three_mul_multiplyBitComplexityBound` and
`fastDFTMultiplyWithCost_concrete_ops_bound`), the instrumented cost function satisfies
`(fun n => (fastDFTMultiplyWithCost (spec n) (localSyn n) (localOvh n) (localBase n) (b n) (k1 n) (k2 n) (A n) (B n)).2) =O[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))`. -/
theorem fastDFTMultiplyWithCost_snd_isBigO_n_log_n_of_bound
    (spec : ℕ → FastDFTSpec)
    (localSyn localOvh localBase : ℕ → ℕ → ℝ)
    (b k1 k2 A B : ℕ → ℕ)
    (C_syn C_ovh C_base : ℝ)
    (hC_ovh_base : 0 ≤ C_ovh + C_base)
    (h_nonneg : ∀ n, 3 ≤ n →
      0 ≤ (fastDFTMultiplyWithCost (spec n) (localSyn n) (localOvh n) (localBase n)
        (b n) (k1 n) (k2 n) (A n) (B n)).2)
    (h_bound : ∀ n, 3 ≤ n →
      (fastDFTMultiplyWithCost (spec n) (localSyn n) (localOvh n) (localBase n)
        (b n) (k1 n) (k2 n) (A n) (B n)).2 ≤
        3 * multiplyBitComplexityBound C_syn C_ovh C_base n) :
    (fun n : ℕ => (fastDFTMultiplyWithCost (spec n) (localSyn n) (localOvh n) (localBase n)
      (b n) (k1 n) (k2 n) (A n) (B n)).2) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (3 * (2 * C_syn + 4 * (C_ovh + C_base))) ?_
  rw [Filter.eventually_atTop]
  refine ⟨3, fun n hn => ?_⟩
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_ge_one : 1 ≤ Real.log (n : ℝ) := one_le_log_of_three_le (n : ℝ) hn_real
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by linarith
  have h_nlogn_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hn_nonneg hlog_nonneg
  have h_cost_nonneg := h_nonneg n hn
  rw [Real.norm_of_nonneg h_cost_nonneg, Real.norm_of_nonneg h_nlogn_nonneg]
  have h1 := h_bound n hn
  have h2 := theorem5_multiply_bit_complexity_le_n_log_n C_syn C_ovh C_base hC_ovh_base n hn
  linarith


end IntMul
