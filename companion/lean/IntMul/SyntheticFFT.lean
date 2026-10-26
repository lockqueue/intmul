import IntMul.Defs
import IntMul.FixedPoint

/-!
# Normalized 1D/2D DFT & Polynomial-Transform Reduction (`IntMul.SyntheticFFT`)

This module formalizes the DFT, two-call convolution, negacyclic polynomial-transform
(`syntheticFFT` in this development), and Nussbaumer–Quandalle polynomial-transform reduction
components of the paper (Section 3.1 (`sec:notation`), Section 3.5 (`sec:prelim-dft`),
Lemma 3.4 (`lem:two-call`), Lemma 3.5 (`lem:syn-fft`), Section 4.1 (`sec:twisted`),
Proposition 4.1 (`thm:twisted`)), together with restricted-model barrier identities retained from
an earlier draft:

1. **Normalized 1D/2D DFT Properties (Section 3.1 (`sec:notation`), Section 3.5 (`sec:prelim-dft`))**:
   - Basic properties of `vecInfNorm` and `matInfNorm` (`vecInfNorm_nonneg`, `norm_le_vecInfNorm`,
     `vecInfNorm_le_iff`, `matInfNorm_nonneg`, `norm_le_matInfNorm`, `matInfNorm_le_iff`).
   - Unit-modulus lemmas `norm_expTwoPiI`, `norm_expNegTwoPiI`, and `norm_zetaPow`.
   - $\ell_\infty$ stability of `normDFT1D` (`vecInfNorm_normDFT1D_le`) and `normDFT2D`
     (`matInfNorm_normDFT2D_le`).
   - 1D inverse DFT reconstruction identities (`sum_normDFT1D_mul_expNegTwoPiI`,
     `conj_normDFT1D_conj_eq`).
   - Two-call real convolution and conjugate-symmetry extraction identities
     (Section 3.5 (`sec:prelim-dft`), Lemma 3.4 (`lem:two-call`)).

2. **Negacyclic Polynomial Ring $\mathcal{R}_r = \mathbb{C}[y]/(y^r + 1)$ and Evaluation Homomorphism (Section 3.5 (`sec:prelim-dft`), Section 4.1 (`sec:twisted`))**:
   - `NegacyclicPoly r`, `negacyclicShift`, `negacyclicMul`.
   - Odd-root evaluation functionals `evalZetaOdd`, `phiOddRoot` ($\zeta^{2u_2 - 1}$), and
     `evalOddRoot` ($\zeta^{-(2u_2 + 1)}$).
   - Linearity, multiplicativity, and root twist theorems.

3. **Proposition 4.1 (`thm:twisted`): Polynomial-Transform Reduction (Nussbaumer–Quandalle, Section 4.1 (`sec:twisted`))**:
   - Reduction of `normDFT2D` and odd-twisted 1D DFTs to `t1` calls to `normDFT1D` via
     `preTwist`, `syntheticFFT`, `postTwist`, and the odd-stride permutation `oddStrideIndex`
     (with bijectivity `oddStrideIndex_bijective` when $t_1 = 2^{k_1}$).

4. **Lemma 3.5 (`lem:syn-fft`): Exactness and Stability of the Radix-2 Polynomial Transform & Quantized Twist Roots (Section 3.5 (`sec:prelim-dft`), Section 6.3 (`sec:forward-error`))**:
   - Recursive $k_1$-stage radix-2 Cooley–Tukey butterfly network over $\mathcal{R}_r$ in both
     exact arithmetic and quantized fixed-point arithmetic at precision $q = p_{\ell+1} + 2$.
   - Proof that the exact butterfly network computes the polynomial transform (`syntheticFFT`) and
     that the quantized butterfly network accumulates $\ell_\infty$ error at most
     $k_1 \frac{\sqrt{2}}{4} 2^{-p_{\ell+1}} \le 0.18 K_\ell 2^{-p_{\ell+1}}$
     (equation (13) (`eq:syn-err`), Table 3 (`tab:lean-map`)).
   - Quantized twist roots `zetaPowQuant`, `preTwistQuantRoots`, and `postTwistQuantRoots`
     and their matrix $\ell_\infty$ error bounds `matInfNorm_preTwistQuantRoots_sub_preTwistExact_le`
     and `matInfNorm_postTwistQuantRoots_sub_postTwistExact_le`.

5. **Subring Decomposition & Restricted-Model Barrier Identities (`## 7`, omitted from the published paper)**:
   - Coset subring decomposition of radix-$B$ polynomial-transform butterflies over $\mathcal{R}_r$
     (`radixBSyntheticButterfly_coset_decomposition`, `radixB_interStage_twiddle_ops_le`) and
     restricted-model barrier identities (`abs_decoupledSubringOperatorInt_le`,
     `decoupledSubringOperatorInt_const_zero`, `bitSlice_output_exceeds_slice_width`,
     `bitSliceAccumulationOps_decomp`, `floyd_transpose_step_lower_bound`,
     `kronecker_conv_ops_gt_addition_butterfly`, `chunk_telescoping_conservation_lower_bound`,
     `negacyclicShift_order_two_mul_r`, `butterfly_stage_sum_telescoping_invariance`,
     `root_working_precision_gt_two_mul_rootK0`, `swar_packed_bit_ops_conservation`) retained from
     the restricted-model section of an earlier draft.
-/

namespace IntMul

open scoped BigOperators ComplexConjugate

/-! ## 1. Unit-Modulus & Algebraic Properties of `expTwoPiI`, `expNegTwoPiI`, and `zetaPow` -/

/-- `expNegTwoPiI x` equals `expTwoPiI (-x)`. -/
theorem expNegTwoPiI_eq_expTwoPiI_neg (x : ℝ) :
    expNegTwoPiI x = expTwoPiI (-x) := by
  simp only [expNegTwoPiI, expTwoPiI]
  congr 1
  push_cast
  ring

/-- `expTwoPiI x` equals `expNegTwoPiI (-x)`. -/
theorem expTwoPiI_eq_expNegTwoPiI_neg (x : ℝ) :
    expTwoPiI x = expNegTwoPiI (-x) := by
  rw [expNegTwoPiI_eq_expTwoPiI_neg, neg_neg]

/-- Unit modulus of $e^{2\pi i x}$ for $x \in \mathbb{R}$. -/
@[simp]
theorem norm_expTwoPiI (x : ℝ) : ‖expTwoPiI x‖ = 1 := by
  unfold expTwoPiI
  have h : (2 : ℂ) * ↑Real.pi * ↑x * Complex.I = ↑(2 * Real.pi * x) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

/-- Unit modulus of $e^{-2\pi i x}$ for $x \in \mathbb{R}$. -/
@[simp]
theorem norm_expNegTwoPiI (x : ℝ) : ‖expNegTwoPiI x‖ = 1 := by
  rw [expNegTwoPiI_eq_expTwoPiI_neg, norm_expTwoPiI]

/-- Unit modulus of $\zeta^m = e^{\pi i m / r}$ for $r \in \mathbb{N}$ and $m \in \mathbb{Z}$. -/
@[simp]
theorem norm_zetaPow (r : ℕ) (m : ℤ) : ‖zetaPow r m‖ = 1 := by
  unfold zetaPow
  have h : (↑Real.pi : ℂ) * ↑(m : ℝ) / ↑(r : ℝ) * Complex.I =
      ↑(Real.pi * (m : ℝ) / (r : ℝ)) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I (Real.pi * (m : ℝ) / (r : ℝ))

@[simp]
theorem expTwoPiI_zero : expTwoPiI 0 = 1 := by
  unfold expTwoPiI
  simp

@[simp]
theorem expNegTwoPiI_zero : expNegTwoPiI 0 = 1 := by
  unfold expNegTwoPiI
  simp

theorem expTwoPiI_add (x y : ℝ) :
    expTwoPiI (x + y) = expTwoPiI x * expTwoPiI y := by
  unfold expTwoPiI
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expNegTwoPiI_add (x y : ℝ) :
    expNegTwoPiI (x + y) = expNegTwoPiI x * expNegTwoPiI y := by
  unfold expNegTwoPiI
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expTwoPiI_sub (x y : ℝ) :
    expTwoPiI (x - y) = expTwoPiI x * expNegTwoPiI y := by
  rw [sub_eq_add_neg, expTwoPiI_add, ← expNegTwoPiI_eq_expTwoPiI_neg]

theorem expTwoPiI_mul_expNegTwoPiI (x : ℝ) :
    expTwoPiI x * expNegTwoPiI x = 1 := by
  rw [expNegTwoPiI_eq_expTwoPiI_neg, ← expTwoPiI_add, add_neg_cancel, expTwoPiI_zero]

theorem expNegTwoPiI_mul_expTwoPiI (x : ℝ) :
    expNegTwoPiI x * expTwoPiI x = 1 := by
  rw [mul_comm, expTwoPiI_mul_expNegTwoPiI]

theorem expTwoPiI_nat_mul (x : ℝ) (n : ℕ) :
    expTwoPiI ((n : ℝ) * x) = (expTwoPiI x) ^ n := by
  unfold expTwoPiI
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem expTwoPiI_int (m : ℤ) : expTwoPiI (m : ℝ) = 1 := by
  unfold expTwoPiI
  have h : (2 : ℂ) * ↑Real.pi * ↑(m : ℝ) * Complex.I =
      (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I m

theorem expNegTwoPiI_int (m : ℤ) : expNegTwoPiI (m : ℝ) = 1 := by
  rw [expNegTwoPiI_eq_expTwoPiI_neg]
  exact_mod_cast expTwoPiI_int (-m)

theorem expTwoPiI_add_int (x : ℝ) (m : ℤ) :
    expTwoPiI (x + (m : ℝ)) = expTwoPiI x := by
  rw [expTwoPiI_add, expTwoPiI_int, mul_one]

theorem expNegTwoPiI_add_int (x : ℝ) (m : ℤ) :
    expNegTwoPiI (x + (m : ℝ)) = expNegTwoPiI x := by
  rw [expNegTwoPiI_add, expNegTwoPiI_int, mul_one]

theorem conj_expTwoPiI (x : ℝ) :
    conj (expTwoPiI x) = expNegTwoPiI x := by
  unfold expTwoPiI expNegTwoPiI
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem conj_expNegTwoPiI (x : ℝ) :
    conj (expNegTwoPiI x) = expTwoPiI x := by
  rw [← conj_expTwoPiI, RingHomCompTriple.comp_apply, RingHom.id_apply]

@[simp]
theorem zetaPow_zero (r : ℕ) : zetaPow r 0 = 1 := by
  unfold zetaPow
  simp

theorem zetaPow_add (r : ℕ) (m n : ℤ) :
    zetaPow r (m + n) = zetaPow r m * zetaPow r n := by
  unfold zetaPow
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zetaPow_sub (r : ℕ) (m n : ℤ) :
    zetaPow r (m - n) = zetaPow r m * zetaPow r (-n) := by
  rw [sub_eq_add_neg, zetaPow_add]

theorem zetaPow_mul_neg (r : ℕ) (m : ℤ) :
    zetaPow r m * zetaPow r (-m) = 1 := by
  rw [← zetaPow_add, add_neg_cancel, zetaPow_zero]

theorem zetaPow_int_mul (r : ℕ) (m k : ℤ) :
    zetaPow r (m * k) = (zetaPow r m) ^ k := by
  unfold zetaPow
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem conj_zetaPow (r : ℕ) (m : ℤ) :
    conj (zetaPow r m) = zetaPow r (-m) := by
  unfold zetaPow
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_div₀, map_intCast, map_natCast, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem zetaPow_two_mul (r : ℕ) (m : ℤ) :
    zetaPow r (2 * m) = expTwoPiI ((m : ℝ) / (r : ℝ)) := by
  unfold zetaPow expTwoPiI
  congr 1
  push_cast
  ring

theorem zetaPow_neg_two_mul (r : ℕ) (m : ℤ) :
    zetaPow r (-2 * m) = expNegTwoPiI ((m : ℝ) / (r : ℝ)) := by
  unfold zetaPow expNegTwoPiI
  congr 1
  push_cast
  ring

/-- $\zeta^r = e^{\pi i} = -1$ for $r > 0$. -/
theorem zetaPow_self {r : ℕ} (hr : 0 < r) : zetaPow r (r : ℤ) = -1 := by
  unfold zetaPow
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ( ne_of_gt hr )
  have h : (↑Real.pi : ℂ) * ↑((r : ℤ) : ℝ) / ↑(r : ℝ) * Complex.I =
      ↑Real.pi * Complex.I := by
    push_cast
    rw [mul_div_cancel_right₀ _ hr_ne]
  rw [h, Complex.exp_pi_mul_I]

/-- $\zeta^{2r} = 1$ for $r > 0$. -/
theorem zetaPow_two_mul_self {r : ℕ} (hr : 0 < r) : zetaPow r (2 * (r : ℤ)) = 1 := by
  have h : (2 : ℤ) * (r : ℤ) = (r : ℤ) + (r : ℤ) := by ring
  rw [h, zetaPow_add, zetaPow_self hr]
  ring

/-- For any odd integer $m$ and $r > 0$, $\zeta^{m r} = -1$. -/
theorem zetaPow_odd_mul_self {r : ℕ} (hr : 0 < r) {m : ℤ} (hm : Odd m) :
    zetaPow r (m * (r : ℤ)) = -1 := by
  rcases hm with ⟨k, rfl⟩
  have h : (2 * k + 1) * (r : ℤ) = (r : ℤ) * (2 * k + 1) := by ring
  rw [h, zetaPow_int_mul, zetaPow_self hr]
  rw [zpow_add₀ (by norm_num), zpow_one, zpow_mul]
  norm_num

/-! ## 2. Vector/Matrix $\ell_\infty$ Norms & Normalized 1D/2D DFT Stability (Section 3.1 (`sec:notation`), Section 3.5 (`sec:prelim-dft`)) -/

/-- Non-negativity of `vecInfNorm`. -/
theorem vecInfNorm_nonneg {R : ℕ} (x : Fin R → ℂ) : 0 ≤ vecInfNorm x := by
  unfold vecInfNorm
  exact NNReal.coe_nonneg _

/-- Every coordinate modulus is bounded by `vecInfNorm`. -/
theorem norm_le_vecInfNorm {R : ℕ} (x : Fin R → ℂ) (u : Fin R) :
    ‖x u‖ ≤ vecInfNorm x := by
  unfold vecInfNorm
  exact_mod_cast Finset.le_sup (f := fun v : Fin R => ‖x v‖₊) (Finset.mem_univ u)

/-- Characterization of upper bounds on `vecInfNorm`. -/
theorem vecInfNorm_le_iff {R : ℕ} (x : Fin R → ℂ) {B : ℝ} (hB : 0 ≤ B) :
    vecInfNorm x ≤ B ↔ ∀ u : Fin R, ‖x u‖ ≤ B := by
  unfold vecInfNorm
  lift B to NNReal using hB
  rw [NNReal.coe_le_coe, Finset.sup_le_iff]
  simp [← NNReal.coe_le_coe]

/-- Upper bound introduction rule for `vecInfNorm`. -/
theorem vecInfNorm_le {R : ℕ} (x : Fin R → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ u : Fin R, ‖x u‖ ≤ B) : vecInfNorm x ≤ B :=
  (vecInfNorm_le_iff x hB).mpr h

/-- Triangle inequality for `vecInfNorm`. -/
theorem vecInfNorm_add_le {R : ℕ} (x y : Fin R → ℂ) :
    vecInfNorm (fun u => x u + y u) ≤ vecInfNorm x + vecInfNorm y := by
  apply vecInfNorm_le _ (add_nonneg (vecInfNorm_nonneg x) (vecInfNorm_nonneg y))
  intro u
  exact (norm_add_le (x u) (y u)).trans
    (add_le_add (norm_le_vecInfNorm x u) (norm_le_vecInfNorm y u))

/-- Subtraction triangle inequality for `vecInfNorm`. -/
theorem vecInfNorm_sub_le {R : ℕ} (x y z : Fin R → ℂ) :
    vecInfNorm (fun u => x u - z u) ≤
      vecInfNorm (fun u => x u - y u) + vecInfNorm (fun u => y u - z u) := by
  apply vecInfNorm_le _ (add_nonneg (vecInfNorm_nonneg _) (vecInfNorm_nonneg _))
  intro u
  calc
    ‖x u - z u‖ = ‖(x u - y u) + (y u - z u)‖ := by ring_nf
    _ ≤ ‖x u - y u‖ + ‖y u - z u‖ := norm_add_le _ _
    _ ≤ vecInfNorm (fun v => x v - y v) + vecInfNorm (fun v => y v - z v) :=
      add_le_add (norm_le_vecInfNorm (fun v => x v - y v) u)
        (norm_le_vecInfNorm (fun v => y v - z v) u)

/-- Non-negativity of `matInfNorm`. -/
theorem matInfNorm_nonneg {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) : 0 ≤ matInfNorm U := by
  unfold matInfNorm
  exact NNReal.coe_nonneg _

/-- Every matrix entry modulus is bounded by `matInfNorm`. -/
theorem norm_le_matInfNorm {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) (j1 : Fin t1) (j2 : Fin r) :
    ‖U j1 j2‖ ≤ matInfNorm U := by
  unfold matInfNorm
  exact_mod_cast Finset.le_sup (f := fun p : Fin t1 × Fin r => ‖U p.1 p.2‖₊)
    (Finset.mem_univ (j1, j2))

/-- Characterization of upper bounds on `matInfNorm`. -/
theorem matInfNorm_le_iff {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) {B : ℝ} (hB : 0 ≤ B) :
    matInfNorm U ≤ B ↔ ∀ (j1 : Fin t1) (j2 : Fin r), ‖U j1 j2‖ ≤ B := by
  unfold matInfNorm
  lift B to NNReal using hB
  rw [NNReal.coe_le_coe, Finset.sup_le_iff]
  constructor
  · intro h j1 j2
    exact_mod_cast h (j1, j2) (Finset.mem_univ (j1, j2))
  · intro h p _
    exact_mod_cast h p.1 p.2

/-- Upper bound introduction rule for `matInfNorm`. -/
theorem matInfNorm_le {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (j1 : Fin t1) (j2 : Fin r), ‖U j1 j2‖ ≤ B) : matInfNorm U ≤ B :=
  (matInfNorm_le_iff U hB).mpr h

/-- Pointwise bound on the normalized 1D DFT: `‖(F_R x)_u‖ ≤ vecInfNorm x`. -/
theorem norm_normDFT1D_le {R : ℕ} (x : Fin R → ℂ) (u : Fin R) :
    ‖normDFT1D x u‖ ≤ vecInfNorm x := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact Fin.elim0 u
  · unfold normDFT1D
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg R)]
    calc
      (R : ℝ)⁻¹ * ‖∑ j : Fin R, x j * expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ))‖
        ≤ (R : ℝ)⁻¹ * ∑ j : Fin R, ‖x j * expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ))‖ := by
          gcongr
          exact norm_sum_le _ _
      _ = (R : ℝ)⁻¹ * ∑ j : Fin R, ‖x j‖ := by
          congr 1
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [norm_mul, norm_expTwoPiI, mul_one]
      _ ≤ (R : ℝ)⁻¹ * ∑ _j : Fin R, vecInfNorm x := by
          gcongr with j _
          exact norm_le_vecInfNorm x j
      _ = vecInfNorm x := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hR_ne : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hR)
          rw [← mul_assoc, inv_mul_cancel₀ hR_ne, one_mul]

/-- Normalized 1D DFT $\ell_\infty$ stability: $\|F_R x\|_\infty \le \|x\|_\infty$ (Section 3.5 (`sec:prelim-dft`)). -/
theorem vecInfNorm_normDFT1D_le {R : ℕ} (x : Fin R → ℂ) :
    vecInfNorm (normDFT1D x) ≤ vecInfNorm x :=
  vecInfNorm_le (normDFT1D x) (vecInfNorm_nonneg x) (norm_normDFT1D_le x)

/-- Pointwise bound on the normalized 2D DFT: `‖(F_{t1, r} U)_{u1, u2}‖ ≤ matInfNorm U`. -/
theorem norm_normDFT2D_le {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) (u1 : Fin t1) (u2 : Fin r) :
    ‖normDFT2D U u1 u2‖ ≤ matInfNorm U := by
  rcases Nat.eq_zero_or_pos t1 with rfl | ht1
  · exact Fin.elim0 u1
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact Fin.elim0 u2
    · unfold normDFT2D
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg (t1 * r))]
      calc
        ((t1 * r : ℕ) : ℝ)⁻¹ *
            ‖∑ j1 : Fin t1, ∑ j2 : Fin r,
              U j1 j2 * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) *
                expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))‖
          ≤ ((t1 * r : ℕ) : ℝ)⁻¹ *
              ∑ j1 : Fin t1, ∑ j2 : Fin r,
                ‖U j1 j2 * expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) *
                  expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))‖ := by
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j1 _ => norm_sum_le _ _))
        _ = ((t1 * r : ℕ) : ℝ)⁻¹ * ∑ j1 : Fin t1, ∑ j2 : Fin r, ‖U j1 j2‖ := by
            congr 1
            refine Finset.sum_congr rfl (fun j1 _ => Finset.sum_congr rfl (fun j2 _ => ?_))
            rw [norm_mul, norm_mul, norm_expTwoPiI, norm_expTwoPiI, mul_one, mul_one]
        _ ≤ ((t1 * r : ℕ) : ℝ)⁻¹ * ∑ _j1 : Fin t1, ∑ _j2 : Fin r, matInfNorm U := by
            gcongr with j1 _ j2 _
            exact norm_le_matInfNorm U j1 j2
        _ = matInfNorm U := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.cast_mul]
            have ht1_ne : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ht1)
            have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hr)
            have htr_ne : (t1 : ℝ) * (r : ℝ) ≠ 0 := mul_ne_zero ht1_ne hr_ne
            calc
              ((t1 : ℝ) * (r : ℝ))⁻¹ * ((t1 : ℝ) * ((r : ℝ) * matInfNorm U))
                = (((t1 : ℝ) * (r : ℝ))⁻¹ * ((t1 : ℝ) * (r : ℝ))) * matInfNorm U := by ring
              _ = matInfNorm U := by rw [inv_mul_cancel₀ htr_ne, one_mul]

/-- Normalized 2D DFT $\ell_\infty$ stability: $\|F_{t_1, r} U\|_\infty \le \|U\|_\infty$ (Section 3.5 (`sec:prelim-dft`)). -/
theorem matInfNorm_normDFT2D_le {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) :
    matInfNorm (normDFT2D U) ≤ matInfNorm U :=
  matInfNorm_le (normDFT2D U) (matInfNorm_nonneg U) (norm_normDFT2D_le U)

/-- Linearity of `normDFT1D` under vector addition. -/
theorem normDFT1D_add {R : ℕ} (x y : Fin R → ℂ) (u : Fin R) :
    normDFT1D (fun j => x j + y j) u = normDFT1D x u + normDFT1D y u := by
  unfold normDFT1D
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Linearity of `normDFT1D` under vector subtraction. -/
theorem normDFT1D_sub {R : ℕ} (x y : Fin R → ℂ) (u : Fin R) :
    normDFT1D (fun j => x j - y j) u = normDFT1D x u - normDFT1D y u := by
  unfold normDFT1D
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Linearity of `normDFT1D` under scalar multiplication. -/
theorem normDFT1D_smul {R : ℕ} (c : ℂ) (x : Fin R → ℂ) (u : Fin R) :
    normDFT1D (fun j => c * x j) u = c * normDFT1D x u := by
  unfold normDFT1D
  have h : ∑ j : Fin R, c * x j * expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ)) =
      c * ∑ j : Fin R, x j * expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h]
  ring

/-! ## 3. 1D Inverse DFT Reconstruction & 2-Call Real Convolution (Section 3.5 (`sec:prelim-dft`), Lemma 3.4 (`lem:two-call`)) -/

/-- If $0 < |d| < R$, then $e^{2\pi i d / R} \ne 1$. -/
theorem expTwoPiI_div_ne_one {R : ℕ} {d : ℤ} (hd0 : d ≠ 0) (hdR : |d| < (R : ℤ)) :
    expTwoPiI ((d : ℝ) / (R : ℝ)) ≠ 1 := by
  have hR_pos : (0 : ℤ) < (R : ℤ) := (abs_nonneg d).trans_lt hdR
  have hR_real_pos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR_pos
  unfold expTwoPiI
  rw [ Ne, Complex.exp_eq_one_iff ]
  rintro ⟨m, hm⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hm' : (d : ℂ) / (R : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ hI
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hpi)
    calc
      (2 : ℂ) * ↑Real.pi * ((d : ℂ) / (R : ℂ) * Complex.I)
        = 2 * ↑Real.pi * ↑((d : ℝ) / (R : ℝ)) * Complex.I := by push_cast; ring
      _ = ↑m * (2 * ↑Real.pi * Complex.I) := hm
      _ = (2 : ℂ) * ↑Real.pi * ((m : ℂ) * Complex.I) := by ring
  have hm_real : (d : ℝ) / (R : ℝ) = (m : ℝ) := by exact_mod_cast hm'
  have hdm : (d : ℝ) = (m : ℝ) * (R : ℝ) :=
    (div_eq_iff (ne_of_gt hR_real_pos)).mp hm_real
  have hdm_int : d = m * (R : ℤ) := by exact_mod_cast hdm
  have hm_ne : m ≠ 0 := by
    rintro rfl
    simp only [zero_mul] at hdm_int
    exact hd0 hdm_int
  have h_abs : (R : ℤ) ≤ |d| := by
    rw [hdm_int, abs_mul, abs_of_pos hR_pos]
    exact le_mul_of_one_le_left (le_of_lt hR_pos) (Int.one_le_abs hm_ne)
  exact not_lt_of_ge h_abs hdR

/-- Discrete orthogonality of roots of unity over `Fin R`. -/
theorem sum_expTwoPiI_sub_div {R : ℕ} (j k : Fin R) :
    ∑ u : Fin R,
      expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ)) *
        expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ)) =
      if j = k then (R : ℂ) else 0 := by
  have h_term : ∀ u : Fin R,
      expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ)) *
        expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ)) =
      (expTwoPiI (((j.val : ℝ) - (k.val : ℝ)) / (R : ℝ))) ^ u.val := by
    intro u
    rw [← expTwoPiI_sub, ← expTwoPiI_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [h_term]
  split_ifs with hjk
  · subst hjk
    simp [expTwoPiI_zero]
  · rw [Fin.sum_univ_eq_sum_range
      (fun u : ℕ => (expTwoPiI (((j.val : ℝ) - (k.val : ℝ)) / (R : ℝ))) ^ u) R]
    set d : ℤ := (j.val : ℤ) - (k.val : ℤ)
    have hd_real : (j.val : ℝ) - (k.val : ℝ) = (d : ℝ) := by
      simp [d]
    rw [hd_real]
    have hd0 : d ≠ 0 := by
      intro h0
      apply hjk
      ext
      omega
    have hdR : |d| < (R : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have h_ne : expTwoPiI ((d : ℝ) / (R : ℝ)) ≠ 1 := expTwoPiI_div_ne_one hd0 hdR
    rw [geom_sum_eq h_ne, ← expTwoPiI_nat_mul]
    have hR_ne : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [mul_div_cancel₀ _ hR_ne, expTwoPiI_int d, sub_self, zero_div]

/-- **1D Inverse DFT Reconstruction Identity** (using `expNegTwoPiI`):
$$\sum_{u : \text{Fin } R} (F_R x)_u e^{-2\pi i u k / R} = x_k.$$ -/
theorem sum_normDFT1D_mul_expNegTwoPiI {R : ℕ} (x : Fin R → ℂ) (k : Fin R) :
    ∑ u : Fin R,
      normDFT1D x u * expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ)) = x k := by
  have hR_pos : 0 < R := k.pos
  have hR_ne : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hR_pos)
  unfold normDFT1D
  simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h_inner : ∀ j : Fin R,
      ∑ u : Fin R,
        (x j * expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ))) *
          expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ)) =
      x j * if j = k then (R : ℂ) else 0 := by
    intro j
    rw [← sum_expTwoPiI_sub_div j k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    ring
  simp_rw [h_inner, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  push_cast
  calc
    (R : ℂ)⁻¹ * (x k * (R : ℂ)) = ((R : ℂ)⁻¹ * (R : ℂ)) * x k := by ring
    _ = x k := by rw [inv_mul_cancel₀ hR_ne, one_mul]

/-- **1D Inverse DFT Reconstruction via Conjugate Symmetry** (Section 3.5 (`sec:prelim-dft`)):
$$R \cdot \overline{\bigl(F_R \, \overline{F_R x}\bigr)_k} = x_k.$$ -/
theorem conj_normDFT1D_conj_eq {R : ℕ} (x : Fin R → ℂ) (k : Fin R) :
    (R : ℂ) * conj (normDFT1D (fun u => conj (normDFT1D x u)) k) = x k := by
  have hR_pos : 0 < R := k.pos
  have hR_ne : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hR_pos)
  rw [← sum_normDFT1D_mul_expNegTwoPiI x k]
  unfold normDFT1D
  rw [map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ hR_ne, one_mul]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, conj_expTwoPiI]

/-- Modular negation `(-u) mod R` on `Fin R` (Section 3.5 (`sec:prelim-dft`)). -/
def negModFin {R : ℕ} (u : Fin R) : Fin R :=
  ⟨(R - u.val) % R, Nat.mod_lt _ u.pos⟩

@[simp]
theorem negModFin_negModFin {R : ℕ} (u : Fin R) :
    negModFin (negModFin u) = u := by
  ext
  simp only [negModFin]
  rcases Nat.eq_zero_or_pos u.val with hu | hu
  · simp [hu]
  · have hlt : R - u.val < R := Nat.sub_lt u.pos hu
    rw [Nat.mod_eq_of_lt hlt, Nat.sub_sub_self (le_of_lt u.isLt), Nat.mod_eq_of_lt u.isLt]

/-- Phase identity for `negModFin`:
`expNegTwoPiI (j * ((R - u) % R) / R) = expTwoPiI (j * u / R)`. -/
theorem expNegTwoPiI_negModFin {R : ℕ} (j u : Fin R) :
    expNegTwoPiI (((j.val * (negModFin u).val : ℕ) : ℝ) / (R : ℝ)) =
      expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ)) := by
  have hR_pos : 0 < R := u.pos
  have hR_ne : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hR_pos)
  unfold negModFin
  dsimp
  rcases Nat.eq_zero_or_pos u.val with hu | hu
  · simp [hu]
  · have hlt : R - u.val < R := Nat.sub_lt hR_pos hu
    rw [Nat.mod_eq_of_lt hlt]
    rw [expNegTwoPiI_eq_expTwoPiI_neg]
    have h_split :
        -(((j.val * (R - u.val) : ℕ) : ℝ) / (R : ℝ)) =
          (((j.val * u.val : ℕ) : ℝ) / (R : ℝ)) + ((-(j.val : ℤ) : ℤ) : ℝ) := by
      push_cast [Nat.cast_sub (le_of_lt u.isLt)]
      field_simp [hR_ne]
      ring
    rw [h_split, expTwoPiI_add_int]

/-- **1D Inverse DFT Sum with Positive Exponential**:
$$\sum_{u : \text{Fin } R} (F_R x)_u e^{2\pi i u k / R} = x_{(-k) \bmod R}.$$ -/
theorem sum_normDFT1D_mul_expTwoPiI {R : ℕ} (x : Fin R → ℂ) (k : Fin R) :
    ∑ u : Fin R,
      normDFT1D x u * expTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ)) =
      x (negModFin k) := by
  rw [← sum_normDFT1D_mul_expNegTwoPiI x (negModFin k)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  congr 1
  exact (expNegTwoPiI_negModFin u k).symm

/-- Conjugate symmetry of `normDFT1D` on a real input vector $a : \text{Fin } R \to \mathbb{R}$:
$$\overline{(F_R a)_{(-u) \bmod R}} = (F_R a)_u.$$ -/
theorem conj_normDFT1D_real_negModFin {R : ℕ} (a : Fin R → ℝ) (u : Fin R) :
    conj (normDFT1D (fun j => (a j : ℂ)) (negModFin u)) =
      normDFT1D (fun j => (a j : ℂ)) u := by
  unfold normDFT1D
  rw [map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, Complex.conj_ofReal, conj_expTwoPiI, expNegTwoPiI_negModFin]

/-- Real-input packing $z_k = a_k + i b_k$ (Section 3.5 (`sec:prelim-dft`), Lemma 3.4 (`lem:two-call`)). -/
def packRealComplex {R : ℕ} (a b : Fin R → ℝ) (k : Fin R) : ℂ :=
  (a k : ℂ) + (b k : ℂ) * Complex.I

/-- Conjugate-symmetry extraction of the first real DFT $X_u = \frac{Z_u + \overline{Z_{(-u) \bmod R}}}{2}$ (Section 3.5 (`sec:prelim-dft`)). -/
noncomputable def extractRealDFT_X {R : ℕ} (Z : Fin R → ℂ) (u : Fin R) : ℂ :=
  (Z u + conj (Z (negModFin u))) / 2

/-- Conjugate-symmetry extraction of the second real DFT $Y_u = \frac{Z_u - \overline{Z_{(-u) \bmod R}}}{2i}$ (Section 3.5 (`sec:prelim-dft`)). -/
noncomputable def extractRealDFT_Y {R : ℕ} (Z : Fin R → ℂ) (u : Fin R) : ℂ :=
  (Z u - conj (Z (negModFin u))) / (2 * Complex.I)

/-- Linearity of `normDFT1D` on `packRealComplex a b`. -/
theorem normDFT1D_packRealComplex {R : ℕ} (a b : Fin R → ℝ) (u : Fin R) :
    normDFT1D (packRealComplex a b) u =
      normDFT1D (fun j => (a j : ℂ)) u + Complex.I * normDFT1D (fun j => (b j : ℂ)) u := by
  unfold packRealComplex
  have h : (fun j : Fin R => (a j : ℂ) + (b j : ℂ) * Complex.I) =
      (fun j : Fin R => (a j : ℂ) + Complex.I * (b j : ℂ)) := by
    funext j; ring
  rw [h, normDFT1D_add, normDFT1D_smul]

/-- **2-Call Real Convolution Extraction Identity for $a$** (Section 3.5 (`sec:prelim-dft`), Lemma 3.4 (`lem:two-call`)):
$$X_u = \frac{Z_u + \overline{Z_{(-u) \bmod R}}}{2} = (F_R a)_u.$$ -/
theorem extractRealDFT_X_eq {R : ℕ} (a b : Fin R → ℝ) (u : Fin R) :
    extractRealDFT_X (normDFT1D (packRealComplex a b)) u =
      normDFT1D (fun j => (a j : ℂ)) u := by
  unfold extractRealDFT_X
  rw [normDFT1D_packRealComplex, normDFT1D_packRealComplex]
  rw [map_add, map_mul, Complex.conj_I, conj_normDFT1D_real_negModFin,
    conj_normDFT1D_real_negModFin]
  ring

/-- **2-Call Real Convolution Extraction Identity for $b$** (Section 3.5 (`sec:prelim-dft`), Lemma 3.4 (`lem:two-call`)):
$$Y_u = \frac{Z_u - \overline{Z_{(-u) \bmod R}}}{2i} = (F_R b)_u.$$ -/
theorem extractRealDFT_Y_eq {R : ℕ} (a b : Fin R → ℝ) (u : Fin R) :
    extractRealDFT_Y (normDFT1D (packRealComplex a b)) u =
      normDFT1D (fun j => (b j : ℂ)) u := by
  unfold extractRealDFT_Y
  rw [normDFT1D_packRealComplex, normDFT1D_packRealComplex]
  rw [map_add, map_mul, Complex.conj_I, conj_normDFT1D_real_negModFin,
    conj_normDFT1D_real_negModFin]
  have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  apply mul_right_cancel₀ hI
  rw [div_mul_cancel₀ _ hI]
  ring

/-- **2-Call Packed Square Identity** (Section 3.5 (`sec:prelim-dft`), Lemma 3.4 (`lem:two-call`), equation (10) (`eq:two-call`)):
$$(F_R(a + i b))_u^2 = (F_R a)_u^2 - (F_R b)_u^2 + 2i (F_R a)_u (F_R b)_u.$$ -/
theorem normDFT1D_packRealComplex_sq {R : ℕ} (a b : Fin R → ℝ) (u : Fin R) :
    (normDFT1D (packRealComplex a b) u) ^ 2 =
      (normDFT1D (fun j => (a j : ℂ)) u) ^ 2 -
        (normDFT1D (fun j => (b j : ℂ)) u) ^ 2 +
        2 * Complex.I * normDFT1D (fun j => (a j : ℂ)) u *
          normDFT1D (fun j => (b j : ℂ)) u := by
  rw [normDFT1D_packRealComplex]
  calc
    (normDFT1D (fun j => (a j : ℂ)) u + Complex.I * normDFT1D (fun j => (b j : ℂ)) u) ^ 2
      = (normDFT1D (fun j => (a j : ℂ)) u) ^ 2 +
          Complex.I ^ 2 * (normDFT1D (fun j => (b j : ℂ)) u) ^ 2 +
          2 * Complex.I * normDFT1D (fun j => (a j : ℂ)) u *
            normDFT1D (fun j => (b j : ℂ)) u := by ring
    _ = (normDFT1D (fun j => (a j : ℂ)) u) ^ 2 -
          (normDFT1D (fun j => (b j : ℂ)) u) ^ 2 +
          2 * Complex.I * normDFT1D (fun j => (a j : ℂ)) u *
            normDFT1D (fun j => (b j : ℂ)) u := by
        rw [Complex.I_sq]
        ring

/-! ## 4. Negacyclic Polynomial Ring $\mathcal{R}_r = \mathbb{C}[y]/(y^r + 1)$ and Evaluation Homomorphism (Section 3.5 (`sec:prelim-dft`), Section 4.1 (`sec:twisted`)) -/

/-- Elements of the negacyclic quotient ring $\mathcal{R}_r = \mathbb{C}[y]/(y^r + 1)$ represented
by their degree-$< r$ coefficient vector `Fin r → ℂ` (Section 3.5 (`sec:prelim-dft`)). -/
abbrev NegacyclicPoly (r : ℕ) : Type := Fin r → ℂ

/-- Addition in $\mathcal{R}_r$. -/
def negacyclicAdd {r : ℕ} (P Q : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => P k2 + Q k2

/-- Subtraction in $\mathcal{R}_r$. -/
def negacyclicSub {r : ℕ} (P Q : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => P k2 - Q k2

/-- Scalar multiplication in $\mathcal{R}_r$. -/
def negacyclicSmul {r : ℕ} (c : ℂ) (P : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => c * P k2

/-- Source coefficient index `(k2 - s) mod r` in `Fin r` for a negacyclic monomial shift by $y^s$. -/
def shiftModFin {r : ℕ} (s : ℤ) (k2 : Fin r) : Fin r :=
  ⟨(((k2.val : ℤ) - s) % (r : ℤ)).toNat, by
    have hr : (0 : ℤ) < (r : ℤ) := Nat.cast_pos.mpr k2.pos
    have h0 : 0 ≤ ((k2.val : ℤ) - s) % (r : ℤ) := Int.emod_nonneg _ (ne_of_gt hr)
    have hlt : ((k2.val : ℤ) - s) % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos _ hr
    omega⟩

/-- Integer value of `shiftModFin s k2`. -/
@[simp]
theorem coe_shiftModFin {r : ℕ} (s : ℤ) (k2 : Fin r) :
    ((shiftModFin s k2).val : ℤ) = ((k2.val : ℤ) - s) % (r : ℤ) := by
  unfold shiftModFin
  dsimp
  have hr : (0 : ℤ) < (r : ℤ) := Nat.cast_pos.mpr k2.pos
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hr))

/-- Composition law for `shiftModFin`. -/
@[simp]
theorem shiftModFin_shiftModFin {r : ℕ} (s1 s2 : ℤ) (k2 : Fin r) :
    shiftModFin s2 (shiftModFin s1 k2) = shiftModFin (s1 + s2) k2 := by
  apply Fin.ext
  rw [ ← Int.ofNat_inj ]
  rw [coe_shiftModFin, coe_shiftModFin, coe_shiftModFin]
  conv_lhs => rw [sub_eq_add_neg, Int.emod_add_emod, ← sub_eq_add_neg, sub_sub]

@[simp]
theorem shiftModFin_zero {r : ℕ} (k2 : Fin r) :
    shiftModFin 0 k2 = k2 := by
  apply Fin.ext
  rw [ ← Int.ofNat_inj, coe_shiftModFin, sub_zero ]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg k2.val) (Int.ofNat_lt.mpr k2.isLt)

/-- Bijection on `Fin r` induced by `shiftModFin s`. -/
def shiftModFinEquiv {r : ℕ} (s : ℤ) : Fin r ≃ Fin r where
  toFun := shiftModFin s
  invFun := shiftModFin (-s)
  left_inv k2 := by simp
  right_inv k2 := by simp

/-- Negacyclic monomial shift multiplying $P(y) \in \mathcal{R}_r$ by $y^s \bmod (y^r + 1)$
(Section 3.5 (`sec:prelim-dft`)). -/
noncomputable def negacyclicShift {r : ℕ} (s : ℤ) (P : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => (-1 : ℂ) ^ (((k2.val : ℤ) - s) / (r : ℤ)) * P (shiftModFin s k2)

/-- Sign characterization of `negacyclicShift`: at degree $k_2$, the coefficient from
source index $(k_2 - s) \bmod r$ is negated iff $(k_2 - s) \bmod (2r) \ge r$. -/
theorem negacyclicShift_eq_ite_mod_two_mul {r : ℕ} (s : ℤ) (P : Fin r → ℂ) (k2 : Fin r) :
    negacyclicShift s P k2 =
      if ((k2.val : ℤ) - s) % (2 * (r : ℤ)) < (r : ℤ) then
        P (shiftModFin s k2)
      else
        - P (shiftModFin s k2) := by
  unfold negacyclicShift
  have hr : (0 : ℤ) < (r : ℤ) := Nat.cast_pos.mpr k2.pos
  set d : ℤ := (k2.val : ℤ) - s
  set q : ℤ := d / (r : ℤ)
  set rem : ℤ := d % (r : ℤ)
  have hd : d = (r : ℤ) * q + rem := (Int.mul_ediv_add_emod d (r : ℤ)).symm
  have hrem0 : 0 ≤ rem := Int.emod_nonneg d (ne_of_gt hr)
  have hrem1 : rem < (r : ℤ) := Int.emod_lt_of_pos d hr
  set qh : ℤ := q / 2
  set qr : ℤ := q % 2
  have hq : q = 2 * qh + qr := (Int.mul_ediv_add_emod q 2).symm
  have hq_mod : qr = 0 ∨ qr = 1 := Int.emod_two_eq_zero_or_one q
  rcases hq_mod with hq0 | hq1
  · have hd2 : d % (2 * (r : ℤ)) = rem := by
      have h1 : d = rem + (2 * (r : ℤ)) * qh := by
        linear_combination hd + (r : ℤ) * hq + (r : ℤ) * hq0
      rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hrem0 (by linarith)]
    have hpow : (-1 : ℂ) ^ q = 1 := by
      rw [hq, hq0, add_zero, zpow_mul]
      norm_num
    rw [hd2, if_pos hrem1, hpow, one_mul]
  · have hd2 : d % (2 * (r : ℤ)) = (r : ℤ) + rem := by
      have h1 : d = ((r : ℤ) + rem) + (2 * (r : ℤ)) * qh := by
        linear_combination hd + (r : ℤ) * hq + (r : ℤ) * hq1
      rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by linarith) (by linarith)]
    have hpow : (-1 : ℂ) ^ q = -1 := by
      rw [hq, hq1, zpow_add₀ (by norm_num), zpow_one, zpow_mul]
      norm_num
    rw [hd2, if_neg (by linarith), hpow, neg_one_mul]

/-- Pointwise modulus of `negacyclicShift s P` equals `‖P (shiftModFin s k2)‖`. -/
@[simp]
theorem norm_negacyclicShift {r : ℕ} (s : ℤ) (P : Fin r → ℂ) (k2 : Fin r) :
    ‖negacyclicShift s P k2‖ = ‖P (shiftModFin s k2)‖ := by
  unfold negacyclicShift
  rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]

/-- `negacyclicShift s` is an $\ell_\infty$ isometry on $\mathcal{R}_r$ (Lemma 3.5 (`lem:syn-fft`)). -/
@[simp]
theorem vecInfNorm_negacyclicShift {r : ℕ} (s : ℤ) (P : Fin r → ℂ) :
    vecInfNorm (negacyclicShift s P) = vecInfNorm P := by
  apply le_antisymm
  · apply vecInfNorm_le _ (vecInfNorm_nonneg P)
    intro k2
    rw [norm_negacyclicShift]
    exact norm_le_vecInfNorm P (shiftModFin s k2)
  · apply vecInfNorm_le _ (vecInfNorm_nonneg (negacyclicShift s P))
    intro j
    have h := norm_le_vecInfNorm (negacyclicShift s P) (shiftModFin (-s) j)
    simpa [norm_negacyclicShift] using h

@[simp]
theorem negacyclicShift_zero {r : ℕ} (P : Fin r → ℂ) :
    negacyclicShift 0 P = P := by
  funext k2
  unfold negacyclicShift
  have hdiv : (k2.val : ℤ) / (r : ℤ) = 0 :=
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg k2.val) (Int.ofNat_lt.mpr k2.isLt)
  simp [hdiv]

theorem negacyclicShift_add_poly {r : ℕ} (s : ℤ) (P Q : Fin r → ℂ) :
    negacyclicShift s (fun k2 => P k2 + Q k2) =
      fun k2 => negacyclicShift s P k2 + negacyclicShift s Q k2 := by
  funext k2
  unfold negacyclicShift
  ring

theorem negacyclicShift_sub_poly {r : ℕ} (s : ℤ) (P Q : Fin r → ℂ) :
    negacyclicShift s (fun k2 => P k2 - Q k2) =
      fun k2 => negacyclicShift s P k2 - negacyclicShift s Q k2 := by
  funext k2
  unfold negacyclicShift
  ring

theorem negacyclicShift_smul_poly {r : ℕ} (s : ℤ) (c : ℂ) (P : Fin r → ℂ) :
    negacyclicShift s (fun k2 => c * P k2) =
      fun k2 => c * negacyclicShift s P k2 := by
  funext k2
  unfold negacyclicShift
  ring

/-- Group action law for `negacyclicShift`: shifting by `s1 + s2` equals shifting by `s2` then `s1`. -/
theorem negacyclicShift_add {r : ℕ} (s1 s2 : ℤ) (P : Fin r → ℂ) :
    negacyclicShift (s1 + s2) P = negacyclicShift s1 (negacyclicShift s2 P) := by
  funext k2
  unfold negacyclicShift
  have hr : (0 : ℤ) < (r : ℤ) := Nat.cast_pos.mpr k2.pos
  set j1 := shiftModFin s1 k2
  set j2 := shiftModFin s2 j1
  have hj2 : shiftModFin (s1 + s2) k2 = j2 := (shiftModFin_shiftModFin s1 s2 k2).symm
  rw [hj2]
  set q1 := ((k2.val : ℤ) - s1) / (r : ℤ)
  set q2 := ((j1.val : ℤ) - s2) / (r : ℤ)
  have h1 : (r : ℤ) * q1 + (j1.val : ℤ) = (k2.val : ℤ) - s1 := by
    rw [coe_shiftModFin]
    exact Int.mul_ediv_add_emod ((k2.val : ℤ) - s1) (r : ℤ)
  have h2 : (r : ℤ) * q2 + (j2.val : ℤ) = (j1.val : ℤ) - s2 := by
    rw [coe_shiftModFin]
    exact Int.mul_ediv_add_emod ((j1.val : ℤ) - s2) (r : ℤ)
  have h12 : (k2.val : ℤ) - (s1 + s2) = (j2.val : ℤ) + (r : ℤ) * (q1 + q2) := by linarith
  have hdiv : ((k2.val : ℤ) - (s1 + s2)) / (r : ℤ) = q1 + q2 := by
    rw [h12, Int.add_mul_ediv_left _ _ (ne_of_gt hr),
      Int.ediv_eq_zero_of_lt (Int.natCast_nonneg j2.val) (Int.ofNat_lt.mpr j2.isLt), zero_add]
  rw [hdiv, zpow_add₀ (by norm_num)]
  ring

/-- Negacyclic periodicity: shifting by $r$ negates the polynomial ($y^r \equiv -1$). -/
theorem negacyclicShift_period {r : ℕ} (P : Fin r → ℂ) :
    negacyclicShift (r : ℤ) P = fun k2 => - P k2 := by
  funext k2
  rw [negacyclicShift_eq_ite_mod_two_mul]
  have hr : (0 : ℤ) < (r : ℤ) := Nat.cast_pos.mpr k2.pos
  have hmod2 : ((k2.val : ℤ) - (r : ℤ)) % (2 * (r : ℤ)) = (k2.val : ℤ) + (r : ℤ) := by
    have h1 : (k2.val : ℤ) - (r : ℤ) = ((k2.val : ℤ) + (r : ℤ)) + (2 * (r : ℤ)) * (-1) := by ring
    rw [h1, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by have := k2.isLt; omega)]
  have hshift : shiftModFin (r : ℤ) k2 = k2 := by
    apply Fin.ext
    rw [← Int.ofNat_inj, coe_shiftModFin]
    have h1 : (k2.val : ℤ) - (r : ℤ) = (k2.val : ℤ) + (r : ℤ) * (-1) := by ring
    rw [h1, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (Int.natCast_nonneg k2.val) (Int.ofNat_lt.mpr k2.isLt)]
  rw [hmod2, hshift, if_neg (by omega)]

/-- Shifting by $2r$ is the identity on $\mathcal{R}_r$ ($y^{2r} \equiv 1$). -/
theorem negacyclicShift_two_period {r : ℕ} (P : Fin r → ℂ) :
    negacyclicShift (2 * (r : ℤ)) P = P := by
  have h : (2 : ℤ) * (r : ℤ) = (r : ℤ) + (r : ℤ) := by ring
  rw [h, negacyclicShift_add, negacyclicShift_period, negacyclicShift_period]
  funext k2
  ring

/-- Shifting by any integer multiple of $2r$ leaves `negacyclicShift` unchanged. -/
theorem negacyclicShift_add_mul_two_period {r : ℕ} (s m : ℤ) (P : Fin r → ℂ) :
    negacyclicShift (s + m * (2 * (r : ℤ))) P = negacyclicShift s P := by
  funext k2
  rw [negacyclicShift_eq_ite_mod_two_mul, negacyclicShift_eq_ite_mod_two_mul]
  have h1 : ((k2.val : ℤ) - (s + m * (2 * (r : ℤ)))) % (2 * (r : ℤ)) =
      ((k2.val : ℤ) - s) % (2 * (r : ℤ)) := by
    have h_eq : (k2.val : ℤ) - (s + m * (2 * (r : ℤ))) =
        ((k2.val : ℤ) - s) + (2 * (r : ℤ)) * (-m) := by ring
    rw [h_eq, Int.add_mul_emod_self_left]
  have h2 : shiftModFin (s + m * (2 * (r : ℤ))) k2 = shiftModFin s k2 := by
    apply Fin.ext
    rw [← Int.ofNat_inj, coe_shiftModFin, coe_shiftModFin]
    have h_eq : (k2.val : ℤ) - (s + m * (2 * (r : ℤ))) =
        ((k2.val : ℤ) - s) + (r : ℤ) * (-2 * m) := by ring
    rw [h_eq, Int.add_mul_emod_self_left]
  rw [h1, h2]

/-- Negacyclic polynomial multiplication in $\mathcal{R}_r = \mathbb{C}[y]/(y^r + 1)$ (Section 3.5 (`sec:prelim-dft`)). -/
noncomputable def negacyclicMul {r : ℕ} (P Q : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => ∑ j : Fin r, P j * negacyclicShift (j.val : ℤ) Q k2

/-- General odd-root evaluation functional $P \mapsto \sum_{k_2=0}^{r-1} P(k_2) \zeta^{m k_2}$
for an odd integer $m \in \mathbb{Z}$ (Section 4.1 (`sec:twisted`), Proposition 4.1 (`thm:twisted`)). -/
noncomputable def evalZetaOdd {r : ℕ} (m : ℤ) (P : Fin r → ℂ) : ℂ :=
  ∑ k2 : Fin r, P k2 * zetaPow r (m * (k2.val : ℤ))

/-- Negacyclic evaluation homomorphism $\phi_{u_2}(P) = \sum_{k_2=0}^{r-1} P(k_2) \zeta^{(2u_2 - 1) k_2}$
at $\xi_{u_2} = \zeta^{2u_2 - 1}$ (Section 4.1 (`sec:twisted`), Proposition 4.1 (`thm:twisted`)). -/
noncomputable def phiOddRoot {r : ℕ} (u2 : ℕ) (P : Fin r → ℂ) : ℂ :=
  ∑ k2 : Fin r, P k2 * zetaPow r ((2 * (u2 : ℤ) - 1) * (k2.val : ℤ))

/-- Conjugate odd-root evaluation functional at $\zeta^{-(2u_2 + 1)}$ (Section 4.1 (`sec:twisted`)). -/
noncomputable def evalOddRoot {r : ℕ} (u2 : ℕ) (P : Fin r → ℂ) : ℂ :=
  ∑ k2 : Fin r, P k2 * zetaPow r (-((2 * u2 + 1 : ℕ) * k2.val : ℤ))

theorem phiOddRoot_eq_evalZetaOdd {r : ℕ} (u2 : ℕ) (P : Fin r → ℂ) :
    phiOddRoot u2 P = evalZetaOdd (2 * (u2 : ℤ) - 1) P := rfl

theorem evalOddRoot_eq_evalZetaOdd {r : ℕ} (u2 : ℕ) (P : Fin r → ℂ) :
    evalOddRoot u2 P = evalZetaOdd (-((2 * u2 + 1 : ℕ) : ℤ)) P := by
  unfold evalOddRoot evalZetaOdd
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  congr 2

theorem evalZetaOdd_add {r : ℕ} (m : ℤ) (P Q : Fin r → ℂ) :
    evalZetaOdd m (fun k2 => P k2 + Q k2) = evalZetaOdd m P + evalZetaOdd m Q := by
  unfold evalZetaOdd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  ring

theorem evalZetaOdd_sub {r : ℕ} (m : ℤ) (P Q : Fin r → ℂ) :
    evalZetaOdd m (fun k2 => P k2 - Q k2) = evalZetaOdd m P - evalZetaOdd m Q := by
  unfold evalZetaOdd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  ring

theorem evalZetaOdd_smul {r : ℕ} (m : ℤ) (c : ℂ) (P : Fin r → ℂ) :
    evalZetaOdd m (fun k2 => c * P k2) = c * evalZetaOdd m P := by
  unfold evalZetaOdd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  ring

theorem evalZetaOdd_sum {r : ℕ} {ι : Type*} (s : Finset ι) (m : ℤ) (f : ι → Fin r → ℂ) :
    evalZetaOdd m (fun k2 => ∑ i ∈ s, f i k2) = ∑ i ∈ s, evalZetaOdd m (f i) := by
  unfold evalZetaOdd
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem evalOddRoot_add {r : ℕ} (u2 : ℕ) (P Q : Fin r → ℂ) :
    evalOddRoot u2 (fun k2 => P k2 + Q k2) = evalOddRoot u2 P + evalOddRoot u2 Q := by
  simp only [evalOddRoot_eq_evalZetaOdd, evalZetaOdd_add]

theorem evalOddRoot_sub {r : ℕ} (u2 : ℕ) (P Q : Fin r → ℂ) :
    evalOddRoot u2 (fun k2 => P k2 - Q k2) = evalOddRoot u2 P - evalOddRoot u2 Q := by
  simp only [evalOddRoot_eq_evalZetaOdd, evalZetaOdd_sub]

theorem evalOddRoot_smul {r : ℕ} (u2 : ℕ) (c : ℂ) (P : Fin r → ℂ) :
    evalOddRoot u2 (fun k2 => c * P k2) = c * evalOddRoot u2 P := by
  simp only [evalOddRoot_eq_evalZetaOdd, evalZetaOdd_smul]

theorem phiOddRoot_add {r : ℕ} (u2 : ℕ) (P Q : Fin r → ℂ) :
    phiOddRoot u2 (fun k2 => P k2 + Q k2) = phiOddRoot u2 P + phiOddRoot u2 Q :=
  evalZetaOdd_add _ P Q

theorem phiOddRoot_sub {r : ℕ} (u2 : ℕ) (P Q : Fin r → ℂ) :
    phiOddRoot u2 (fun k2 => P k2 - Q k2) = phiOddRoot u2 P - phiOddRoot u2 Q :=
  evalZetaOdd_sub _ P Q

theorem phiOddRoot_smul {r : ℕ} (u2 : ℕ) (c : ℂ) (P : Fin r → ℂ) :
    phiOddRoot u2 (fun k2 => c * P k2) = c * phiOddRoot u2 P :=
  evalZetaOdd_smul _ c P

/-- **Fundamental Odd-Root Shift Theorem**: For any odd integer $m \in \mathbb{Z}$,
evaluating `negacyclicShift s P` at $\zeta^m$ multiplies the evaluation by $\zeta^{m s}$. -/
theorem evalZetaOdd_negacyclicShift {r : ℕ} {m : ℤ} (hm : Odd m) (s : ℤ) (P : Fin r → ℂ) :
    evalZetaOdd m (negacyclicShift s P) = zetaPow r (m * s) * evalZetaOdd m P := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [evalZetaOdd]
  · unfold evalZetaOdd negacyclicShift
    have h_term : ∀ k2 : Fin r,
        ((-1 : ℂ) ^ (((k2.val : ℤ) - s) / (r : ℤ)) * P (shiftModFin s k2)) *
          zetaPow r (m * (k2.val : ℤ)) =
        zetaPow r (m * s) *
          (P (shiftModFin s k2) * zetaPow r (m * ((shiftModFin s k2).val : ℤ))) := by
      intro k2
      set q : ℤ := ((k2.val : ℤ) - s) / (r : ℤ)
      set j : Fin r := shiftModFin s k2
      have hk2 : (k2.val : ℤ) = (r : ℤ) * q + (j.val : ℤ) + s := by
        have h_div := Int.mul_ediv_add_emod ((k2.val : ℤ) - s) (r : ℤ)
        have hj : (j.val : ℤ) = ((k2.val : ℤ) - s) % (r : ℤ) := coe_shiftModFin s k2
        linarith
      have h_exp : m * (k2.val : ℤ) = (m * (r : ℤ)) * q + m * (j.val : ℤ) + m * s := by
        rw [hk2]; ring
      rw [h_exp, zetaPow_add, zetaPow_add, zetaPow_int_mul, zetaPow_odd_mul_self hr hm]
      have h_cancel : (-1 : ℂ) ^ q * (-1 : ℂ) ^ q = 1 := by
        rw [← mul_zpow]
        norm_num
      calc
        (-1 : ℂ) ^ q * P j * ((-1 : ℂ) ^ q * zetaPow r (m * (j.val : ℤ)) * zetaPow r (m * s))
          = ((-1 : ℂ) ^ q * (-1 : ℂ) ^ q) *
              (zetaPow r (m * s) * (P j * zetaPow r (m * (j.val : ℤ)))) := by ring
        _ = zetaPow r (m * s) * (P j * zetaPow r (m * (j.val : ℤ))) := by
            rw [h_cancel, one_mul]
    simp_rw [h_term, ← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp (shiftModFinEquiv s)
      (fun j : Fin r => P j * zetaPow r (m * (j.val : ℤ)))

/-- Multiplicativity of `evalZetaOdd` with respect to `negacyclicMul` (Section 4.1 (`sec:twisted`), Proposition 4.1 (`thm:twisted`)). -/
theorem evalZetaOdd_negacyclicMul {r : ℕ} {m : ℤ} (hm : Odd m) (P Q : Fin r → ℂ) :
    evalZetaOdd m (negacyclicMul P Q) = evalZetaOdd m P * evalZetaOdd m Q := by
  unfold negacyclicMul
  rw [evalZetaOdd_sum]
  have h : ∀ j : Fin r,
      evalZetaOdd m (fun k2 => P j * negacyclicShift (j.val : ℤ) Q k2) =
        (P j * zetaPow r (m * (j.val : ℤ))) * evalZetaOdd m Q := by
    intro j
    rw [evalZetaOdd_smul, evalZetaOdd_negacyclicShift hm]
    ring
  simp_rw [h, ← Finset.sum_mul]
  rfl

/-- Oddness of $2 u_2 - 1$. -/
theorem odd_two_mul_sub_one (u2 : ℕ) : Odd (2 * (u2 : ℤ) - 1) :=
  ⟨(u2 : ℤ) - 1, by ring⟩

/-- Oddness of $-((2 u_2 + 1 : \mathbb{N}) : \mathbb{Z})$. -/
theorem odd_neg_two_mul_add_one (u2 : ℕ) : Odd (-((2 * u2 + 1 : ℕ) : ℤ)) :=
  ⟨-(u2 : ℤ) - 1, by push_cast; ring⟩

/-- **Negacyclic Root Twist for `phiOddRoot`** ($\xi_{u_2} = \zeta^{2u_2 - 1}$, Section 4.1 (`sec:twisted`), Proposition 4.1 (`thm:twisted`)):
$$\phi_{u_2}(y^s P) = \zeta^{(2u_2 - 1) s} \phi_{u_2}(P).$$ -/
theorem phiOddRoot_negacyclicShift {r : ℕ} (u2 : ℕ) (s : ℤ) (P : Fin r → ℂ) :
    phiOddRoot u2 (negacyclicShift s P) =
      zetaPow r ((2 * (u2 : ℤ) - 1) * s) * phiOddRoot u2 P :=
  evalZetaOdd_negacyclicShift (odd_two_mul_sub_one u2) s P

/-- Multiplicativity of `phiOddRoot` on $\mathcal{R}_r$. -/
theorem phiOddRoot_negacyclicMul {r : ℕ} (u2 : ℕ) (P Q : Fin r → ℂ) :
    phiOddRoot u2 (negacyclicMul P Q) = phiOddRoot u2 P * phiOddRoot u2 Q :=
  evalZetaOdd_negacyclicMul (odd_two_mul_sub_one u2) P Q

/-- **Negacyclic Root Twist for `evalOddRoot`** ($\zeta^{-(2u_2 + 1)}$, Section 4.1 (`sec:twisted`)):
$$\text{evalOddRoot } u_2 (\text{negacyclicShift } s \, P) = \zeta^{-(2u_2 + 1) s} \text{evalOddRoot } u_2 \, P.$$ -/
theorem evalOddRoot_negacyclicShift {r : ℕ} (u2 : ℕ) (s : ℤ) (P : Fin r → ℂ) :
    evalOddRoot u2 (negacyclicShift s P) =
      zetaPow r (-((2 * u2 + 1 : ℕ) : ℤ) * s) * evalOddRoot u2 P := by
  simp only [evalOddRoot_eq_evalZetaOdd]
  exact evalZetaOdd_negacyclicShift (odd_neg_two_mul_add_one u2) s P

/-- Multiplicativity of `evalOddRoot` on $\mathcal{R}_r$. -/
theorem evalOddRoot_negacyclicMul {r : ℕ} (u2 : ℕ) (P Q : Fin r → ℂ) :
    evalOddRoot u2 (negacyclicMul P Q) = evalOddRoot u2 P * evalOddRoot u2 Q := by
  simp only [evalOddRoot_eq_evalZetaOdd]
  exact evalZetaOdd_negacyclicMul (odd_neg_two_mul_add_one u2) P Q

/-- **Fractional-Frequency Twist Identity for $y^{-c_1 j_1}$** (Section 4.1 (`sec:twisted`)):
When $t_1 c_1 = r$ ($t_1 > 0, c_1 > 0$),
$$\text{evalOddRoot } u_2 (y^{-c_1 j_1} P) = \zeta^{(2u_2 + 1) c_1 j_1} \text{evalOddRoot } u_2 \, P
  = e^{2\pi i (u_2 + 1/2) j_1 / t_1} \text{evalOddRoot } u_2 \, P.$$ -/
theorem evalOddRoot_negacyclicShift_neg_c1 {t1 c1 r : ℕ} (ht1 : 0 < t1) (hc1 : 0 < c1)
    (h_rc : t1 * c1 = r) (u2 j1 : ℕ) (P : Fin r → ℂ) :
    evalOddRoot u2 (negacyclicShift (-((c1 * j1 : ℕ) : ℤ)) P) =
      expTwoPiI ((((u2 : ℝ) + 1 / 2) * (j1 : ℝ)) / (t1 : ℝ)) * evalOddRoot u2 P ∧
    evalOddRoot u2 (negacyclicShift (-((c1 * j1 : ℕ) : ℤ)) P) =
      zetaPow r (((2 * u2 + 1 : ℕ) : ℤ) * ((c1 * j1 : ℕ) : ℤ)) * evalOddRoot u2 P := by
  have h_zeta :
      evalOddRoot u2 (negacyclicShift (-((c1 * j1 : ℕ) : ℤ)) P) =
        zetaPow r (((2 * u2 + 1 : ℕ) : ℤ) * ((c1 * j1 : ℕ) : ℤ)) * evalOddRoot u2 P := by
    rw [evalOddRoot_negacyclicShift]
    congr 2
    ring
  refine ⟨?_, h_zeta⟩
  rw [h_zeta]
  congr 1
  unfold zetaPow expTwoPiI
  congr 1
  have ht1_ne : (t1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ht1)
  have hc1_ne : (c1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hc1)
  subst h_rc
  push_cast
  field_simp [ht1_ne, hc1_ne]

/-! ## 5. Proposition 4.1 (`thm:twisted`): Polynomial-Transform Reduction (Nussbaumer–Quandalle, Section 4.1 (`sec:twisted`)) -/

/-- Pre-twist $\tilde{U}_{j_1, k_2} := \zeta^{k_2} U_{j_1, k_2}$ (Proposition 4.1 (`thm:twisted`), Step 1). -/
noncomputable def preTwist {r : ℕ} (P : Fin r → ℂ) (k2 : Fin r) : ℂ :=
  zetaPow r (k2.val : ℤ) * P k2

/-- Post-twist $\tilde{q}_{v_1, k_2} := \zeta^{-k_2} q_{v_1, k_2}$ (Proposition 4.1 (`thm:twisted`), Step 3). -/
noncomputable def postTwist {r : ℕ} (Q : Fin r → ℂ) (k2 : Fin r) : ℂ :=
  zetaPow r (-(k2.val : ℤ)) * Q k2

@[simp]
theorem vecInfNorm_preTwist {r : ℕ} (P : Fin r → ℂ) :
    vecInfNorm (preTwist P) = vecInfNorm P := by
  apply le_antisymm
  · apply vecInfNorm_le _ (vecInfNorm_nonneg P)
    intro k2
    unfold preTwist
    rw [norm_mul, norm_zetaPow, one_mul]
    exact norm_le_vecInfNorm P k2
  · apply vecInfNorm_le _ (vecInfNorm_nonneg (preTwist P))
    intro k2
    have h := norm_le_vecInfNorm (preTwist P) k2
    unfold preTwist at h
    rwa [norm_mul, norm_zetaPow, one_mul] at h

@[simp]
theorem vecInfNorm_postTwist {r : ℕ} (Q : Fin r → ℂ) :
    vecInfNorm (postTwist Q) = vecInfNorm Q := by
  apply le_antisymm
  · apply vecInfNorm_le _ (vecInfNorm_nonneg Q)
    intro k2
    unfold postTwist
    rw [norm_mul, norm_zetaPow, one_mul]
    exact norm_le_vecInfNorm Q k2
  · apply vecInfNorm_le _ (vecInfNorm_nonneg (postTwist Q))
    intro k2
    have h := norm_le_vecInfNorm (postTwist Q) k2
    unfold postTwist at h
    rwa [norm_mul, norm_zetaPow, one_mul] at h

/-- 1D polynomial transform (`syntheticFFT` in this development) $G_{t_1} : (\mathcal{R}_r)^{t_1} \to (\mathcal{R}_r)^{t_1}$ defined by
$(G_{t_1} P)_{v_1}(y) := \frac{1}{t_1} \sum_{j_1=0}^{t_1-1} P_{j_1}(y) y^{2c_1 j_1 v_1} \bmod (y^r + 1)$
(Section 3.5 (`sec:prelim-dft`), equation (12) (`eq:syn-fft`), and Proposition 4.1 (`thm:twisted`), Step 2). -/
noncomputable def syntheticFFT {t1 r : ℕ} (c1 : ℕ) (P : Fin t1 → Fin r → ℂ) (v1 : Fin t1) :
    Fin r → ℂ :=
  fun k2 => ((t1 : ℝ)⁻¹ : ℂ) *
    ∑ j1 : Fin t1, negacyclicShift (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ)) (P j1) k2

/-- Half-step polynomial transform $A_{u_1}(k_2) = \frac{1}{t_1} \sum_{j_1=0}^{t_1-1} (y^{-c_1 j_1 u_1} P_{j_1})(k_2)$ (Section 4.1 (`sec:twisted`)). -/
noncomputable def syntheticFFTOdd {t1 r : ℕ} (c1 : ℕ) (P : Fin t1 → Fin r → ℂ) (u1 : Fin t1) :
    Fin r → ℂ :=
  fun k2 => ((t1 : ℝ)⁻¹ : ℂ) *
    ∑ j1 : Fin t1, negacyclicShift (-((c1 * j1.val * u1.val : ℕ) : ℤ)) (P j1) k2

/-- Negative-exponent normalized 1D DFT $(F_R^{-} x)_u = \frac{1}{R} \sum_{k=0}^{R-1} x_k e^{-2\pi i u k / R}$. -/
noncomputable def normDFT1DNeg {R : ℕ} (x : Fin R → ℂ) (u : Fin R) : ℂ :=
  ((R : ℝ)⁻¹ : ℂ) * ∑ k : Fin R, x k * expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ))

/-- Odd-stride destination index $u_1 = ((2 u_2 - 1) v_1) \bmod t_1 \in \text{Fin } t_1$
(Proposition 4.1 (`thm:twisted`), Step 5, equation (14) (`eq:odd-perm`)). -/
def oddStrideIndex {t1 : ℕ} (u2 : ℕ) (v1 : Fin t1) : Fin t1 :=
  ⟨(((2 * (u2 : ℤ) - 1) * (v1.val : ℤ)) % (t1 : ℤ)).toNat, by
    have ht1 : (0 : ℤ) < (t1 : ℤ) := Nat.cast_pos.mpr v1.pos
    have h0 := Int.emod_nonneg ((2 * (u2 : ℤ) - 1) * (v1.val : ℤ)) (ne_of_gt ht1)
    have hlt := Int.emod_lt_of_pos ((2 * (u2 : ℤ) - 1) * (v1.val : ℤ)) ht1
    omega⟩

@[simp]
theorem coe_oddStrideIndex {t1 : ℕ} (u2 : ℕ) (v1 : Fin t1) :
    ((oddStrideIndex u2 v1).val : ℤ) = ((2 * (u2 : ℤ) - 1) * (v1.val : ℤ)) % (t1 : ℤ) := by
  unfold oddStrideIndex
  dsimp
  have ht1 : (0 : ℤ) < (t1 : ℤ) := Nat.cast_pos.mpr v1.pos
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt ht1))

/-- The natural absolute value `|2 * u2 - 1|` is odd for every `u2 : ℕ`. -/
theorem natAbs_two_mul_sub_one_mod_two (u2 : ℕ) :
    (2 * (u2 : ℤ) - 1).natAbs % 2 = 1 := by
  rcases u2 with _ | u2
  · decide
  · have h : 2 * ((u2 + 1 : ℕ) : ℤ) - 1 = ((2 * u2 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.natAbs_natCast]
    omega

/-- `2 ^ k1` is coprime to `|2 * u2 - 1|` for all `k1 u2 : ℕ`. -/
theorem coprime_two_pow_natAbs_two_mul_sub_one (k1 u2 : ℕ) :
    Nat.Coprime (2 ^ k1) (2 * (u2 : ℤ) - 1).natAbs := by
  apply Nat.Coprime.pow_left k1
  rw [Nat.coprime_two_left, Nat.odd_iff]
  exact natAbs_two_mul_sub_one_mod_two u2

/-- Injectivity of the odd-stride permutation `oddStrideIndex u2` on `Fin (2 ^ k1)` (Proposition 4.1 (`thm:twisted`), Step 5). -/
theorem oddStrideIndex_injective {k1 : ℕ} (u2 : ℕ) :
    Function.Injective (oddStrideIndex (t1 := 2 ^ k1) u2) := by
  intro v1 w1 h
  have hval : ((oddStrideIndex (t1 := 2 ^ k1) u2 v1).val : ℤ) =
      ((oddStrideIndex (t1 := 2 ^ k1) u2 w1).val : ℤ) := by rw [h]
  rw [coe_oddStrideIndex, coe_oddStrideIndex] at hval
  set m : ℤ := 2 * (u2 : ℤ) - 1
  set N : ℤ := ((2 ^ k1 : ℕ) : ℤ)
  have hdiv1 := Int.mul_ediv_add_emod (m * (v1.val : ℤ)) N
  have hdiv2 := Int.mul_ediv_add_emod (m * (w1.val : ℤ)) N
  have hdvd_z : N ∣ m * ((v1.val : ℤ) - (w1.val : ℤ)) := by
    refine ⟨(m * (v1.val : ℤ)) / N - (m * (w1.val : ℤ)) / N, ?_⟩
    linarith
  have hdvd_nat : 2 ^ k1 ∣ m.natAbs * ((v1.val : ℤ) - (w1.val : ℤ)).natAbs := by
    have h1 : N.natAbs ∣ (m * ((v1.val : ℤ) - (w1.val : ℤ))).natAbs :=
      Int.natAbs_dvd_natAbs.mpr hdvd_z
    simpa [N, Int.natAbs_mul] using h1
  have hcop : Nat.Coprime (2 ^ k1) m.natAbs :=
    coprime_two_pow_natAbs_two_mul_sub_one k1 u2
  have hdvd_diff : 2 ^ k1 ∣ ((v1.val : ℤ) - (w1.val : ℤ)).natAbs :=
    hcop.dvd_of_dvd_mul_left hdvd_nat
  have hlt_diff : ((v1.val : ℤ) - (w1.val : ℤ)).natAbs < 2 ^ k1 := by
    have hv := v1.isLt
    have hw := w1.isLt
    omega
  have hzero : ((v1.val : ℤ) - (w1.val : ℤ)).natAbs = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd_diff hlt_diff
  ext
  omega

/-- **Bijectivity of the Odd-Stride Permutation (`oddStrideIndex_bijective`, Proposition 4.1 (`thm:twisted`), Step 5)**:
Since $2 u_2 - 1$ is odd and $t_1 = 2^{k_1}$ is a power of 2, the map
$v_1 \mapsto ((2 u_2 - 1) v_1) \bmod 2^{k_1}$ is a bijection on `Fin (2 ^ k1)` for every $u_2$. -/
theorem oddStrideIndex_bijective {k1 : ℕ} (u2 : ℕ) :
    Function.Bijective (oddStrideIndex (t1 := 2 ^ k1) u2) :=
  Finite.injective_iff_bijective.mp (oddStrideIndex_injective u2)

/-- **Post-Twist 1D DFT Duality Identity** (Section 4.1 (`sec:twisted`), Proposition 4.1 (`thm:twisted`)):
For any polynomial $Q \in \mathcal{R}_r$ and frequency $u_2 \in \text{Fin } r$,
$$(F_r (\zeta^{-k_2} Q))_{u_2} = \frac{1}{r} \phi_{u_2}(Q).$$ -/
theorem normDFT1D_postTwist_eq_phiOddRoot {r : ℕ} (Q : Fin r → ℂ) (u2 : Fin r) :
    normDFT1D (postTwist Q) u2 = ((r : ℝ)⁻¹ : ℂ) * phiOddRoot u2.val Q := by
  unfold normDFT1D postTwist phiOddRoot
  congr 1
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  have h_exp : expTwoPiI (((k2.val * u2.val : ℕ) : ℝ) / (r : ℝ)) =
      zetaPow r (2 * ((u2.val : ℤ) * (k2.val : ℤ))) := by
    rw [zetaPow_two_mul]
    congr 1
    push_cast
    ring
  rw [h_exp, mul_comm (zetaPow r (-(k2.val : ℤ))) (Q k2), mul_assoc, ← zetaPow_add]
  congr 2
  ring

/-- **Pre-Twist Evaluation Identity** (Section 4.1 (`sec:twisted`), Proposition 4.1 (`thm:twisted`)):
$$\phi_{u_2}(\text{preTwist } U_{j_1}) = \sum_{k_2=0}^{r-1} U_{j_1, k_2} e^{2\pi i k_2 u_2 / r}.$$ -/
theorem phiOddRoot_preTwist_eq {r : ℕ} (row : Fin r → ℂ) (u2 : Fin r) :
    phiOddRoot u2.val (preTwist row) =
      ∑ k2 : Fin r, row k2 * expTwoPiI (((k2.val * u2.val : ℕ) : ℝ) / (r : ℝ)) := by
  unfold phiOddRoot preTwist
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  rw [mul_comm (zetaPow r (k2.val : ℤ)) (row k2), mul_assoc, ← zetaPow_add]
  have h_exp : (k2.val : ℤ) + (2 * (u2.val : ℤ) - 1) * (k2.val : ℤ) =
      2 * ((k2.val : ℤ) * (u2.val : ℤ)) := by ring
  rw [h_exp, zetaPow_two_mul]
  congr 2

/-- **Proposition 4.1 (`thm:twisted`) (Polynomial-Transform Reduction (Nussbaumer–Quandalle) for 2D DFT, Section 4.1 (`sec:twisted`))**:
For $t_1 c_1 = r$, pre-twisting $U$ to $P_{j_1} = \text{preTwist } (U \, j_1)$, applying the
polynomial transform (`syntheticFFT`) $Q = G_{t_1} P$, post-twisting $\tilde{Q}_{v_1} = \text{postTwist } (Q \, v_1)$,
and taking 1D DFTs $F_r \tilde{Q}_{v_1}$ yields the exact 2D DFT $(F_{t_1, r} U)_{u_1, u_2}$ at
$u_1 = ((2 u_2 - 1) v_1) \bmod t_1$:
$$(F_r \tilde{Q}_{v_1})_{u_2} = \frac{1}{r} \phi_{u_2}(Q_{v_1}) = (F_{t_1, r} U)_{((2u_2 - 1) v_1) \bmod t_1, u_2}.$$ -/
theorem twisted_fourier_duality_reduction {t1 c1 r : ℕ} (h_rc : t1 * c1 = r)
    (U : Fin t1 → Fin r → ℂ) (v1 : Fin t1) (u2 : Fin r) :
    normDFT1D (postTwist (syntheticFFT c1 (fun j1 => preTwist (U j1)) v1)) u2 =
      ((r : ℝ)⁻¹ : ℂ) * phiOddRoot u2.val (syntheticFFT c1 (fun j1 => preTwist (U j1)) v1) ∧
    normDFT1D (postTwist (syntheticFFT c1 (fun j1 => preTwist (U j1)) v1)) u2 =
      normDFT2D U (oddStrideIndex u2.val v1) u2 := by
  have h_first :=
    normDFT1D_postTwist_eq_phiOddRoot (syntheticFFT c1 (fun j1 => preTwist (U j1)) v1) u2
  refine ⟨h_first, ?_⟩
  rw [h_first]
  have ht1_pos : 0 < t1 := v1.pos
  have hr_pos : 0 < r := u2.pos
  have hc1_pos : 0 < c1 := by
    by_contra hc1
    simp only [not_lt, Nat.le_zero] at hc1
    subst hc1
    omega
  unfold syntheticFFT
  rw [phiOddRoot_smul, phiOddRoot_eq_evalZetaOdd, evalZetaOdd_sum]
  unfold normDFT2D
  have h_inv : ((r : ℝ)⁻¹ : ℂ) * (((t1 : ℝ)⁻¹ : ℂ) *
      ∑ i : Fin t1, evalZetaOdd (2 * (u2.val : ℤ) - 1)
        (negacyclicShift (2 * (c1 : ℤ) * (i.val : ℤ) * (v1.val : ℤ)) (preTwist (U i)))) =
    (((t1 * r : ℕ) : ℝ)⁻¹ : ℂ) *
      ∑ i : Fin t1, evalZetaOdd (2 * (u2.val : ℤ) - 1)
        (negacyclicShift (2 * (c1 : ℤ) * (i.val : ℤ) * (v1.val : ℤ)) (preTwist (U i))) := by
    rw [← mul_assoc]
    congr 1
    push_cast
    ring
  rw [h_inv]
  congr 1
  refine Finset.sum_congr rfl (fun j1 _ => ?_)
  rw [← phiOddRoot_eq_evalZetaOdd, phiOddRoot_negacyclicShift, phiOddRoot_preTwist_eq]
  have h_twiddle :
      zetaPow r ((2 * (u2.val : ℤ) - 1) * (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ))) =
        expTwoPiI (((j1.val * (oddStrideIndex u2.val v1).val : ℕ) : ℝ) / (t1 : ℝ)) := by
    have h_mul : (2 * (u2.val : ℤ) - 1) * (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ)) =
        2 * ((j1.val : ℤ) * ((2 * (u2.val : ℤ) - 1) * (v1.val : ℤ)) * (c1 : ℤ)) := by ring
    rw [h_mul, zetaPow_two_mul]
    have ht1_ne : (t1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ht1_pos)
    have hc1_ne : (c1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hc1_pos)
    set u1 := oddStrideIndex u2.val v1
    set m : ℤ := (2 * (u2.val : ℤ) - 1) * (v1.val : ℤ)
    have hm_div : m = (t1 : ℤ) * (m / (t1 : ℤ)) + (u1.val : ℤ) := by
      rw [coe_oddStrideIndex]
      exact (Int.mul_ediv_add_emod m (t1 : ℤ)).symm
    have h_frac :
        (((j1.val : ℤ) * m * (c1 : ℤ) : ℤ) : ℝ) / (r : ℝ) =
          (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) +
            (((j1.val : ℤ) * (m / (t1 : ℤ)) : ℤ) : ℝ) := by
      rw [← h_rc]
      push_cast
      have hm_real : (m : ℝ) = (t1 : ℝ) * ((m / (t1 : ℤ) : ℤ) : ℝ) + (u1.val : ℝ) := by
        exact_mod_cast hm_div
      rw [hm_real]
      field_simp [ht1_ne, hc1_ne]
      ring
    rw [h_frac, expTwoPiI_add_int]
  rw [h_twiddle, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  ring

/-- **Twisted 1D DFT Duality Identity for `evalOddRoot` and `syntheticFFTOdd`** (Section 4.1 (`sec:twisted`)):
For all $u_1 \in \text{Fin } t_1$ and $u_2 \in \text{Fin } r$ with $t_1 c_1 = r$,
$$(F_r^{-} \tilde{A}_{u_1})_{u_2} = \frac{1}{r} \text{evalOddRoot } u_2 (A_{u_1})
  = \frac{1}{t_1 r} \sum_{j_1=0}^{t_1-1} e^{2\pi i (u_2 + 1/2) j_1 u_1 / t_1} \text{evalOddRoot } u_2 (P_{j_1}).$$ -/
theorem normDFT1D_odd_eq_normDFT1D_twisted {t1 c1 r : ℕ} (h_rc : t1 * c1 = r)
    (P : Fin t1 → Fin r → ℂ) (u1 : Fin t1) (u2 : Fin r) :
    normDFT1DNeg (postTwist (syntheticFFTOdd c1 P u1)) u2 =
      ((r : ℝ)⁻¹ : ℂ) * evalOddRoot u2.val (syntheticFFTOdd c1 P u1) ∧
    ((r : ℝ)⁻¹ : ℂ) * evalOddRoot u2.val (syntheticFFTOdd c1 P u1) =
      (((t1 * r : ℕ) : ℝ)⁻¹ : ℂ) *
        ∑ j1 : Fin t1,
          expTwoPiI ((((u2.val : ℝ) + 1 / 2) * ((j1.val * u1.val : ℕ) : ℝ)) / (t1 : ℝ)) *
            evalOddRoot u2.val (P j1) := by
  have h1 : normDFT1DNeg (postTwist (syntheticFFTOdd c1 P u1)) u2 =
      ((r : ℝ)⁻¹ : ℂ) * evalOddRoot u2.val (syntheticFFTOdd c1 P u1) := by
    unfold normDFT1DNeg postTwist evalOddRoot
    congr 1
    refine Finset.sum_congr rfl (fun k2 _ => ?_)
    have h_exp : expNegTwoPiI (((u2.val * k2.val : ℕ) : ℝ) / (r : ℝ)) =
        zetaPow r (-2 * ((u2.val : ℤ) * (k2.val : ℤ))) := by
      rw [zetaPow_neg_two_mul]
      congr 1
    rw [h_exp, mul_comm (zetaPow r (-(k2.val : ℤ))) _, mul_assoc, ← zetaPow_add]
    congr 2
    push_cast
    ring
  refine ⟨h1, ?_⟩
  have ht1_pos : 0 < t1 := u1.pos
  have hr_pos : 0 < r := u2.pos
  have hc1_pos : 0 < c1 := by
    by_contra hc1
    simp only [not_lt, Nat.le_zero] at hc1
    subst hc1
    omega
  unfold syntheticFFTOdd
  rw [evalOddRoot_smul, evalOddRoot_eq_evalZetaOdd, evalZetaOdd_sum]
  rw [← mul_assoc]
  congr 1
  · push_cast; ring
  · refine Finset.sum_congr rfl (fun j1 _ => ?_)
    rw [← evalOddRoot_eq_evalZetaOdd, Nat.mul_assoc c1 j1.val u1.val]
    exact (evalOddRoot_negacyclicShift_neg_c1 ht1_pos hc1_pos h_rc
      u2.val (j1.val * u1.val) (P j1)).1

/-! ## 6. Lemma 3.5 (`lem:syn-fft`): Exactness and Stability of the Radix-2 Polynomial Transform (Section 3.5 (`sec:prelim-dft`)) -/

/-- Exact radix-2 negacyclic butterfly upper output $\frac{1}{2}(U + y^s V) \in \mathcal{R}_r$ (Lemma 3.5 (`lem:syn-fft`)). -/
noncomputable def butterflyPlusExact {r : ℕ} (s : ℤ) (U V : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => (U k2 + negacyclicShift s V k2) / 2

/-- Exact radix-2 negacyclic butterfly lower output $\frac{1}{2}(U - y^s V) \in \mathcal{R}_r$ (Lemma 3.5 (`lem:syn-fft`)). -/
noncomputable def butterflyMinusExact {r : ℕ} (s : ℤ) (U V : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => (U k2 - negacyclicShift s V k2) / 2

/-- Quantized radix-2 negacyclic butterfly upper output at $q$ fractional bits (Lemma 3.5 (`lem:syn-fft`)). -/
noncomputable def butterflyPlusQuant {r : ℕ} (q : ℕ) (s : ℤ) (U V : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => quantizeComplex q ((U k2 + negacyclicShift s V k2) / 2)

/-- Quantized radix-2 negacyclic butterfly lower output at $q$ fractional bits (Lemma 3.5 (`lem:syn-fft`)). -/
noncomputable def butterflyMinusQuant {r : ℕ} (q : ℕ) (s : ℤ) (U V : Fin r → ℂ) : Fin r → ℂ :=
  fun k2 => quantizeComplex q ((U k2 - negacyclicShift s V k2) / 2)

/-- Even-index embedding `j ↦ 2 * j` from `Fin (2 ^ m)` into `Fin (2 ^ (m + 1))`. -/
def evenSubIndex (m : ℕ) (j : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  ⟨2 * j.val, by have := j.isLt; rw [Nat.pow_succ']; omega⟩

/-- Odd-index embedding `j ↦ 2 * j + 1` from `Fin (2 ^ m)` into `Fin (2 ^ (m + 1))`. -/
def oddSubIndex (m : ℕ) (j : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  ⟨2 * j.val + 1, by have := j.isLt; rw [Nat.pow_succ']; omega⟩

/-- Recursive $k_1$-stage radix-2 Cooley–Tukey polynomial-transform (`syntheticFFT`) butterfly network
over $\mathcal{R}_r$ in exact arithmetic (Lemma 3.5 (`lem:syn-fft`)). -/
noncomputable def radix2SyntheticFFTExact {r : ℕ} :
    (k1 : ℕ) → (c1 : ℕ) → (Fin (2 ^ k1) → Fin r → ℂ) → (Fin (2 ^ k1) → Fin r → ℂ)
  | 0, _c1, P => P
  | m + 1, c1, P =>
    let U := radix2SyntheticFFTExact m (2 * c1) (fun j => P (evenSubIndex m j))
    let V := radix2SyntheticFFTExact m (2 * c1) (fun j => P (oddSubIndex m j))
    fun v1 =>
      let u : Fin (2 ^ m) := ⟨v1.val % (2 ^ m), Nat.mod_lt _ (by positivity)⟩
      let s : ℤ := 2 * (c1 : ℤ) * (u.val : ℤ)
      if v1.val < 2 ^ m then
        butterflyPlusExact s (U u) (V u)
      else
        butterflyMinusExact s (U u) (V u)

/-- Recursive $k_1$-stage radix-2 Cooley–Tukey polynomial-transform (`syntheticFFT`) butterfly network
over $\mathcal{R}_r$ quantized at $q$ fractional bits after every butterfly stage (Lemma 3.5 (`lem:syn-fft`)). -/
noncomputable def radix2SyntheticFFTQuant {r : ℕ} (q : ℕ) :
    (k1 : ℕ) → (c1 : ℕ) → (Fin (2 ^ k1) → Fin r → ℂ) → (Fin (2 ^ k1) → Fin r → ℂ)
  | 0, _c1, P => P
  | m + 1, c1, P =>
    let U := radix2SyntheticFFTQuant q m (2 * c1) (fun j => P (evenSubIndex m j))
    let V := radix2SyntheticFFTQuant q m (2 * c1) (fun j => P (oddSubIndex m j))
    fun v1 =>
      let u : Fin (2 ^ m) := ⟨v1.val % (2 ^ m), Nat.mod_lt _ (by positivity)⟩
      let s : ℤ := 2 * (c1 : ℤ) * (u.val : ℤ)
      if v1.val < 2 ^ m then
        butterflyPlusQuant q s (U u) (V u)
      else
        butterflyMinusQuant q s (U u) (V u)

/-- Even/odd splitting of a sum over `Finset.range (2 * N)`. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ i ∈ Finset.range (2 * N), g i =
      ∑ i ∈ Finset.range N, g (2 * i) + ∑ i ∈ Finset.range N, g (2 * i + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    abel

/-- Even/odd splitting of a sum over `Fin (2 ^ (m + 1))`. -/
theorem sum_fin_pow_succ_even_odd {M : Type*} [AddCommMonoid M] (m : ℕ)
    (f : Fin (2 ^ (m + 1)) → M) :
    ∑ j1 : Fin (2 ^ (m + 1)), f j1 =
      ∑ j : Fin (2 ^ m), f (evenSubIndex m j) + ∑ j : Fin (2 ^ m), f (oddSubIndex m j) := by
  let g : ℕ → M := fun i => f ⟨i % 2 ^ (m + 1), Nat.mod_lt _ (by positivity)⟩
  have hj1 : ∀ j1 : Fin (2 ^ (m + 1)), f j1 = g j1.val := by
    intro j1
    dsimp [g]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt j1.isLt).symm
  have heven : ∀ j : Fin (2 ^ m), f (evenSubIndex m j) = g (2 * j.val) := by
    intro j
    dsimp [g]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt (evenSubIndex m j).isLt).symm
  have hodd : ∀ j : Fin (2 ^ m), f (oddSubIndex m j) = g (2 * j.val + 1) := by
    intro j
    dsimp [g]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt (oddSubIndex m j).isLt).symm
  have h1 : ∑ j1 : Fin (2 ^ (m + 1)), f j1 = ∑ j1 : Fin (2 ^ (m + 1)), g j1.val :=
    Finset.sum_congr rfl (fun j1 _ => hj1 j1)
  have h2 : ∑ j : Fin (2 ^ m), f (evenSubIndex m j) = ∑ j : Fin (2 ^ m), g (2 * j.val) :=
    Finset.sum_congr rfl (fun j _ => heven j)
  have h3 : ∑ j : Fin (2 ^ m), f (oddSubIndex m j) = ∑ j : Fin (2 ^ m), g (2 * j.val + 1) :=
    Finset.sum_congr rfl (fun j _ => hodd j)
  rw [h1, h2, h3]
  rw [Fin.sum_univ_eq_sum_range g (2 ^ (m + 1)),
    Fin.sum_univ_eq_sum_range (fun i => g (2 * i)) (2 ^ m),
    Fin.sum_univ_eq_sum_range (fun i => g (2 * i + 1)) (2 ^ m)]
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
  rw [hpow]
  exact sum_range_two_mul (2 ^ m) g

/-- Pointwise scalar multiplication for `negacyclicShift`. -/
theorem negacyclicShift_smul_apply {r : ℕ} (s : ℤ) (c : ℂ) (P : Fin r → ℂ) (k2 : Fin r) :
    negacyclicShift s (fun k => c * P k) k2 = c * negacyclicShift s P k2 := by
  unfold negacyclicShift
  ring

/-- `negacyclicShift` distributes over a finite sum of polynomials. -/
theorem negacyclicShift_sum {r : ℕ} {ι : Type*} (I : Finset ι) (s : ℤ)
    (f : ι → Fin r → ℂ) (k2 : Fin r) :
    negacyclicShift s (fun k => ∑ i ∈ I, f i k) k2 =
      ∑ i ∈ I, negacyclicShift s (f i) k2 := by
  unfold negacyclicShift
  simp [Finset.mul_sum]

/-- **Exactness of the $k_1$-Stage Radix-2 Polynomial-Transform Butterfly Network** (Lemma 3.5 (`lem:syn-fft`)):
When $2^{k_1} c_1 = r$, the $k_1$-stage radix-2 butterfly network `radix2SyntheticFFTExact k1 c1 P`
computes `syntheticFFT c1 P` exactly. -/
theorem radix2SyntheticFFTExact_eq_syntheticFFT {r : ℕ} (k1 : ℕ) :
    ∀ (c1 : ℕ) (_h_rc : 2 ^ k1 * c1 = r) (P : Fin (2 ^ k1) → Fin r → ℂ) (v1 : Fin (2 ^ k1)),
      radix2SyntheticFFTExact k1 c1 P v1 = syntheticFFT c1 P v1 := by
  induction k1 with
  | zero =>
    intro c1 _h_rc P v1
    funext k2
    change P v1 k2 = (((2 ^ 0 : ℕ) : ℝ)⁻¹ : ℂ) *
      ∑ j1 : Fin 1, negacyclicShift (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ)) (P j1) k2
    have hv1 : v1 = 0 := Fin.ext (by omega)
    subst hv1
    rw [Fin.sum_univ_one]
    simp [negacyclicShift_zero]
  | succ m ih =>
    intro c1 h_rc P v1
    have h_rc' : 2 ^ m * (2 * c1) = r := by
      calc
        2 ^ m * (2 * c1) = (2 * 2 ^ m) * c1 := by ring
        _ = 2 ^ (m + 1) * c1 := by rw [← Nat.pow_succ']
        _ = r := h_rc
    funext k2
    unfold radix2SyntheticFFTExact
    dsimp only
    set u : Fin (2 ^ m) := ⟨v1.val % (2 ^ m), Nat.mod_lt _ (by positivity)⟩
    set s : ℤ := 2 * (c1 : ℤ) * (u.val : ℤ)
    rw [ih (2 * c1) h_rc' (fun j => P (evenSubIndex m j)) u,
      ih (2 * c1) h_rc' (fun j => P (oddSubIndex m j)) u]
    unfold syntheticFFT
    rw [sum_fin_pow_succ_even_odd m]
    have h_pow_inv : (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹ : ℂ) =
        (((2 ^ m : ℕ) : ℝ)⁻¹ : ℂ) / 2 := by
      rw [Nat.pow_succ']
      push_cast
      ring
    split_ifs with hv1
    · have hu_val : v1.val = u.val := (Nat.mod_eq_of_lt hv1).symm
      unfold butterflyPlusExact
      rw [negacyclicShift_smul_apply, negacyclicShift_sum]
      have h_even : ∀ j : Fin (2 ^ m),
          negacyclicShift (2 * (c1 : ℤ) * ((evenSubIndex m j).val : ℤ) * (v1.val : ℤ))
            (P (evenSubIndex m j)) k2 =
          negacyclicShift (2 * ((2 * c1 : ℕ) : ℤ) * (j.val : ℤ) * (u.val : ℤ))
            (P (evenSubIndex m j)) k2 := by
        intro j
        have hs : 2 * (c1 : ℤ) * ((evenSubIndex m j).val : ℤ) * (v1.val : ℤ) =
            2 * ((2 * c1 : ℕ) : ℤ) * (j.val : ℤ) * (u.val : ℤ) := by
          rw [hu_val]
          simp only [evenSubIndex]
          push_cast
          ring
        rw [hs]
      have h_odd : ∀ j : Fin (2 ^ m),
          negacyclicShift (2 * (c1 : ℤ) * ((oddSubIndex m j).val : ℤ) * (v1.val : ℤ))
            (P (oddSubIndex m j)) k2 =
          negacyclicShift s
            (negacyclicShift (2 * ((2 * c1 : ℕ) : ℤ) * (j.val : ℤ) * (u.val : ℤ))
              (P (oddSubIndex m j))) k2 := by
        intro j
        rw [← negacyclicShift_add]
        have hs : 2 * (c1 : ℤ) * ((oddSubIndex m j).val : ℤ) * (v1.val : ℤ) =
            s + 2 * ((2 * c1 : ℕ) : ℤ) * (j.val : ℤ) * (u.val : ℤ) := by
          rw [hu_val]
          simp only [oddSubIndex, s]
          push_cast
          ring
        rw [hs]
      simp_rw [h_even, h_odd, h_pow_inv]
      ring
    · have hv1_ge : 2 ^ m ≤ v1.val := le_of_not_gt hv1
      have hv1_lt : v1.val < 2 * 2 ^ m := by
        have h1 := v1.isLt
        have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
        omega
      have hu_val : v1.val = u.val + 2 ^ m := by
        have h_mod : v1.val % (2 ^ m) = v1.val - 2 ^ m := by
          rw [Nat.mod_eq_sub_mod hv1_ge, Nat.mod_eq_of_lt (by omega)]
        change v1.val = v1.val % (2 ^ m) + 2 ^ m
        omega
      have hr_nat : 2 * c1 * 2 ^ m = r := by linarith [h_rc']
      have hr_int : (2 : ℤ) * (c1 : ℤ) * (2 : ℤ) ^ m = (r : ℤ) := by
        exact_mod_cast hr_nat
      unfold butterflyMinusExact
      rw [negacyclicShift_smul_apply, negacyclicShift_sum]
      have h_even : ∀ j : Fin (2 ^ m),
          negacyclicShift (2 * (c1 : ℤ) * ((evenSubIndex m j).val : ℤ) * (v1.val : ℤ))
            (P (evenSubIndex m j)) k2 =
          negacyclicShift (2 * ((2 * c1 : ℕ) : ℤ) * (j.val : ℤ) * (u.val : ℤ))
            (P (evenSubIndex m j)) k2 := by
        intro j
        have h_exp : 2 * (c1 : ℤ) * ((evenSubIndex m j).val : ℤ) * (v1.val : ℤ) =
            (2 * ((2 * c1 : ℕ) : ℤ) * (j.val : ℤ) * (u.val : ℤ)) +
              (j.val : ℤ) * (2 * (r : ℤ)) := by
          rw [hu_val]
          simp only [evenSubIndex]
          push_cast
          linear_combination (2 * (j.val : ℤ)) * hr_int
        rw [h_exp, negacyclicShift_add_mul_two_period]
      have h_odd : ∀ j : Fin (2 ^ m),
          negacyclicShift (2 * (c1 : ℤ) * ((oddSubIndex m j).val : ℤ) * (v1.val : ℤ))
            (P (oddSubIndex m j)) k2 =
          - negacyclicShift s
              (negacyclicShift (2 * ((2 * c1 : ℕ) : ℤ) * (j.val : ℤ) * (u.val : ℤ))
                (P (oddSubIndex m j))) k2 := by
        intro j
        have h_exp : 2 * (c1 : ℤ) * ((oddSubIndex m j).val : ℤ) * (v1.val : ℤ) =
            ((r : ℤ) + (s + 2 * ((2 * c1 : ℕ) : ℤ) * (j.val : ℤ) * (u.val : ℤ))) +
              (j.val : ℤ) * (2 * (r : ℤ)) := by
          rw [hu_val]
          simp only [oddSubIndex, s]
          push_cast
          linear_combination (2 * (j.val : ℤ) + 1) * hr_int
        rw [h_exp, negacyclicShift_add_mul_two_period, negacyclicShift_add,
          negacyclicShift_period]
        dsimp only
        rw [negacyclicShift_add]
      simp_rw [h_even, h_odd, Finset.sum_neg_distrib, h_pow_inv]
      ring

/-- Real floor-shifted quantization error: $|\text{quantizeReal } q \, x - x| \le \frac{1}{2} 2^{-q}$
(Section 3.2 (`sec:prelim-model`), equation (4) (`eq:quant-err`)). -/
theorem abs_quantizeReal_sub_le (q : ℕ) (x : ℝ) :
    |quantizeReal q x - x| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) :=
  abs_quantizeReal_sub_self_le q x

/-- Euclidean norm bound on a complex number from coordinate bounds (Section 3.2 (`sec:prelim-model`)). -/
theorem norm_complex_le_sqrt_two_mul_max (z : ℂ) {B : ℝ} (hre : |z.re| ≤ B) (him : |z.im| ≤ B) :
    ‖z‖ ≤ Real.sqrt 2 * B :=
  norm_complex_le_of_re_im_le ((abs_nonneg z.re).trans hre) hre him

/-- Complex quantization error at $q$ fractional bits:
$\|\text{quantizeComplex } q \, z - z\| \le \frac{\sqrt{2}}{2} 2^{-q}$
(Section 3.2 (`sec:prelim-model`), equation (4) (`eq:quant-err`)). -/
theorem norm_quantizeComplex_sub_le (q : ℕ) (z : ℂ) :
    ‖quantizeComplex q z - z‖ ≤ (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
  norm_quantizeComplex_sub_self_le q z

/-- One-stage error propagation for `butterflyPlusQuant` (Lemma 3.5 (`lem:syn-fft`)). -/
theorem vecInfNorm_butterflyPlusQuant_sub_le {r : ℕ} (q : ℕ) (s : ℤ)
    (U_q V_q U V : Fin r → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hU : vecInfNorm (fun k2 => U_q k2 - U k2) ≤ E)
    (hV : vecInfNorm (fun k2 => V_q k2 - V k2) ≤ E) :
    vecInfNorm (fun k2 => butterflyPlusQuant q s U_q V_q k2 - butterflyPlusExact s U V k2) ≤
      E + (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  apply vecInfNorm_le _ (add_nonneg hE (by positivity))
  intro k2
  unfold butterflyPlusQuant butterflyPlusExact
  set w_q : ℂ := (U_q k2 + negacyclicShift s V_q k2) / 2
  set w : ℂ := (U k2 + negacyclicShift s V k2) / 2
  have hw_diff : w_q - w =
      ((U_q k2 - U k2) + negacyclicShift s (fun j => V_q j - V j) k2) / 2 := by
    simp only [w_q, w, negacyclicShift_sub_poly]
    ring
  have hw_norm : ‖w_q - w‖ ≤ E := by
    rw [hw_diff, norm_div, RCLike.norm_ofNat]
    have h1 : ‖U_q k2 - U k2‖ ≤ E := (norm_le_vecInfNorm (fun j => U_q j - U j) k2).trans hU
    have h2 : ‖negacyclicShift s (fun j => V_q j - V j) k2‖ ≤ E := by
      have h_iso := norm_le_vecInfNorm (negacyclicShift s (fun j => V_q j - V j)) k2
      rw [vecInfNorm_negacyclicShift] at h_iso
      exact h_iso.trans hV
    have h3 : ‖(U_q k2 - U k2) + negacyclicShift s (fun j => V_q j - V j) k2‖ ≤ E + E :=
      (norm_add_le _ _).trans (add_le_add h1 h2)
    linarith
  calc
    ‖quantizeComplex q w_q - w‖ = ‖(w_q - w) + (quantizeComplex q w_q - w_q)‖ := by ring_nf
    _ ≤ ‖w_q - w‖ + ‖quantizeComplex q w_q - w_q‖ := norm_add_le _ _
    _ ≤ E + (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
      add_le_add hw_norm (norm_quantizeComplex_sub_le q w_q)

/-- One-stage error propagation for `butterflyMinusQuant` (Lemma 3.5 (`lem:syn-fft`)). -/
theorem vecInfNorm_butterflyMinusQuant_sub_le {r : ℕ} (q : ℕ) (s : ℤ)
    (U_q V_q U V : Fin r → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hU : vecInfNorm (fun k2 => U_q k2 - U k2) ≤ E)
    (hV : vecInfNorm (fun k2 => V_q k2 - V k2) ≤ E) :
    vecInfNorm (fun k2 => butterflyMinusQuant q s U_q V_q k2 - butterflyMinusExact s U V k2) ≤
      E + (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  apply vecInfNorm_le _ (add_nonneg hE (by positivity))
  intro k2
  unfold butterflyMinusQuant butterflyMinusExact
  set w_q : ℂ := (U_q k2 - negacyclicShift s V_q k2) / 2
  set w : ℂ := (U k2 - negacyclicShift s V k2) / 2
  have hw_diff : w_q - w =
      ((U_q k2 - U k2) - negacyclicShift s (fun j => V_q j - V j) k2) / 2 := by
    simp only [w_q, w, negacyclicShift_sub_poly]
    ring
  have hw_norm : ‖w_q - w‖ ≤ E := by
    rw [hw_diff, norm_div, RCLike.norm_ofNat]
    have h1 : ‖U_q k2 - U k2‖ ≤ E := (norm_le_vecInfNorm (fun j => U_q j - U j) k2).trans hU
    have h2 : ‖negacyclicShift s (fun j => V_q j - V j) k2‖ ≤ E := by
      have h_iso := norm_le_vecInfNorm (negacyclicShift s (fun j => V_q j - V j)) k2
      rw [vecInfNorm_negacyclicShift] at h_iso
      exact h_iso.trans hV
    have h3 : ‖(U_q k2 - U k2) - negacyclicShift s (fun j => V_q j - V j) k2‖ ≤ E + E :=
      (norm_sub_le _ _).trans (add_le_add h1 h2)
    linarith
  calc
    ‖quantizeComplex q w_q - w‖ = ‖(w_q - w) + (quantizeComplex q w_q - w_q)‖ := by ring_nf
    _ ≤ ‖w_q - w‖ + ‖quantizeComplex q w_q - w_q‖ := norm_add_le _ _
    _ ≤ E + (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
      add_le_add hw_norm (norm_quantizeComplex_sub_le q w_q)

/-- **$k_1$-Stage Quantized Polynomial-Transform Error Bound at Precision $q$** (Lemma 3.5 (`lem:syn-fft`)):
Across $k_1$ radix-2 butterfly stages over $\mathcal{R}_r$, each stage adds at most
$\frac{\sqrt{2}}{2} 2^{-q}$ in $\ell_\infty$ norm without amplifying prior stage errors. -/
theorem vecInfNorm_radix2SyntheticFFTQuant_sub_exact_le {r : ℕ} (q k1 : ℕ) :
    ∀ (c1 : ℕ) (P : Fin (2 ^ k1) → Fin r → ℂ) (v1 : Fin (2 ^ k1)),
      vecInfNorm (fun k2 =>
        radix2SyntheticFFTQuant q k1 c1 P v1 k2 -
          radix2SyntheticFFTExact k1 c1 P v1 k2) ≤
        (k1 : ℝ) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  induction k1 with
  | zero =>
    intro c1 P v1
    unfold radix2SyntheticFFTQuant radix2SyntheticFFTExact
    simp only [sub_self, Nat.cast_zero, zero_mul]
    apply vecInfNorm_le _ le_rfl
    intro k2
    simp
  | succ m ih =>
    intro c1 P v1
    unfold radix2SyntheticFFTQuant radix2SyntheticFFTExact
    dsimp only
    set u : Fin (2 ^ m) := ⟨v1.val % (2 ^ m), Nat.mod_lt _ (by positivity)⟩
    set s : ℤ := 2 * (c1 : ℤ) * (u.val : ℤ)
    have hE_nonneg : 0 ≤ (m : ℝ) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by positivity
    have hU := ih (2 * c1) (fun j => P (evenSubIndex m j)) u
    have hV := ih (2 * c1) (fun j => P (oddSubIndex m j)) u
    have h_step :
        (m : ℝ) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) +
          (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) =
        ((m + 1 : ℕ) : ℝ) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
      push_cast; ring
    split_ifs with hv1
    · rw [← h_step]
      exact vecInfNorm_butterflyPlusQuant_sub_le q s _ _ _ _ hE_nonneg hU hV
    · rw [← h_step]
      exact vecInfNorm_butterflyMinusQuant_sub_le q s _ _ _ _ hE_nonneg hU hV

/-- Numerical constant bound $\frac{\sqrt{2}}{8} \le 0.18$ used in Lemma 3.5 (`lem:syn-fft`) (derived from
`IntMul.sqrt_two_div_eight_le` in `IntMul.FixedPoint`). -/
theorem sqrt_two_div_eight_le_018 : Real.sqrt 2 / 8 ≤ (0.18 : ℝ) := by
  linarith [sqrt_two_div_eight_le]

/-- **Lemma 3.5 (`lem:syn-fft`) (Per-Stage Rounding Error of the Radix-2 Polynomial Transform $G_{t_1}$,
Section 3.5 (`sec:prelim-dft`), equation (13) (`eq:syn-err`), Table 3 (`tab:lean-map`))**:
At precision $q = p_{\ell+1} + 2$ with $k_1 = \lfloor K_\ell / 2 \rfloor = \text{k1Ell } K_\ell$
and $2^{k_1} c_1 = r$, the quantized $k_1$-stage radix-2 polynomial transform (`radix2SyntheticFFTQuant`)
over $\mathcal{R}_r$ accumulates a total $\ell_\infty$ rounding error of at most
$$k_1 \frac{\sqrt{2}}{4} 2^{-p_{\ell+1}} \le 0.18 K_\ell 2^{-p_{\ell+1}}.$$ -/
theorem syntheticFFT_rounding_error_le {r : ℕ} (K pChild c1 : ℕ)
    (h_rc : 2 ^ k1Ell K * c1 = r)
    (P : Fin (2 ^ k1Ell K) → Fin r → ℂ) (v1 : Fin (2 ^ k1Ell K)) :
    vecInfNorm (fun k2 =>
      radix2SyntheticFFTQuant (pChild + 2) (k1Ell K) c1 P v1 k2 -
        syntheticFFT c1 P v1 k2) ≤
      (k1Ell K : ℝ) * ((Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(pChild : ℤ))) ∧
    (k1Ell K : ℝ) * ((Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(pChild : ℤ))) ≤
      (0.18 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
  have h_exact := radix2SyntheticFFTExact_eq_syntheticFFT (k1Ell K) c1 h_rc P v1
  have h_quant :=
    vecInfNorm_radix2SyntheticFFTQuant_sub_exact_le (pChild + 2) (k1Ell K) c1 P v1
  rw [h_exact] at h_quant
  have h_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
  have h_pow_le : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-((pChild + 2 : ℕ) : ℤ)) ≤
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
    have h_exp : -((pChild + 2 : ℕ) : ℤ) = -(pChild : ℤ) + (-2 : ℤ) := by push_cast; ring
    have h_zpow2 : (2 : ℝ) ^ (-2 : ℤ) = (1 / 4 : ℝ) := by norm_num
    rw [h_exp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h_zpow2]
    have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith
  have h_quant' :
      vecInfNorm (fun k2 =>
        radix2SyntheticFFTQuant (pChild + 2) (k1Ell K) c1 P v1 k2 -
          syntheticFFT c1 P v1 k2) ≤
        (k1Ell K : ℝ) * ((Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(pChild : ℤ))) :=
    h_quant.trans (mul_le_mul_of_nonneg_left h_pow_le (Nat.cast_nonneg _))
  refine ⟨h_quant', ?_⟩
  have hk1_le : (k1Ell K : ℝ) ≤ (K : ℝ) / 2 := by
    unfold k1Ell
    have h_div : 2 * (K / 2) ≤ K := Nat.mul_div_le K 2
    have h_div_real : (2 : ℝ) * ((K / 2 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h_div
    linarith
  have h_sqrt : Real.sqrt 2 / 8 ≤ (0.18 : ℝ) := sqrt_two_div_eight_le_018
  calc
    (k1Ell K : ℝ) * ((Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(pChild : ℤ)))
      ≤ ((K : ℝ) / 2) * ((Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(pChild : ℤ))) := by gcongr
    _ = (Real.sqrt 2 / 8) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by ring
    _ ≤ (0.18 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by gcongr

/-- **1D Inverse DFT Reconstruction for `normDFT1DNeg`**:
$$\sum_{u : \text{Fin } R} (F_R^{-} x)_u e^{2\pi i u k / R} = x_k.$$ -/
theorem sum_normDFT1DNeg_mul_expTwoPiI {R : ℕ} (x : Fin R → ℂ) (k : Fin R) :
    ∑ u : Fin R,
      normDFT1DNeg x u * expTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ)) = x k := by
  have h := sum_normDFT1D_mul_expNegTwoPiI (fun j => conj (x j)) k
  apply_fun conj at h
  rw [map_sum] at h
  have h_lhs :
      ∑ u : Fin R, conj (normDFT1D (fun j => conj (x j)) u *
        expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ))) =
      ∑ u : Fin R,
        normDFT1DNeg x u * expTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R : ℝ)) := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [map_mul, conj_expNegTwoPiI]
    congr 1
    unfold normDFT1D normDFT1DNeg
    rw [map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, conj_expTwoPiI, Nat.mul_comm]
  rw [← h_lhs, h, RingHomCompTriple.comp_apply, RingHom.id_apply]

/-- Stride-$t_1$ input polynomial family $P_{j_1}(k_2) = x(j_1 + k_2 t_1)$ (Section 4.2 (`sec:poisson`), Section 6.2 (`sec:kronecker`)). -/
def inputPolyFamily {t1 r : ℕ} (x : Fin (t1 * r) → ℂ) (j1 : Fin t1) (k2 : Fin r) : ℂ :=
  x ⟨j1.val + k2.val * t1, by
    calc
      j1.val + k2.val * t1 < t1 + k2.val * t1 := Nat.add_lt_add_right j1.isLt (k2.val * t1)
      _ = (k2.val + 1) * t1 := by ring
      _ ≤ r * t1 := Nat.mul_le_mul_right t1 (Nat.succ_le_of_lt k2.isLt)
      _ = t1 * r := Nat.mul_comm r t1⟩

/-- Quantized pre-twist at $q$ fractional bits (Proposition 4.1 (`thm:twisted`), Step 1, Section 7.1 (`sec:alg-spec`)). -/
noncomputable def preTwistQuant {r : ℕ} (q : ℕ) (P : Fin r → ℂ) (k2 : Fin r) : ℂ :=
  quantizeComplex q (zetaPow r (k2.val : ℤ) * P k2)

/-- Quantized post-twist at $q$ fractional bits (Proposition 4.1 (`thm:twisted`), Step 3, Section 7.1 (`sec:alg-spec`)). -/
noncomputable def postTwistQuant {r : ℕ} (q : ℕ) (Q : Fin r → ℂ) (k2 : Fin r) : ℂ :=
  quantizeComplex q (zetaPow r (-(k2.val : ℤ)) * Q k2)

/-- Error bound for `preTwistQuant` with approximate input `P_q`:
$\|\text{preTwistQuant } q \, P_q - \text{preTwist } P\|_\infty \le \|P_q - P\|_\infty + \frac{\sqrt{2}}{2} 2^{-q}$. -/
theorem vecInfNorm_preTwistQuant_sub_le {r : ℕ} (q : ℕ) (P_q P : Fin r → ℂ) :
    vecInfNorm (fun k2 => preTwistQuant q P_q k2 - preTwist P k2) ≤
      vecInfNorm (fun k2 => P_q k2 - P k2) + (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  apply vecInfNorm_le _ (add_nonneg (vecInfNorm_nonneg _) (by positivity))
  intro k2
  unfold preTwistQuant preTwist
  set w_q : ℂ := zetaPow r (k2.val : ℤ) * P_q k2
  set w : ℂ := zetaPow r (k2.val : ℤ) * P k2
  have hw_norm : ‖w_q - w‖ ≤ vecInfNorm (fun j => P_q j - P j) := by
    have h_sub : w_q - w = zetaPow r (k2.val : ℤ) * (P_q k2 - P k2) := by
      simp only [w_q, w]; ring
    rw [h_sub, norm_mul, norm_zetaPow, one_mul]
    exact norm_le_vecInfNorm (fun j => P_q j - P j) k2
  calc
    ‖quantizeComplex q w_q - w‖ = ‖(w_q - w) + (quantizeComplex q w_q - w_q)‖ := by ring_nf
    _ ≤ ‖w_q - w‖ + ‖quantizeComplex q w_q - w_q‖ := norm_add_le _ _
    _ ≤ vecInfNorm (fun j => P_q j - P j) + (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
      add_le_add hw_norm (norm_quantizeComplex_sub_le q w_q)

/-- Error bound for `postTwistQuant` with approximate input `Q_q`:
$\|\text{postTwistQuant } q \, Q_q - \text{postTwist } Q\|_\infty \le \|Q_q - Q\|_\infty + \frac{\sqrt{2}}{2} 2^{-q}$. -/
theorem vecInfNorm_postTwistQuant_sub_le {r : ℕ} (q : ℕ) (Q_q Q : Fin r → ℂ) :
    vecInfNorm (fun k2 => postTwistQuant q Q_q k2 - postTwist Q k2) ≤
      vecInfNorm (fun k2 => Q_q k2 - Q k2) + (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  apply vecInfNorm_le _ (add_nonneg (vecInfNorm_nonneg _) (by positivity))
  intro k2
  unfold postTwistQuant postTwist
  set w_q : ℂ := zetaPow r (-(k2.val : ℤ)) * Q_q k2
  set w : ℂ := zetaPow r (-(k2.val : ℤ)) * Q k2
  have hw_norm : ‖w_q - w‖ ≤ vecInfNorm (fun j => Q_q j - Q j) := by
    have h_sub : w_q - w = zetaPow r (-(k2.val : ℤ)) * (Q_q k2 - Q k2) := by
      simp only [w_q, w]; ring
    rw [h_sub, norm_mul, norm_zetaPow, one_mul]
    exact norm_le_vecInfNorm (fun j => Q_q j - Q j) k2
  calc
    ‖quantizeComplex q w_q - w‖ = ‖(w_q - w) + (quantizeComplex q w_q - w_q)‖ := by ring_nf
    _ ≤ ‖w_q - w‖ + ‖quantizeComplex q w_q - w_q‖ := norm_add_le _ _
    _ ≤ vecInfNorm (fun j => Q_q j - Q j) + (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
      add_le_add hw_norm (norm_quantizeComplex_sub_le q w_q)

/-! ### Quantized Twist Roots (`zetaPowQuant`, `preTwistQuantRoots`, `postTwistQuantRoots`, Section 6.3 (`sec:forward-error`)) -/

/-- Exact matrix pre-twist $(j_1, k_2) \mapsto \zeta^{k_2} P_{j_1, k_2}$ (Proposition 4.1 (`thm:twisted`), Step 1). -/
noncomputable abbrev preTwistExact {t1 r : ℕ} (P : Fin t1 → Fin r → ℂ)
    (j1 : Fin t1) (k2 : Fin r) : ℂ :=
  preTwist (P j1) k2

/-- Exact matrix post-twist $(v_1, k_2) \mapsto \zeta^{-k_2} Q_{v_1, k_2}$ (Proposition 4.1 (`thm:twisted`), Step 3). -/
noncomputable abbrev postTwistExact {t1 r : ℕ} (Q : Fin t1 → Fin r → ℂ)
    (v1 : Fin t1) (k2 : Fin r) : ℂ :=
  postTwist (Q v1) k2

/-- $2r$-th root of unity power $\zeta^m$ quantized to $q$ fractional bits in $\tilde{\mathbb{C}}_q$
(Section 3.3 (`sec:tables`), Lemma 6.5 (`lem:forward`)). -/
noncomputable def zetaPowQuant (q r : ℕ) (m : ℤ) : ℂ :=
  quantizeComplex q (zetaPow r m)

/-- Matrix pre-twist with $q$-bit quantized twist roots $\tilde{\zeta}^{k_2}$ followed by $q$-bit
quantization (Lemma 6.5 (`lem:forward`), Section 7.1 (`sec:alg-spec`), Listing 1 (`lst:multiply`)). -/
noncomputable def preTwistQuantRoots (q : ℕ) {t1 r : ℕ} (P : Fin t1 → Fin r → ℂ)
    (j1 : Fin t1) (k2 : Fin r) : ℂ :=
  quantizeComplex q (zetaPowQuant q r (k2.val : ℤ) * P j1 k2)

/-- Matrix post-twist with $q$-bit quantized twist roots $\tilde{\zeta}^{-k_2}$ followed by $q$-bit
quantization (Lemma 6.5 (`lem:forward`), Section 7.1 (`sec:alg-spec`), Listing 1 (`lst:multiply`)). -/
noncomputable def postTwistQuantRoots (q : ℕ) {t1 r : ℕ} (Q : Fin t1 → Fin r → ℂ)
    (v1 : Fin t1) (k2 : Fin r) : ℂ :=
  quantizeComplex q (zetaPowQuant q r (-(k2.val : ℤ)) * Q v1 k2)

/-- Rounding error of a quantized twist root:
$\|\text{zetaPowQuant } q \, r \, m - \text{zetaPow } r \, m\| \le \frac{\sqrt{2}}{2} 2^{-q}$. -/
theorem norm_zetaPowQuant_sub_zetaPow_le (q r : ℕ) (m : ℤ) :
    ‖zetaPowQuant q r m - zetaPow r m‖ ≤ (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
  norm_quantizeComplex_sub_self_le q (zetaPow r m)

/-- Fixed-point complex multiplication `FixedComplex.mulRounded` by the quantized root
`quantizeComplexFixed q (zetaPow r k2)` matches `preTwistQuantRoots`. -/
theorem toComplex_mulRounded_zetaPow_eq_preTwistQuantRoots (q : ℕ) {t1 r : ℕ}
    (P : Fin t1 → Fin r → FixedComplex q) (j1 : Fin t1) (k2 : Fin r) :
    (FixedComplex.mulRounded (quantizeComplexFixed q (zetaPow r (k2.val : ℤ))) (P j1 k2)).toComplex =
      preTwistQuantRoots q (fun i1 i2 => (P i1 i2).toComplex) j1 k2 := by
  rw [FixedComplex.toComplex_mulRounded]
  rfl

/-- Fixed-point complex multiplication `FixedComplex.mulRounded` by the quantized inverse root
`quantizeComplexFixed q (zetaPow r (-k2))` matches `postTwistQuantRoots`. -/
theorem toComplex_mulRounded_zetaPow_eq_postTwistQuantRoots (q : ℕ) {t1 r : ℕ}
    (Q : Fin t1 → Fin r → FixedComplex q) (v1 : Fin t1) (k2 : Fin r) :
    (FixedComplex.mulRounded (quantizeComplexFixed q (zetaPow r (-(k2.val : ℤ)))) (Q v1 k2)).toComplex =
      postTwistQuantRoots q (fun i1 i2 => (Q i1 i2).toComplex) v1 k2 := by
  rw [FixedComplex.toComplex_mulRounded]
  rfl

/-- Pointwise rounding error bound for `preTwistQuantRoots` with approximate input `P_q`. -/
theorem norm_preTwistQuantRoots_sub_le (q : ℕ) {t1 r : ℕ}
    (P_q P : Fin t1 → Fin r → ℂ) (j1 : Fin t1) (k2 : Fin r) :
    ‖preTwistQuantRoots q P_q j1 k2 - preTwistExact P j1 k2‖ ≤
      ‖P_q j1 k2 - P j1 k2‖ +
        (1 + ‖P_q j1 k2‖) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  unfold preTwistQuantRoots preTwistExact preTwist
  set z_q : ℂ := zetaPowQuant q r (k2.val : ℤ)
  set z : ℂ := zetaPow r (k2.val : ℤ)
  set w_q : ℂ := z_q * P_q j1 k2
  set w : ℂ := z * P j1 k2
  have h_decomp : w_q - w = z * (P_q j1 k2 - P j1 k2) + (z_q - z) * P_q j1 k2 := by
    simp only [w_q, w]; ring
  have hw_diff :
      ‖w_q - w‖ ≤ ‖P_q j1 k2 - P j1 k2‖ +
        ‖P_q j1 k2‖ * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
    rw [h_decomp]
    calc
      ‖z * (P_q j1 k2 - P j1 k2) + (z_q - z) * P_q j1 k2‖
        ≤ ‖z * (P_q j1 k2 - P j1 k2)‖ + ‖(z_q - z) * P_q j1 k2‖ := norm_add_le _ _
      _ = ‖P_q j1 k2 - P j1 k2‖ + ‖z_q - z‖ * ‖P_q j1 k2‖ := by
        rw [norm_mul, norm_zetaPow, one_mul, norm_mul]
      _ ≤ ‖P_q j1 k2 - P j1 k2‖ +
          ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) * ‖P_q j1 k2‖ := by
        gcongr
        exact norm_zetaPowQuant_sub_zetaPow_le q r (k2.val : ℤ)
      _ = ‖P_q j1 k2 - P j1 k2‖ +
          ‖P_q j1 k2‖ * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by ring
  calc
    ‖quantizeComplex q w_q - w‖ = ‖(w_q - w) + (quantizeComplex q w_q - w_q)‖ := by ring_nf
    _ ≤ ‖w_q - w‖ + ‖quantizeComplex q w_q - w_q‖ := norm_add_le _ _
    _ ≤ (‖P_q j1 k2 - P j1 k2‖ +
          ‖P_q j1 k2‖ * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)))) +
        (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
      add_le_add hw_diff (norm_quantizeComplex_sub_self_le q w_q)
    _ = ‖P_q j1 k2 - P j1 k2‖ +
        (1 + ‖P_q j1 k2‖) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by ring

/-- Pointwise rounding error bound for `postTwistQuantRoots` with approximate input `Q_q`. -/
theorem norm_postTwistQuantRoots_sub_le (q : ℕ) {t1 r : ℕ}
    (Q_q Q : Fin t1 → Fin r → ℂ) (v1 : Fin t1) (k2 : Fin r) :
    ‖postTwistQuantRoots q Q_q v1 k2 - postTwistExact Q v1 k2‖ ≤
      ‖Q_q v1 k2 - Q v1 k2‖ +
        (1 + ‖Q_q v1 k2‖) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  unfold postTwistQuantRoots postTwistExact postTwist
  set z_q : ℂ := zetaPowQuant q r (-(k2.val : ℤ))
  set z : ℂ := zetaPow r (-(k2.val : ℤ))
  set w_q : ℂ := z_q * Q_q v1 k2
  set w : ℂ := z * Q v1 k2
  have h_decomp : w_q - w = z * (Q_q v1 k2 - Q v1 k2) + (z_q - z) * Q_q v1 k2 := by
    simp only [w_q, w]; ring
  have hw_diff :
      ‖w_q - w‖ ≤ ‖Q_q v1 k2 - Q v1 k2‖ +
        ‖Q_q v1 k2‖ * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
    rw [h_decomp]
    calc
      ‖z * (Q_q v1 k2 - Q v1 k2) + (z_q - z) * Q_q v1 k2‖
        ≤ ‖z * (Q_q v1 k2 - Q v1 k2)‖ + ‖(z_q - z) * Q_q v1 k2‖ := norm_add_le _ _
      _ = ‖Q_q v1 k2 - Q v1 k2‖ + ‖z_q - z‖ * ‖Q_q v1 k2‖ := by
        rw [norm_mul, norm_zetaPow, one_mul, norm_mul]
      _ ≤ ‖Q_q v1 k2 - Q v1 k2‖ +
          ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) * ‖Q_q v1 k2‖ := by
        gcongr
        exact norm_zetaPowQuant_sub_zetaPow_le q r (-(k2.val : ℤ))
      _ = ‖Q_q v1 k2 - Q v1 k2‖ +
          ‖Q_q v1 k2‖ * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by ring
  calc
    ‖quantizeComplex q w_q - w‖ = ‖(w_q - w) + (quantizeComplex q w_q - w_q)‖ := by ring_nf
    _ ≤ ‖w_q - w‖ + ‖quantizeComplex q w_q - w_q‖ := norm_add_le _ _
    _ ≤ (‖Q_q v1 k2 - Q v1 k2‖ +
          ‖Q_q v1 k2‖ * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)))) +
        (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
      add_le_add hw_diff (norm_quantizeComplex_sub_self_le q w_q)
    _ = ‖Q_q v1 k2 - Q v1 k2‖ +
        (1 + ‖Q_q v1 k2‖) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by ring

/-- Row-level $\ell_\infty$ error bound for `preTwistQuantRoots` with approximate input `P_q`. -/
theorem vecInfNorm_preTwistQuantRoots_sub_le (q : ℕ) {t1 r : ℕ}
    (P_q P : Fin t1 → Fin r → ℂ) (j1 : Fin t1) :
    vecInfNorm (fun k2 => preTwistQuantRoots q P_q j1 k2 - preTwistExact P j1 k2) ≤
      vecInfNorm (fun k2 => P_q j1 k2 - P j1 k2) +
        (1 + vecInfNorm (P_q j1)) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have h_rhs_nn : 0 ≤ vecInfNorm (fun k2 => P_q j1 k2 - P j1 k2) +
      (1 + vecInfNorm (P_q j1)) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
    have := vecInfNorm_nonneg (fun k2 => P_q j1 k2 - P j1 k2)
    have := vecInfNorm_nonneg (P_q j1)
    positivity
  apply vecInfNorm_le _ h_rhs_nn
  intro k2
  calc
    ‖preTwistQuantRoots q P_q j1 k2 - preTwistExact P j1 k2‖
      ≤ ‖P_q j1 k2 - P j1 k2‖ +
          (1 + ‖P_q j1 k2‖) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) :=
        norm_preTwistQuantRoots_sub_le q P_q P j1 k2
    _ ≤ vecInfNorm (fun j => P_q j1 j - P j1 j) +
          (1 + vecInfNorm (P_q j1)) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
        gcongr
        · exact norm_le_vecInfNorm (fun j => P_q j1 j - P j1 j) k2
        · exact norm_le_vecInfNorm (P_q j1) k2

/-- Row-level $\ell_\infty$ error bound for `postTwistQuantRoots` with approximate input `Q_q`. -/
theorem vecInfNorm_postTwistQuantRoots_sub_le (q : ℕ) {t1 r : ℕ}
    (Q_q Q : Fin t1 → Fin r → ℂ) (v1 : Fin t1) :
    vecInfNorm (fun k2 => postTwistQuantRoots q Q_q v1 k2 - postTwistExact Q v1 k2) ≤
      vecInfNorm (fun k2 => Q_q v1 k2 - Q v1 k2) +
        (1 + vecInfNorm (Q_q v1)) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have h_rhs_nn : 0 ≤ vecInfNorm (fun k2 => Q_q v1 k2 - Q v1 k2) +
      (1 + vecInfNorm (Q_q v1)) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
    have := vecInfNorm_nonneg (fun k2 => Q_q v1 k2 - Q v1 k2)
    have := vecInfNorm_nonneg (Q_q v1)
    positivity
  apply vecInfNorm_le _ h_rhs_nn
  intro k2
  calc
    ‖postTwistQuantRoots q Q_q v1 k2 - postTwistExact Q v1 k2‖
      ≤ ‖Q_q v1 k2 - Q v1 k2‖ +
          (1 + ‖Q_q v1 k2‖) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) :=
        norm_postTwistQuantRoots_sub_le q Q_q Q v1 k2
    _ ≤ vecInfNorm (fun j => Q_q v1 j - Q v1 j) +
          (1 + vecInfNorm (Q_q v1)) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
        gcongr
        · exact norm_le_vecInfNorm (fun j => Q_q v1 j - Q v1 j) k2
        · exact norm_le_vecInfNorm (Q_q v1) k2

/-- Matrix $\ell_\infty$ error bound for `preTwistQuantRoots` with approximate input `P_q`. -/
theorem matInfNorm_preTwistQuantRoots_sub_le (q : ℕ) {t1 r : ℕ}
    (P_q P : Fin t1 → Fin r → ℂ) :
    matInfNorm (fun j1 k2 => preTwistQuantRoots q P_q j1 k2 - preTwistExact P j1 k2) ≤
      matInfNorm (fun j1 k2 => P_q j1 k2 - P j1 k2) +
        (1 + matInfNorm P_q) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have h_rhs_nn : 0 ≤ matInfNorm (fun j1 k2 => P_q j1 k2 - P j1 k2) +
      (1 + matInfNorm P_q) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
    have := matInfNorm_nonneg (fun j1 k2 => P_q j1 k2 - P j1 k2)
    have := matInfNorm_nonneg P_q
    positivity
  apply matInfNorm_le _ h_rhs_nn
  intro j1 k2
  calc
    ‖preTwistQuantRoots q P_q j1 k2 - preTwistExact P j1 k2‖
      ≤ ‖P_q j1 k2 - P j1 k2‖ +
          (1 + ‖P_q j1 k2‖) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) :=
        norm_preTwistQuantRoots_sub_le q P_q P j1 k2
    _ ≤ matInfNorm (fun i1 i2 => P_q i1 i2 - P i1 i2) +
          (1 + matInfNorm P_q) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
        gcongr
        · exact norm_le_matInfNorm (fun i1 i2 => P_q i1 i2 - P i1 i2) j1 k2
        · exact norm_le_matInfNorm P_q j1 k2

/-- Matrix $\ell_\infty$ error bound for `postTwistQuantRoots` with approximate input `Q_q`. -/
theorem matInfNorm_postTwistQuantRoots_sub_le (q : ℕ) {t1 r : ℕ}
    (Q_q Q : Fin t1 → Fin r → ℂ) :
    matInfNorm (fun v1 k2 => postTwistQuantRoots q Q_q v1 k2 - postTwistExact Q v1 k2) ≤
      matInfNorm (fun v1 k2 => Q_q v1 k2 - Q v1 k2) +
        (1 + matInfNorm Q_q) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have h_rhs_nn : 0 ≤ matInfNorm (fun v1 k2 => Q_q v1 k2 - Q v1 k2) +
      (1 + matInfNorm Q_q) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
    have := matInfNorm_nonneg (fun v1 k2 => Q_q v1 k2 - Q v1 k2)
    have := matInfNorm_nonneg Q_q
    positivity
  apply matInfNorm_le _ h_rhs_nn
  intro v1 k2
  calc
    ‖postTwistQuantRoots q Q_q v1 k2 - postTwistExact Q v1 k2‖
      ≤ ‖Q_q v1 k2 - Q v1 k2‖ +
          (1 + ‖Q_q v1 k2‖) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) :=
        norm_postTwistQuantRoots_sub_le q Q_q Q v1 k2
    _ ≤ matInfNorm (fun i1 i2 => Q_q i1 i2 - Q i1 i2) +
          (1 + matInfNorm Q_q) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
        gcongr
        · exact norm_le_matInfNorm (fun i1 i2 => Q_q i1 i2 - Q i1 i2) v1 k2
        · exact norm_le_matInfNorm Q_q v1 k2

/-- **Quantized Twist-Root Pre-Twist Error Bound (`matInfNorm_preTwistQuantRoots_sub_preTwistExact_le`,
Section 6.3 (`sec:forward-error`), Lemma 6.5 (`lem:forward`))**:
Quantizing the twist roots $\zeta^{k_2}$ to $q$ bits before multiplying by $P_{j_1, k_2}$ and
quantizing the product to $q$ bits incurs matrix $\ell_\infty$ error at most
$(1 + \|P\|_\infty) \frac{\sqrt{2}}{2} 2^{-q}$. -/
theorem matInfNorm_preTwistQuantRoots_sub_preTwistExact_le (q : ℕ) {t1 r : ℕ}
    (P : Fin t1 → Fin r → ℂ) :
    matInfNorm (fun j1 k2 => preTwistQuantRoots q P j1 k2 - preTwistExact P j1 k2) ≤
      (1 + matInfNorm P) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  have h := matInfNorm_preTwistQuantRoots_sub_le q P P
  have h0 : matInfNorm (fun j1 k2 => P j1 k2 - P j1 k2) = 0 := by
    apply le_antisymm _ (matInfNorm_nonneg _)
    apply matInfNorm_le _ le_rfl
    intro j1 k2
    simp
  linarith

/-- **Quantized Twist-Root Post-Twist Error Bound (`matInfNorm_postTwistQuantRoots_sub_postTwistExact_le`,
Section 6.3 (`sec:forward-error`), Lemma 6.5 (`lem:forward`))**:
Quantizing the inverse twist roots $\zeta^{-k_2}$ to $q$ bits before multiplying by $Q_{v_1, k_2}$
and quantizing the product to $q$ bits incurs matrix $\ell_\infty$ error at most
$(1 + \|Q\|_\infty) \frac{\sqrt{2}}{2} 2^{-q}$. -/
theorem matInfNorm_postTwistQuantRoots_sub_postTwistExact_le (q : ℕ) {t1 r : ℕ}
    (Q : Fin t1 → Fin r → ℂ) :
    matInfNorm (fun v1 k2 => postTwistQuantRoots q Q v1 k2 - postTwistExact Q v1 k2) ≤
      (1 + matInfNorm Q) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) := by
  have h := matInfNorm_postTwistQuantRoots_sub_le q Q Q
  have h0 : matInfNorm (fun v1 k2 => Q v1 k2 - Q v1 k2) = 0 := by
    apply le_antisymm _ (matInfNorm_nonneg _)
    apply matInfNorm_le _ le_rfl
    intro v1 k2
    simp
  linarith

/-! ## 7. Subring Decomposition & Restricted-Model Barrier Identities

This part retains the radix-$B$ subring decomposition and algebraic barrier identities from an
earlier draft (omitted from the published paper; see Section 10 (`sec:discussion`) for discussion
of the remaining $\Theta(n \log n)$ polynomial-transform and tape-routing term):
1. **Radix-$B$ subring decomposition (`radixBSyntheticButterfly_coset_decomposition`,
   `radixB_interStage_twiddle_ops_le`)**:
   Canonical coset decomposition of radix-$B$ ($B = 2 B_{\text{half}}$) polynomial-transform
   (`syntheticFFT`) butterflies over $\mathcal{R}_r = \mathbb{C}[y]/(y^r + 1)$ ($r = B_{\text{half}} \cdot d$,
   $d = 2r/B$) into $d$ independent, shift-free copies of the fixed $\pm 1$ operator $\mathcal{M}_B$ over
   $\mathcal{R}_{B/2} = \mathbb{C}[z]/(z^{B/2} + 1)$, corresponding to
   Theorem 6 of an earlier draft (restricted-model section, not in the published paper).
2. **Bit-slice range expansion and overlap (`abs_decoupledSubringOperatorInt_le`,
   `decoupledSubringOperatorInt_const_zero`, `bitSlice_output_exceeds_slice_width`,
   `bitSliceAccumulationOps_decomp`)**:
   Bit-slice output range expansion ($[-B(2^s-1), B(2^s-1)]$, strictly exceeding $2^s$) and
   slice accumulation bit-operation identity.
3. **Sub-word packet transposition potential (`floydPotential_init_eq_zero`,
   `floydPotential_final_eq`, `floyd_transpose_step_lower_bound`)**:
   Floyd's discrete entropy potential $\Phi = \sum_{i,j} a_{i,j} \lfloor \log_2 a_{i,j} \rfloor$
   for $B \times B$ sub-word packet transposition ($\Phi_{\text{init}} = 0$,
   $\Phi_{\text{final}} = k B^2$ for $B = 2^k$), forcing $\Omega(k B)$ register operations per $B$
   registers and $\Omega(\log_2 t_1)$ operations per register across all $(\log_2 t_1)/k$ stages.
4. **Kronecker packing bit-width comparison (`kronecker_conv_ops_gt_addition_butterfly`)**:
   Packing $\mathcal{M}_B$ into a Kronecker integer of bit-length $N_B (2p + 2k)$ strictly
   exceeds the $k N_B p$ addition-only radix-2 butterfly cost.
5. **Chunk-reduction telescoping (`chunk_telescoping_conservation_lower_bound`)**:
   Telescoping conservation lower bound across any chain of super-logarithmic chunk reductions
   $b_0 > b_1 > \dots > b_m$.
6. **Negacyclic shift order and stage-count telescoping (`negacyclicShift_order_two_mul_r`,
   `butterfly_stage_sum_telescoping_invariance`)**:
   Exact multiplicative order $\operatorname{ord}(y) = 2r$ of `negacyclicShift` in $\mathcal{R}_r$
   and telescoping invariance $\sum_{\ell=0}^{L-1} (K_\ell - K_{\ell+1}) = K_0 - K_L$ of total
   radix-2 polynomial-transform butterfly stages.
7. **SWAR width conservation and root precision lower bound (`root_working_precision_gt_two_mul_rootK0`,
   `swar_packed_bit_ops_conservation`)**:
   SWAR gate conservation and root dynamic-range lower bound $q_{\text{child}}(K_0, p_0) > 2 K_0$
   independent of chunk width $b$.

Items 2–7 correspond to Theorems 7.1–7.6 of an earlier draft (restricted-model section, not in the published paper). -/

/-- Block-coset coordinate index $k_2 = \gamma \cdot d + \beta \in \{0, \dots, B_{\text{half}} d - 1\}$
for $\gamma \in \{0, \dots, B_{\text{half}} - 1\}$ and $\beta \in \{0, \dots, d - 1\}$. -/
def cosetBlockIndex (d : ℕ) {Bhalf : ℕ} (γ : Fin Bhalf) (β : Fin d) : Fin (Bhalf * d) :=
  ⟨γ.val * d + β.val, by
    have hγ : γ.val + 1 ≤ Bhalf := γ.isLt
    have hβ : β.val < d := β.isLt
    calc γ.val * d + β.val < γ.val * d + d := Nat.add_lt_add_left hβ _
      _ = (γ.val + 1) * d := by ring
      _ ≤ Bhalf * d := Nat.mul_le_mul_right d hγ⟩

/-- Radix-$B$ ($B = 2 B_{\text{half}}$) intra-butterfly transform over
$\mathcal{R}_r = \mathbb{C}[y]/(y^r + 1)$ ($r = B_{\text{half}} d$, $d = 2r/B$), generated by the
primitive $B$-th root of unity $\omega_B = y^d$. -/
noncomputable def radixBSyntheticButterfly {Bhalf d : ℕ}
    (P : Fin (2 * Bhalf) → Fin (Bhalf * d) → ℂ)
    (v : Fin (2 * Bhalf)) (k2 : Fin (Bhalf * d)) : ℂ :=
  ∑ m : Fin (2 * Bhalf), negacyclicShift ((m.val * v.val : ℤ) * (d : ℤ)) (P m) k2

/-- Decoupled shift-free $\pm 1$ operator $\mathcal{M}_B$ over
$\mathcal{R}_{B/2} = \mathbb{C}[z]/(z^{B/2} + 1)$. -/
noncomputable def decoupledSubringOperator {Bhalf : ℕ}
    (x : Fin (2 * Bhalf) → Fin Bhalf → ℂ)
    (v : Fin (2 * Bhalf)) (γ : Fin Bhalf) : ℂ :=
  ∑ m : Fin (2 * Bhalf),
    (-1 : ℂ) ^ (((γ.val : ℤ) - (m.val * v.val : ℤ)) / (Bhalf : ℤ)) *
      x m (shiftModFin (m.val * v.val : ℤ) γ)

theorem coset_ediv_mul_add {Bhalf d : ℕ} (hB : 0 < Bhalf) (A : ℤ) (β : Fin d) :
    (A * (d : ℤ) + (β.val : ℤ)) / ((Bhalf * d : ℕ) : ℤ) = A / (Bhalf : ℤ) := by
  have hd : 0 < d := β.pos
  have hBd : (0 : ℤ) < ((Bhalf * d : ℕ) : ℤ) := by positivity
  have hBz : (0 : ℤ) < (Bhalf : ℤ) := Nat.cast_pos.mpr hB
  set q := A / (Bhalf : ℤ)
  set rem := A % (Bhalf : ℤ)
  have hA : (Bhalf : ℤ) * q + rem = A := Int.mul_ediv_add_emod A (Bhalf : ℤ)
  have hrem0 : 0 ≤ rem := Int.emod_nonneg A (ne_of_gt hBz)
  have hrem1 : rem < (Bhalf : ℤ) := Int.emod_lt_of_pos A hBz
  have hβ0 : (0 : ℤ) ≤ (β.val : ℤ) := Int.natCast_nonneg β.val
  have hβ1 : (β.val : ℤ) < (d : ℤ) := Int.ofNat_lt.mpr β.isLt
  have hdecomp : A * (d : ℤ) + (β.val : ℤ) =
      (rem * (d : ℤ) + (β.val : ℤ)) + ((Bhalf * d : ℕ) : ℤ) * q := by
    push_cast
    linear_combination -(d : ℤ) * hA
  have hlt : rem * (d : ℤ) + (β.val : ℤ) < ((Bhalf * d : ℕ) : ℤ) := by
    push_cast
    have hrem_le : rem + 1 ≤ (Bhalf : ℤ) := by omega
    have hmul : (rem + 1) * (d : ℤ) ≤ (Bhalf : ℤ) * (d : ℤ) :=
      mul_le_mul_of_nonneg_right hrem_le (by omega)
    linarith
  rw [hdecomp, Int.add_mul_ediv_left _ _ (ne_of_gt hBd),
    Int.ediv_eq_zero_of_lt (by positivity) hlt, zero_add]

theorem coset_emod_mul_add {Bhalf d : ℕ} (hB : 0 < Bhalf) (A : ℤ) (β : Fin d) :
    (A * (d : ℤ) + (β.val : ℤ)) % ((Bhalf * d : ℕ) : ℤ) =
      (A % (Bhalf : ℤ)) * (d : ℤ) + (β.val : ℤ) := by
  have hd : 0 < d := β.pos
  have hBz : (0 : ℤ) < (Bhalf : ℤ) := Nat.cast_pos.mpr hB
  set q := A / (Bhalf : ℤ)
  set rem := A % (Bhalf : ℤ)
  have hA : (Bhalf : ℤ) * q + rem = A := Int.mul_ediv_add_emod A (Bhalf : ℤ)
  have hrem0 : 0 ≤ rem := Int.emod_nonneg A (ne_of_gt hBz)
  have hrem1 : rem < (Bhalf : ℤ) := Int.emod_lt_of_pos A hBz
  have hβ0 : (0 : ℤ) ≤ (β.val : ℤ) := Int.natCast_nonneg β.val
  have hβ1 : (β.val : ℤ) < (d : ℤ) := Int.ofNat_lt.mpr β.isLt
  have hdecomp : A * (d : ℤ) + (β.val : ℤ) =
      (rem * (d : ℤ) + (β.val : ℤ)) + ((Bhalf * d : ℕ) : ℤ) * q := by
    push_cast
    linear_combination -(d : ℤ) * hA
  have hlt : rem * (d : ℤ) + (β.val : ℤ) < ((Bhalf * d : ℕ) : ℤ) := by
    push_cast
    have hrem_le : rem + 1 ≤ (Bhalf : ℤ) := by omega
    have hmul : (rem + 1) * (d : ℤ) ≤ (Bhalf : ℤ) * (d : ℤ) :=
      mul_le_mul_of_nonneg_right hrem_le (by omega)
    linarith
  rw [hdecomp, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) hlt]

/-- **Canonical Subring Decomposition of Radix-$B$ Polynomial-Transform Butterflies
(`radixBSyntheticButterfly_coset_decomposition`)**:
Partitioning each polynomial $P_m \in \mathcal{R}_r$ ($r = B_{\text{half}} d$) into $d$ cosets
$x^{(\beta)}_{m, \alpha} = P_m(\alpha d + \beta)$ decouples the radix-$B$ ($B = 2 B_{\text{half}}$)
butterfly into $d = 2r/B$ independent copies of $\mathcal{M}_B$ (`decoupledSubringOperator`) over
$\mathcal{R}_{B/2}$. -/
theorem radixBSyntheticButterfly_coset_decomposition {Bhalf d : ℕ}
    (P : Fin (2 * Bhalf) → Fin (Bhalf * d) → ℂ)
    (v : Fin (2 * Bhalf)) (γ : Fin Bhalf) (β : Fin d) :
    radixBSyntheticButterfly P v (cosetBlockIndex d γ β) =
      decoupledSubringOperator (fun m α => P m (cosetBlockIndex d α β)) v γ := by
  unfold radixBSyntheticButterfly decoupledSubringOperator
  refine Finset.sum_congr rfl (fun m _ => ?_)
  unfold negacyclicShift
  have hB : 0 < Bhalf := γ.pos
  set A : ℤ := (γ.val : ℤ) - (m.val * v.val : ℤ)
  have hnum : ((cosetBlockIndex d γ β).val : ℤ) - (m.val * v.val : ℤ) * (d : ℤ) =
      A * (d : ℤ) + (β.val : ℤ) := by
    simp only [cosetBlockIndex, A]
    push_cast
    ring
  have hdiv : (((cosetBlockIndex d γ β).val : ℤ) - (m.val * v.val : ℤ) * (d : ℤ)) /
      ((Bhalf * d : ℕ) : ℤ) = A / (Bhalf : ℤ) := by
    rw [hnum]
    exact coset_ediv_mul_add hB A β
  have hshift : shiftModFin ((m.val * v.val : ℤ) * (d : ℤ)) (cosetBlockIndex d γ β) =
      cosetBlockIndex d (shiftModFin (m.val * v.val : ℤ) γ) β := by
    apply Fin.ext
    rw [← Int.ofNat_inj, coe_shiftModFin, hnum, coset_emod_mul_add hB A β]
    simp only [cosetBlockIndex, Nat.cast_add, Nat.cast_mul, coe_shiftModFin, A]
  rw [hdiv, hshift]

/-- **Inter-Stage Monomial Twiddle Reduction by Factor $k$ (`radixB_interStage_twiddle_ops_le`)**:
Across $k_1 / k$ radix-$B$ ($B = 2^k$) stages, applying one inter-stage monomial twiddle per
polynomial ($t_1 r p$ bit operations per stage) costs $(k_1 / k) \cdot (t_1 r p)$ bit operations,
which is at most $(1/k)$ of the radix-2 stage work $k_1 t_1 r p$. -/
theorem radixB_interStage_twiddle_ops_le (k k1 t1 r p : ℕ) :
    k * ((k1 / k) * (t1 * r * p)) ≤ k1 * (t1 * r * p) := by
  calc k * ((k1 / k) * (t1 * r * p))
      = (k * (k1 / k)) * (t1 * r * p) := by ring
    _ ≤ k1 * (t1 * r * p) := Nat.mul_le_mul_right _ (Nat.mul_div_le k1 k)

/-- Integer-valued decoupled operator $\mathcal{M}_B : \mathbb{Z}^{N_B} \to \mathbb{Z}^{N_B}$
on coset slices over $\mathbb{Z}[z]/(z^{B/2} + 1)$. -/
def decoupledSubringOperatorInt {Bhalf : ℕ}
    (x : Fin (2 * Bhalf) → Fin Bhalf → ℤ)
    (v : Fin (2 * Bhalf)) (γ : Fin Bhalf) : ℤ :=
  ∑ m : Fin (2 * Bhalf),
    (-1 : ℤ) ^ (((γ.val : ℤ) - (m.val * v.val : ℤ)) / (Bhalf : ℤ)).natAbs *
      x m (shiftModFin (m.val * v.val : ℤ) γ)

/-- **Bit-Slice Output Range Expansion Bound (`abs_decoupledSubringOperatorInt_le`)**:
For $s$-bit slice inputs $x_{m,\alpha} \in [-(2^s - 1), 2^s - 1]$, every output coordinate of
$\mathcal{M}_B x$ is bounded in magnitude by $B (2^s - 1)$ where $B = 2 B_{\text{half}}$. -/
theorem abs_decoupledSubringOperatorInt_le {Bhalf : ℕ} (s : ℕ)
    (x : Fin (2 * Bhalf) → Fin Bhalf → ℤ)
    (hx : ∀ m α, |x m α| ≤ (2 : ℤ) ^ s - 1)
    (v : Fin (2 * Bhalf)) (γ : Fin Bhalf) :
    |decoupledSubringOperatorInt x v γ| ≤ (2 * Bhalf : ℤ) * ((2 : ℤ) ^ s - 1) := by
  unfold decoupledSubringOperatorInt
  calc
    |∑ m : Fin (2 * Bhalf),
        (-1 : ℤ) ^ (((γ.val : ℤ) - (m.val * v.val : ℤ)) / (Bhalf : ℤ)).natAbs *
          x m (shiftModFin (m.val * v.val : ℤ) γ)|
      ≤ ∑ m : Fin (2 * Bhalf),
          |(-1 : ℤ) ^ (((γ.val : ℤ) - (m.val * v.val : ℤ)) / (Bhalf : ℤ)).natAbs *
            x m (shiftModFin (m.val * v.val : ℤ) γ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m : Fin (2 * Bhalf), |x m (shiftModFin (m.val * v.val : ℤ) γ)| := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ ≤ ∑ _m : Fin (2 * Bhalf), ((2 : ℤ) ^ s - 1) :=
        Finset.sum_le_sum (fun m _ => hx m _)
    _ = (2 * Bhalf : ℤ) * ((2 : ℤ) ^ s - 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
          Nat.cast_ofNat]

/-- **Extremal Bit-Slice Output Attainment & Overlap
(`decoupledSubringOperatorInt_const_zero`, `bitSlice_output_exceeds_slice_width`)**:
On the constant slice $x_{m,\alpha} = 2^s - 1$ at output index $v = 0$, $\mathcal{M}_B x$ attains
$B (2^s - 1) \ge 2^s$ (for $B = 2 B_{\text{half}} \ge 2, s \ge 1$), strictly exceeding the $s$-bit
slice modulus $2^s$ and forcing cross-slice bit overlap at every chunk boundary. -/
theorem decoupledSubringOperatorInt_const_zero {Bhalf : ℕ} (hB : 0 < Bhalf) (s : ℕ)
    (γ : Fin Bhalf) :
    decoupledSubringOperatorInt (fun _ _ => (2 : ℤ) ^ s - 1) ⟨0, by omega⟩ γ =
      (2 * Bhalf : ℤ) * ((2 : ℤ) ^ s - 1) := by
  unfold decoupledSubringOperatorInt
  have hterm : ∀ m : Fin (2 * Bhalf),
      (-1 : ℤ) ^ (((γ.val : ℤ) - (m.val : ℤ) * ((0 : ℕ) : ℤ)) / (Bhalf : ℤ)).natAbs *
        ((2 : ℤ) ^ s - 1) = (2 : ℤ) ^ s - 1 := by
    intro m
    rw [Nat.cast_zero, mul_zero, sub_zero,
      Int.ediv_eq_zero_of_lt (Int.natCast_nonneg γ.val) (Int.ofNat_lt.mpr γ.isLt)]
    simp only [Int.natAbs_zero, pow_zero, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat]

theorem bitSlice_output_exceeds_slice_width (Bhalf s : ℕ) (hB : 1 ≤ Bhalf) (hs : 1 ≤ s) :
    (2 : ℤ) ^ s ≤ (2 * Bhalf : ℤ) * ((2 : ℤ) ^ s - 1) := by
  have h2s : (2 : ℤ) ≤ (2 : ℤ) ^ s := by
    calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
      _ ≤ (2 : ℤ) ^ s := pow_le_pow_right₀ (by norm_num) hs
  have hB2 : (2 : ℤ) ≤ (2 * Bhalf : ℤ) := by omega
  nlinarith

/-- **Bit-Slice Accumulation Cost Decomposition (`bitSliceAccumulationOps_decomp`)**:
Across `numStages = (\log_2 t_1)/k` stages and `numInstances = t_1 r / N_B` instances of
$\mathcal{M}_B$, accumulating `numSlices` overlapping slices of width $s + k$ across all $N_B$
coordinates decomposes into the full $s$-bit term plus the $k$-bit overlap term. -/
theorem bitSliceAccumulationOps_decomp (numStages numInstances N_B numSlices s k : ℕ) :
    numStages * numInstances * (N_B * numSlices * (s + k)) =
      numStages * (numInstances * N_B) * (numSlices * s) +
        numStages * (numInstances * N_B) * (numSlices * k) := by
  ring

/-- Floyd's discrete potential $\Phi(a) = \sum_{i,j} a_{i,j} \lfloor \log_2 a_{i,j} \rfloor$ for a
$B \times B$ packet routing matrix. -/
def floydPotential {B : ℕ} (a : Fin B → Fin B → ℕ) : ℕ :=
  ∑ i : Fin B, ∑ j : Fin B, a i j * Nat.log 2 (a i j)

/-- Initial $B \times B$ packet distribution before transposition: each register $i$ holds $1$
packet for each destination $j$. -/
def floydInitMatrix (B : ℕ) : Fin B → Fin B → ℕ :=
  fun _ _ => 1

/-- Final $B \times B$ packet distribution after transposition: register $j$ holds all $B$ packets
destined for $j$. -/
def floydFinalMatrix (B : ℕ) : Fin B → Fin B → ℕ :=
  fun i j => if i = j then B else 0

/-- **Initial Floyd Potential (`floydPotential_init_eq_zero`)**:
Initially $a_{i,j} = 1$ for all $i, j$, so $\Phi_{\text{init}} = 0$. -/
theorem floydPotential_init_eq_zero (B : ℕ) :
    floydPotential (floydInitMatrix B) = 0 := by
  unfold floydPotential floydInitMatrix
  simp

/-- **Final Floyd Potential (`floydPotential_final_eq`)**:
At completion of a $B \times B$ packet transpose with $B = 2^k$,
$\Phi_{\text{final}} = k B^2 = k \cdot 2^k \cdot 2^k$. -/
theorem floydPotential_final_eq (k : ℕ) :
    floydPotential (floydFinalMatrix (2 ^ k)) = k * (2 ^ k) * (2 ^ k) := by
  unfold floydPotential floydFinalMatrix
  have hrow : ∀ i : Fin (2 ^ k),
      (∑ j : Fin (2 ^ k), (if i = j then 2 ^ k else 0) *
        Nat.log 2 (if i = j then 2 ^ k else 0)) = 2 ^ k * k := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [Nat.log_pow (by decide : 1 < 2)]
    · intro j _ hji
      simp [Ne.symm hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- **Floyd's Potential Packet Transpose Lower Bound (`floyd_transpose_step_lower_bound`)**:
If $T$ register operations transition the packet configuration from `floydInitMatrix (2 ^ k)` to
`floydFinalMatrix (2 ^ k)` with each operation increasing $\Phi$ by at most $\Delta \cdot 2^k$,
then $k \cdot 2^k \le T \cdot \Delta$ ($\Omega(k)$ operations per register per stage), and across
$m$ stages ($k_1 = m \cdot k$), $k_1 \cdot 2^k \le m \cdot (T \cdot \Delta)$. -/
theorem floyd_transpose_step_lower_bound (k T Δ m : ℕ)
    (hstep : floydPotential (floydFinalMatrix (2 ^ k)) -
      floydPotential (floydInitMatrix (2 ^ k)) ≤ T * (Δ * 2 ^ k)) :
    k * 2 ^ k ≤ T * Δ ∧ (m * k) * 2 ^ k ≤ m * (T * Δ) := by
  rw [floydPotential_init_eq_zero, floydPotential_final_eq, Nat.sub_zero] at hstep
  have h1 : (k * 2 ^ k) * 2 ^ k ≤ (T * Δ) * 2 ^ k := by
    calc (k * 2 ^ k) * 2 ^ k = k * 2 ^ k * 2 ^ k := by ring
      _ ≤ T * (Δ * 2 ^ k) := hstep
      _ = (T * Δ) * 2 ^ k := by ring
  have hk : k * 2 ^ k ≤ T * Δ := Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos k)
  refine ⟨hk, ?_⟩
  calc (m * k) * 2 ^ k = m * (k * 2 ^ k) := by ring
    _ ≤ m * (T * Δ) := Nat.mul_le_mul_left m hk

/-- **Kronecker Packing Bit-Operation Lower Comparison (`kronecker_conv_ops_gt_addition_butterfly`)**:
Packing an $N_B$-term 2D convolution of $p$-bit integers into a Kronecker integer with slot width
$2p + 2k$ (bit-length $M_{\text{kron}} = N_B (2p + 2k)$) requires
$M_{\text{kron}} (2k + \lfloor \log_2 p \rfloor) > k N_B p$ bit operations, strictly exceeding the
addition-only radix-2 butterfly work $k N_B p$. -/
theorem kronecker_conv_ops_gt_addition_butterfly (k p N_B : ℕ)
    (hk : 1 ≤ k) (hp : 1 ≤ p) (hN : 1 ≤ N_B) :
    k * N_B * p < N_B * (2 * p + 2 * k) * (2 * k + Nat.log 2 p) := by
  have h1 : k * N_B * p < 4 * (k * N_B * p) := by
    have hpos : 0 < k * N_B * p := by positivity
    omega
  have h2 : 4 * (k * N_B * p) ≤ N_B * (2 * p + 2 * k) * (2 * k + Nat.log 2 p) := by
    calc 4 * (k * N_B * p)
        = N_B * (2 * p) * (2 * k) := by ring
      _ ≤ N_B * (2 * p + 2 * k) * (2 * k + Nat.log 2 p) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left N_B (by omega)) (by omega)
  exact lt_of_lt_of_le h1 h2

/-- **Chunk-Size Telescoping Conservation Bound (`chunk_telescoping_conservation_lower_bound`)**:
For any chain of chunk reductions $b_0 > b_1 > \dots > b_m$ where the normalized work per bit
$W(i) = \mathcal{C}_{\text{mul}}(b_i) / b_i$ satisfies
$W(i) \ge c (L(i) - L(i+1)) + W(i+1)$ ($L(i) = \log_2 b_i$), telescoping across $m$ levels gives
$W(0) \ge c (L(0) - L(m)) + W(m)$. -/
theorem chunk_telescoping_conservation_lower_bound (c : ℝ) (L W : ℕ → ℝ)
    (hstep : ∀ i : ℕ, c * (L i - L (i + 1)) + W (i + 1) ≤ W i) (m : ℕ) :
    c * (L 0 - L m) + W m ≤ W 0 := by
  induction m with
  | zero => linarith
  | succ m ih =>
    have hm := hstep m
    linarith

/-- **Exact Multiplicative Order $\operatorname{ord}(y) = 2r$ of `negacyclicShift` in $\mathcal{R}_r = \mathbb{C}[y]/(y^r + 1)$
(`negacyclicShift_order_two_mul_r`)**:
Shifting by $2r$ is the identity on $\mathcal{R}_r$, whereas for every $1 \le s < 2r$,
`negacyclicShift (s : ℤ)` is non-trivial (moving or negating the unit basis element $e_0 = 1$). -/
theorem negacyclicShift_order_two_mul_r {r : ℕ} (hr : 0 < r) :
    (∀ P : Fin r → ℂ, negacyclicShift (2 * (r : ℤ)) P = P) ∧
      (∀ s : ℕ, 1 ≤ s → s < 2 * r →
        negacyclicShift (s : ℤ) (fun k2 : Fin r => if k2.val = 0 then (1 : ℂ) else 0) ≠
          (fun k2 : Fin r => if k2.val = 0 then (1 : ℂ) else 0)) := by
  refine ⟨fun P => negacyclicShift_two_period P, fun s hs1 hs2 heq => ?_⟩
  set e0 : Fin r → ℂ := fun k2 => if k2.val = 0 then (1 : ℂ) else 0
  by_cases hsr : s = r
  · subst hsr
    have h0 := congr_fun (negacyclicShift_period e0) ⟨0, hr⟩
    rw [heq] at h0
    simp only [e0, ↓reduceIte] at h0
    norm_num at h0
  · set k2 : Fin r := ⟨s % r, Nat.mod_lt s hr⟩
    have hk2_ne : k2.val ≠ 0 := by
      dsimp [k2]
      by_cases hslt : s < r
      · rw [Nat.mod_eq_of_lt hslt]
        omega
      · have h_eq : s = (s - r) + r * 1 := by omega
        have h_mod : s % r = s - r := by
          calc s % r = ((s - r) + r * 1) % r := by rw [← h_eq]
            _ = s - r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        omega
    have hshift : shiftModFin (s : ℤ) k2 = ⟨0, hr⟩ := by
      apply Fin.ext
      rw [← Int.ofNat_inj, coe_shiftModFin]
      dsimp [k2]
      have hdiv : (s : ℤ) = (s : ℤ) % (r : ℤ) + (r : ℤ) * ((s : ℤ) / (r : ℤ)) :=
        (Int.emod_add_mul_ediv (s : ℤ) (r : ℤ)).symm
      have hsub : (s : ℤ) % (r : ℤ) - (s : ℤ) = 0 + (r : ℤ) * (-((s : ℤ) / (r : ℤ))) := by
        linarith
      rw [hsub, Int.add_mul_emod_self_left, Int.zero_emod]
    have hnorm := norm_negacyclicShift (s : ℤ) e0 k2
    rw [heq, hshift] at hnorm
    simp [e0, hk2_ne] at hnorm

/-- **Telescoping Invariance of Total Polynomial-Transform Butterfly Stages
(`butterfly_stage_sum_telescoping_invariance`)**:
For any non-increasing log-dimension sequence $K_0 \ge K_1 \ge \dots \ge K_L$ where level $\ell$
executes $K_\ell - K_{\ell+1} = \log_2(R_\ell / R_{\ell+1})$ butterfly stages, the total stage count
across all $L$ levels is identically $K_0 - K_L = \log_2(R_0 / R_L)$
(compare equation (38) (`eq:syn-route-total`) in Section 7.2 (`sec:cost-proof`)). -/
theorem butterfly_stage_sum_telescoping_invariance (K : ℕ → ℕ) (L : ℕ)
    (hmono : ∀ ell < L, K (ell + 1) ≤ K ell) :
    (∑ ell ∈ Finset.range L, (K ell - K (ell + 1))) = K 0 - K L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih (fun ell hell => hmono ell (Nat.lt_succ_of_lt hell))]
    have h2 : K L ≤ K 0 := by
      clear ih
      induction L with
      | zero => exact le_rfl
      | succ m ihm =>
        exact le_trans (hmono m (Nat.lt_succ_of_lt (Nat.lt_succ_self m)))
          (ihm (fun ell hell => hmono ell (Nat.lt_succ_of_lt hell)))
    have h1 : K (L + 1) ≤ K L := hmono L (Nat.lt_succ_self L)
    omega

/-- **SWAR Gate Conservation & Root Dynamic-Range Lower Bound
(`root_working_precision_gt_two_mul_rootK0`, `swar_packed_bit_ops_conservation`)**:
1. Regardless of how small the chunk width $b$ is, the level-$0$ working precision satisfies
   $q_{\text{child}}(K_0(n), p_0(n)) > 2 K_0(n) = 2 \log_2 R_0(n)$ because column deconvolution
   conditioning and root normalization require at least $2 K_0$ fractional bits.
2. Adding $N_{\text{pack}}$ packed $p$-bit integers conserves total bit width
   $\sum_{i < N_{\text{pack}}} p = N_{\text{pack}} \cdot p$. -/
theorem root_working_precision_gt_two_mul_rootK0 (n : ℕ) :
    2 * rootK0 n < qChildEll (rootK0 n) (rootP0 n) := by
  unfold qChildEll pChildEll pWorkEll
  omega

theorem swar_packed_bit_ops_conservation (N_pack p : ℕ) :
    (∑ _i : Fin N_pack, p) = N_pack * p := by
  simp [Finset.sum_const, Fintype.card_fin]

/-! ## 8. Axiom Verification -/

#print axioms norm_expTwoPiI
#print axioms norm_expNegTwoPiI
#print axioms norm_zetaPow
#print axioms vecInfNorm_normDFT1D_le
#print axioms matInfNorm_normDFT2D_le
#print axioms sum_normDFT1D_mul_expNegTwoPiI
#print axioms sum_normDFT1DNeg_mul_expTwoPiI
#print axioms extractRealDFT_X_eq
#print axioms extractRealDFT_Y_eq
#print axioms evalOddRoot_negacyclicShift
#print axioms evalOddRoot_negacyclicMul
#print axioms twisted_fourier_duality_reduction
#print axioms oddStrideIndex_bijective
#print axioms normDFT1D_odd_eq_normDFT1D_twisted
#print axioms radix2SyntheticFFTExact_eq_syntheticFFT
#print axioms syntheticFFT_rounding_error_le
#print axioms vecInfNorm_postTwistQuant_sub_le
#print axioms matInfNorm_preTwistQuantRoots_sub_preTwistExact_le
#print axioms matInfNorm_postTwistQuantRoots_sub_postTwistExact_le
#print axioms radixBSyntheticButterfly_coset_decomposition
#print axioms abs_decoupledSubringOperatorInt_le
#print axioms floydPotential_final_eq
#print axioms floyd_transpose_step_lower_bound
#print axioms kronecker_conv_ops_gt_addition_butterfly
#print axioms chunk_telescoping_conservation_lower_bound
#print axioms negacyclicShift_order_two_mul_r
#print axioms butterfly_stage_sum_telescoping_invariance
#print axioms root_working_precision_gt_two_mul_rootK0



end IntMul
