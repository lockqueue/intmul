import Mathlib

/-!
# Common: norms on finite arrays (Section 3.1 (`sec:notation`))

* `‖x‖` for `x : ι → ℂ` (`ι` a `Fintype`) is Mathlib's sup norm: `‖x‖ = max_i |x_i|`. This is the
  paper's `‖x‖_∞`; we do not define a separate sup norm.
* `l1Norm`, `l2Norm`: the `ℓ¹` and `ℓ²` norms (used for filter norms, Lemma 4.6 (bridge Lemma C)(i)).
* `opNormInf A`: the operator norm induced by `‖·‖_∞`, i.e. the largest absolute row sum of the
  matrix of `A` (Section 3.1 (`sec:notation`)).
-/

namespace SubNLogN.Math.Common

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The `ℓ¹` norm `∑_i |x_i|`. -/
noncomputable def l1Norm (x : ι → ℂ) : ℝ := ∑ i, ‖x i‖

/-- The `ℓ²` norm `(∑_i |x_i|^2)^{1/2}`. -/
noncomputable def l2Norm (x : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- The sup norm characterization (Mathlib's norm on `ι → ℂ` is `max_i ‖x i‖`). -/
theorem norm_le_iff_forall {x : ι → ℂ} {C : ℝ} (hC : 0 ≤ C) : ‖x‖ ≤ C ↔ ∀ i, ‖x i‖ ≤ C :=
  pi_norm_le_iff_of_nonneg hC

variable [DecidableEq ι]

/-- The operator norm induced by `‖·‖_∞` (largest absolute row sum, Section 3.1 (`sec:notation`)). -/
noncomputable def opNormInf (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) : ℝ :=
  ((Finset.univ.sup fun i => ∑ j, ‖LinearMap.toMatrix' A i j‖₊ : NNReal) : ℝ)

/-- `opNormInf A` is the operator norm of `A`, viewed as a continuous linear map on the sup-normed
space `ι → ℂ` (Mathlib: `Matrix.linfty_opNorm_def`, `Matrix.linfty_opNorm_eq_opNorm`). -/
private theorem exists_clm_opNormInf (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) :
    ∃ f : (ι → ℂ) →L[ℂ] (ι → ℂ), opNormInf A = ‖f‖ ∧ ∀ x, f x = A x := by
  refine ⟨ContinuousLinearMap.mk (Matrix.mulVecLin (LinearMap.toMatrix' A))
    (LinearMap.continuous_of_finiteDimensional _), ?_, fun x => ?_⟩
  · exact (Matrix.linfty_opNorm_def (LinearMap.toMatrix' A)).symm.trans
      (Matrix.linfty_opNorm_eq_opNorm (LinearMap.toMatrix' A))
  · exact LinearMap.toMatrix'_mulVec A x

/-- CONTRACT: `‖A x‖_∞ ≤ ‖A‖_∞ ‖x‖_∞`. -/
theorem norm_apply_le_opNormInf (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (x : ι → ℂ) :
    ‖A x‖ ≤ opNormInf A * ‖x‖ := by
  obtain ⟨f, hf, hfx⟩ := exists_clm_opNormInf A
  rw [hf, ← hfx x]
  exact f.le_opNorm x

/-- CONTRACT: the largest absolute row sum is the induced norm: for `C ≥ 0`,
`‖A‖_∞ ≤ C ↔ ∀ x, ‖A x‖_∞ ≤ C ‖x‖_∞`. -/
theorem opNormInf_le_iff (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) {C : ℝ} (hC : 0 ≤ C) :
    opNormInf A ≤ C ↔ ∀ x, ‖A x‖ ≤ C * ‖x‖ := by
  obtain ⟨f, hf, hfx⟩ := exists_clm_opNormInf A
  rw [hf, ContinuousLinearMap.opNorm_le_iff hC]
  simp only [hfx]

/-- CONTRACT: submultiplicativity `‖AB‖_∞ ≤ ‖A‖_∞ ‖B‖_∞`. -/
theorem opNormInf_comp_le (A B : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) :
    opNormInf (A ∘ₗ B) ≤ opNormInf A * opNormInf B := by
  have hA : 0 ≤ opNormInf A := by unfold opNormInf; positivity
  have hB : 0 ≤ opNormInf B := by unfold opNormInf; positivity
  rw [opNormInf_le_iff _ (mul_nonneg hA hB)]
  intro x
  calc ‖(A ∘ₗ B) x‖ = ‖A (B x)‖ := rfl
    _ ≤ opNormInf A * ‖B x‖ := norm_apply_le_opNormInf A (B x)
    _ ≤ opNormInf A * (opNormInf B * ‖x‖) :=
        mul_le_mul_of_nonneg_left (norm_apply_le_opNormInf B x) hA
    _ = opNormInf A * opNormInf B * ‖x‖ := by ring

/-- CONTRACT: `‖A‖_∞ ≥ 0`. -/
theorem opNormInf_nonneg (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) : 0 ≤ opNormInf A := by
  unfold opNormInf; positivity

end SubNLogN.Math.Common
