import SubNLogN.Math.Networks.CellCalc

/-!
# Cell soundness, factor forms: the factor forms of the two label fields

Facts about the factor forms of `Labels.lean` ([OAI26, §3.3]):
* bit network, `K = ℚ`, `β = xᵀ(I − J/9)y` (`betaB`): `β(t_S, t_T) = |S ∩ T| − 1`
  (`betaB_ind`); `β` is symmetric and, for `h ≠ 9`, nondegenerate (`G0 h` is invertible:
  `G0_mul_inv`);
* complex network, `K = 𝔽₂`, the dot product (`betaC`): `t_S · t_T = |S ∩ T| mod 2` (`betaC_ind`).
In both fields triple lines are nondegenerate and neighbouring triple lines are orthogonal
(`betaB_nbr`, `betaC_nbr`).
-/

namespace SubNLogN.Math.Networks.WP6b

variable {h : ℕ}

section Ind

variable {K : Type*} [Field K]

theorem sum_ind (t : Tri h) : ∑ i, (ind t i : K) = 3 := by
  have h1 : ∀ i, (ind t i : K) = if i ∈ t.1 then 1 else 0 := fun i => rfl
  simp only [h1, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, t.2]
  norm_num

theorem sum_ind_mul_ind (S T : Tri h) : ∑ i, (ind S i : K) * ind T i = (inter S T : K) := by
  have h1 : ∀ i, (ind S i : K) * ind T i = if i ∈ S.1 ∩ T.1 then 1 else 0 := by
    intro i
    simp only [ind, Finset.mem_inter]
    split_ifs <;> simp_all
  simp only [h1, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, inter]

theorem inter_self (t : Tri h) : inter t t = 3 := by
  simp [inter, t.2]

end Ind

/-! ### The bit factor form `I − J/9` -/

/-- The all-one matrix. -/
def Jm (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := Matrix.of fun _ _ => 1

theorem Jm_mul_Jm : Jm h * Jm h = (h : ℚ) • Jm h := by
  ext i j
  simp [Jm, Matrix.mul_apply]

theorem G0_eq : G0 h = 1 - (9 : ℚ)⁻¹ • Jm h := rfl

/-- `(I − J/9)⁻¹ = I + J/(9 − h)` for `h ≠ 9`. -/
theorem G0_mul_inv (hh : (h : ℚ) ≠ 9) : G0 h * (1 + (9 - (h : ℚ))⁻¹ • Jm h) = 1 := by
  have h9 : (9 : ℚ) - h ≠ 0 := sub_ne_zero.2 (Ne.symm hh)
  rw [G0_eq, sub_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, Jm_mul_Jm,
    smul_smul, smul_smul]
  have : (9 : ℚ)⁻¹ • Jm h + ((9 : ℚ)⁻¹ * (9 - (h : ℚ))⁻¹ * h) • Jm h = (9 - (h : ℚ))⁻¹ • Jm h := by
    rw [← add_smul]
    congr 1
    field_simp
    ring
  rw [← this]
  abel

theorem G0_det_ne_zero (hh : (h : ℚ) ≠ 9) : (G0 h).det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse (G0_mul_inv hh)

theorem G0_transpose : (G0 h).transpose = G0 h := by
  ext i j
  simp only [G0, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]

theorem betaB_apply (x y : Fin h → ℚ) :
    betaB h x y = ∑ i, x i * y i - (9 : ℚ)⁻¹ * ((∑ i, x i) * ∑ j, y j) := by
  rw [betaB, Matrix.toBilin'_apply, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  have h1 : ∑ j, x i * G0 h i j * y j =
      ∑ j, ((if i = j then x i * y j else 0) - (9 : ℚ)⁻¹ * (x i * y j)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G0, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul]
    split_ifs <;> ring
  rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

theorem betaB_symm (x y : Fin h → ℚ) : betaB h x y = betaB h y x := by
  rw [betaB_apply, betaB_apply, mul_comm (∑ i, x i)]
  simp only [mul_comm (x _)]

/-- `⟨t_S, t_T⟩ = |S ∩ T| − 1` ([OAI26, §3.3]). -/
theorem betaB_ind (S T : Tri h) : betaB h (ind S) (ind T) = (inter S T : ℚ) - 1 := by
  rw [betaB_apply, sum_ind_mul_ind, sum_ind, sum_ind]
  norm_num

theorem betaB_self (t : Tri h) : betaB h (ind t) (ind t) ≠ 0 := by
  rw [betaB_ind, inter_self]; norm_num

theorem betaB_nbr {S T : Tri h} (hST : Nbr .bit S T) : betaB h (ind S) (ind T) = 0 := by
  have : inter S T = 1 := hST
  rw [betaB_ind, this]; norm_num

theorem betaB_nondeg (hh : (h : ℚ) ≠ 9) (x : Fin h → ℚ) (hx : ∀ y, betaB h x y = 0) : x = 0 := by
  have hnd : (Matrix.toBilin' (G0 h)).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_of_det_ne_zero (G0_det_ne_zero hh))
  exact hnd.1 x hx

/-! ### The complex factor form: the dot product over `𝔽₂` -/

theorem betaC_apply (x y : Fin h → ZMod 2) : betaC h x y = ∑ i, x i * y i := by
  simp [betaC, Matrix.toBilin'_apply, Matrix.one_apply]

theorem betaC_symm (x y : Fin h → ZMod 2) : betaC h x y = betaC h y x := by
  rw [betaC_apply, betaC_apply]
  simp only [mul_comm (x _)]

theorem betaC_ind (S T : Tri h) : betaC h (ind S) (ind T) = (inter S T : ZMod 2) := by
  rw [betaC_apply, sum_ind_mul_ind]

theorem betaC_self (t : Tri h) : betaC h (ind t) (ind t) ≠ 0 := by
  rw [betaC_ind, inter_self]; decide

theorem betaC_nbr {S T : Tri h} (hST : Nbr .complex S T) : betaC h (ind S) (ind T) = 0 := by
  rw [betaC_ind]
  rcases hST.2 with h0 | h2
  · rw [h0]; rfl
  · rw [h2]; rfl

theorem betaC_nondeg (x : Fin h → ZMod 2) (hx : ∀ y, betaC h x y = 0) : x = 0 := by
  have hnd : (Matrix.toBilin' (1 : Matrix (Fin h) (Fin h) (ZMod 2))).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_of_det_ne_zero (by simp))
  exact hnd.1 x hx

theorem betaC3_apply (x y : Cube h → ZMod 2) : betaC3 h x y = ∑ p, x p * y p := by
  simp [betaC3, Matrix.toBilin'_apply, Matrix.one_apply]

end SubNLogN.Math.Networks.WP6b
