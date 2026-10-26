import SubNLogN.Math.Networks.AppCFun

/-!
# Lemma A.10 (`lem:transfer-phase`) kernel facts of `AppCFun.lean`

Proofs of `InverseKernelStmt` and `KernelSlotStmt h` (statements in
`SubNLogN/Math/Networks/AppCFun.lean`, § 4), with no hypotheses. Helpers live in the
sub-namespace `SubNLogN.Math.Networks.KernelFactsAux`.

Paper: Lemma A.10 (`lem:transfer-phase`), Appendix A.5 (`sec:transfer-frames`) (`C⁻¹ = −iZCZ`; a coordinate kernel is one child).

## Proof plan
* `InverseKernelStmt`. `C2 · (−i)ZC2Z = 1` by a `2 × 2` computation (`ab = 1/2`,
  `a² − b² = i`), hence `C2⁻¹ = (−i)ZC2Z` (`Matrix.inv_eq_right_inv`). On `f` columns `tpow` is
  multiplicative (`Fintype.prod_sum`), sends `c • A` to `c^f • tpow A` and `1` to `1`, so
  `tpow C2 · (−i)^f (tpow Z · tpow C2 · tpow Z) = tpow (C2 · (−i)ZC2Z) = tpow 1 = 1`.
* `KernelSlotStmt`. `(aI + bX_{e_j})_{x,y} = a[x = y] + b[y = x + e_j]`, which is `C2(x_j, y_j)`
  when `x, y` agree off `j` and `0` otherwise (`Kv_single_apply`); the tensor power is the
  product over the `f` columns, which vanishes iff some column disagrees off `j`.
-/

namespace SubNLogN.Math.Networks

namespace KernelFactsAux

/-! ## Tensor powers -/

/-- `tpow` is multiplicative. -/
theorem tpow_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (A B : Matrix ι ι ℂ) :
    tpow k (A * B) = tpow k A * tpow k B := by
  ext x y
  simp only [tpow, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib]

/-- `tpow k (c • A) = c^k • tpow k A`. -/
theorem tpow_smul {ι : Type*} [Fintype ι] (k : ℕ) (c : ℂ) (A : Matrix ι ι ℂ) :
    tpow k (c • A) = c ^ k • tpow k A := by
  ext x y
  simp only [tpow, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Fin.prod_const]

/-- `tpow k 1 = 1`. -/
theorem tpow_one {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    tpow k (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  simp only [tpow]
  by_cases hxy : x = y
  · rw [hxy, Matrix.one_apply_eq]
    exact Finset.prod_eq_one fun c _ => Matrix.one_apply_eq _
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨c, hc⟩ : ∃ c, x c ≠ y c := by
      by_contra hne
      push Not at hne
      exact hxy (funext hne)
    exact Finset.prod_eq_zero (Finset.mem_univ c) (Matrix.one_apply_ne hc)

/-! ## The `2 × 2` inverse `C⁻¹ = −i Z C Z` -/

theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem sum_zmod2 (g : ZMod 2 → ℂ) : ∑ x, g x = g 0 + g 1 := by
  refine Fintype.sum_eq_add 0 1 (by decide) fun x hx => ?_
  rcases zmod2_cases x with rfl | rfl
  · exact absurd rfl hx.1
  · exact absurd rfl hx.2

theorem C2_apply (u v : ZMod 2) : C2 u v = if u = v then ka else kb := rfl

theorem C2_00 : C2 0 0 = ka := if_pos rfl
theorem C2_01 : C2 0 1 = kb := if_neg (by decide)
theorem C2_10 : C2 1 0 = kb := if_neg (by decide)
theorem C2_11 : C2 1 1 = ka := if_pos rfl

theorem zsign_0 : (-1 : ℂ) ^ (0 : ZMod 2).val = 1 := by
  rw [ZMod.val_zero, pow_zero]

theorem zsign_1 : (-1 : ℂ) ^ (1 : ZMod 2).val = -1 := by
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

/-- `C2 · (−i) Z C2 Z = 1`. -/
theorem C2_mul_inv : C2 * ((-Complex.I) • (Zmat * C2 * Zmat)) = 1 := by
  ext x y
  rw [Matrix.mul_apply, sum_zmod2]
  simp only [Matrix.smul_apply, smul_eq_mul, Zmat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp only [C2_00, C2_01, C2_10, C2_11, zsign_0, zsign_1, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : ZMod 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : ZMod 2) ≠ 0 by decide)] <;> simp only [ka, kb]
  · linear_combination (-1 : ℂ) * Complex.I_sq
  · ring
  · ring
  · linear_combination (-1 : ℂ) * Complex.I_sq

end KernelFactsAux

open KernelFactsAux

/-- **Lemma A.10 (`lem:transfer-phase`) inverse child** (`InverseKernelStmt`): `C⁻¹ = −i Z C Z`, and on every number `f` of
columns `(C^{⊗f})⁻¹ = (−i)^f Z^{⊗f} C^{⊗f} Z^{⊗f}`. -/
theorem inverseKernel_holds : InverseKernelStmt := by
  refine ⟨Matrix.inv_eq_right_inv C2_mul_inv, fun f => Matrix.inv_eq_right_inv ?_⟩
  rw [← tpow_mul, ← tpow_mul, ← tpow_smul, ← tpow_mul, C2_mul_inv, tpow_one]

/-! ## A coordinate kernel is one child on its slot -/

namespace KernelFactsAux

theorem zmod2_ne_add_one : ∀ a b : ZMod 2, a ≠ b → b = a + 1 := by decide

theorem zmod2_ne_self_add_one : ∀ a : ZMod 2, a ≠ a + 1 := by decide

/-- One column: `(aI + bX_{e_j})_{x,y} = [x, y agree off j] · C2(x_j, y_j)`. -/
theorem Kv_single_apply {h : ℕ} (j : Cube h) (x y : Pt h) :
    Kv (Pi.single j 1) 1 x y = if ∀ p, p ≠ j → x p = y p then C2 (x j) (y j) else 0 := by
  simp only [Kv, if_true, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Xv,
    Matrix.one_apply]
  by_cases hoff : ∀ p, p ≠ j → x p = y p
  · rw [if_pos hoff]
    by_cases hj : x j = y j
    · have hxy : x = y := funext fun p => if hp : p = j then hp ▸ hj else hoff p hp
      have hne : ¬ y = x + Pi.single j 1 := by
        intro hy
        have h' := congrFun hy j
        rw [hxy, Pi.add_apply, Pi.single_eq_same] at h'
        exact zmod2_ne_self_add_one _ h'
      rw [if_pos hxy, if_neg hne, C2_apply, if_pos hj, mul_one, mul_zero, add_zero]
    · have hxy : x ≠ y := fun hxy => hj (hxy ▸ rfl)
      have hy : y = x + Pi.single j 1 := by
        funext p
        by_cases hp : p = j
        · rw [hp, Pi.add_apply, Pi.single_eq_same]
          exact zmod2_ne_add_one _ _ hj
        · rw [Pi.add_apply, Pi.single_eq_of_ne hp, add_zero]
          exact (hoff p hp).symm
      rw [if_neg hxy, if_pos hy, C2_apply, if_neg hj, mul_zero, mul_one, zero_add]
  · rw [if_neg hoff]
    push Not at hoff
    obtain ⟨p, hp, hxp⟩ := hoff
    have hxy : x ≠ y := fun hxy => hxp (hxy ▸ rfl)
    have hne : ¬ y = x + Pi.single j 1 := by
      intro hy
      apply hxp
      rw [hy, Pi.add_apply, Pi.single_eq_of_ne hp, add_zero]
    rw [if_neg hxy, if_neg hne, mul_zero, mul_zero, add_zero]

end KernelFactsAux

/-- **Lemma A.10 (`lem:transfer-phase`) coordinate kernel = child on one slot** (`KernelSlotStmt h`): on `f` columns,
`(aI + bX_{e_j})^{⊗f}` is `C^{⊗f}` on the bits `(x c j)_c` of slot `j` and the identity on all
other bits. -/
theorem kernelSlot_holds (h : ℕ) : KernelSlotStmt h := by
  intro f j x y
  simp only [tpow, Kv_single_apply]
  by_cases hall : ∀ c, ∀ p, p ≠ j → x c p = y c p
  · rw [if_pos hall]
    exact Finset.prod_congr rfl fun c _ => if_pos (hall c)
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨c, p, hp, hne⟩ := hall
    exact Finset.prod_eq_zero (Finset.mem_univ c) (if_neg fun hc => hne (hc p hp))

end SubNLogN.Math.Networks
