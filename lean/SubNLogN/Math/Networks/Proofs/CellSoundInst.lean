import SubNLogN.Math.Networks.Proofs.CellSoundGeom
import SubNLogN.Math.Networks.Proofs.Lemma6Forms

/-!
# Cell soundness: the two label fields satisfy `AGeom`

* bit network: `agBit (hh : (h : ℚ) ≠ 9) : AGeom (betaB h) (betaB3 h)` (`ℚ`, `I − J/9` and its
  Kronecker cube; nondegenerate since `G0 h` is invertible for `h ≠ 9`);
* complex network: `agComplex : AGeom (betaC h) (betaC3 h)` (`𝔽₂`, dot products), every `h`.
-/

namespace SubNLogN.Math.Networks.WP6b

open CellLib

variable {h : ℕ}

theorem G0_isSymm : (G0 h).IsSymm := G0_transpose

theorem G0_nondegenerate (hh : (h : ℚ) ≠ 9) : (Matrix.toBilin' (G0 h)).Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_of_det_ne_zero (G0_det_ne_zero hh))

theorem betaB3_symm (x y : Cube h → ℚ) : betaB3 h x y = betaB3 h y x :=
  LinearMap.BilinForm.isSymm_def.1 (kron3_isSymm G0_isSymm G0_isSymm G0_isSymm) x y

theorem betaB3_nondeg (hh : (h : ℚ) ≠ 9) (x : Cube h → ℚ) (hx : ∀ y, betaB3 h x y = 0) : x = 0 :=
  (kron3_nondegenerate (G0_nondegenerate hh) (G0_nondegenerate hh) (G0_nondegenerate hh)).1 x hx

theorem betaB3_pure (u v w u' v' w' : Fin h → ℚ) :
    betaB3 h (pure3 u v w) (pure3 u' v' w') = betaB h u u' * betaB h v v' * betaB h w w' :=
  toBilin'_kron3_pure3 _ _ _ u v w u' v' w'

/-- The bit label field (`ℚ`, `I − J/9`, Kronecker cube) satisfies `AGeom` for `h ≠ 9`. -/
theorem agBit (hh : (h : ℚ) ≠ 9) : AGeom (betaB h) (betaB3 h) where
  symm := betaB_symm
  nondeg := betaB_nondeg hh
  self := betaB_self
  symm3 := betaB3_symm
  nondeg3 := betaB3_nondeg hh
  pure := betaB3_pure

theorem betaC3_eq_kron : betaC3 h = Matrix.toBilin' (kron3 1 1 1) := by
  rw [kron3_one]; rfl

theorem betaC3_pure (u v w u' v' w' : Fin h → ZMod 2) :
    betaC3 h (pure3 u v w) (pure3 u' v' w') = betaC h u u' * betaC h v v' * betaC h w w' := by
  rw [betaC3_eq_kron]; exact toBilin'_kron3_pure3 _ _ _ u v w u' v' w'

theorem betaC3_symm (x y : Cube h → ZMod 2) : betaC3 h x y = betaC3 h y x := by
  rw [betaC3_apply, betaC3_apply]; simp only [mul_comm (x _)]

theorem betaC3_nondeg (x : Cube h → ZMod 2) (hx : ∀ y, betaC3 h x y = 0) : x = 0 := by
  have hnd : (Matrix.toBilin' (1 : Matrix (Cube h) (Cube h) (ZMod 2))).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_of_det_ne_zero (by simp))
  exact hnd.1 x hx

/-- The complex label field (`𝔽₂`, dot products) satisfies `AGeom`. -/
theorem agComplex : AGeom (betaC h) (betaC3 h) where
  symm := betaC_symm
  nondeg := betaC_nondeg
  self := betaC_self
  symm3 := betaC3_symm
  nondeg3 := betaC3_nondeg
  pure := betaC3_pure

end SubNLogN.Math.Networks.WP6b
