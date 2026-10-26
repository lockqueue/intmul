import SubNLogN.Math.Networks.PhaseFrames

/-!
# Lemma A.10 (`lem:transfer-phase`) edge operations: the inverse kernel as a conjugated forward kernel

`kv_conj_Z`: for a basis vector `v = e_e` of `𝔽₂^m` (`m = 100³`) and `ε ≠ 1`,
`(−i)^f · Z^{⊗f} · K_v^{⊗f} · Z^{⊗f} = (K_v^{-1})^{⊗f}` where `K_v = aI + bX_v`, `K_v^{-1} = bI + aX_v`
(`Kv v ε`) and `Z = diag((−1)^{x_e})` on the coordinate `e` of every column. This is how Lemma A.10 (`lem:transfer-phase`) realizes
an inverse kernel by the forward child (Appendix A.5 (`sec:transfer-frames`)). No hypotheses beyond
`ε ≠ 1`.

Proof: entrywise. All four factors are column products, so the identity reduces to one coordinate:
`(−i) (−1)^{x_e} K_v(x, y) (−1)^{y_e} = K_v^{-1}(x, y)`. On the diagonal this is `(−i) a = b`; for
`y = x + e_e` the signs give `−1` and `i b = a`; elsewhere both sides vanish.
-/

namespace SubNLogN.Math.Networks

namespace CCoreEdgeMatAux

theorem neg_I_mul_ka : -Complex.I * ka = kb := by
  unfold ka kb
  linear_combination (-1 / 2 : ℂ) * Complex.I_sq

theorem neg_I_mul_kb_neg : -Complex.I * kb * -1 = ka := by
  unfold ka kb
  linear_combination (-1 / 2 : ℂ) * Complex.I_sq

/-- The coordinate identity behind `kv_conj_Z`. -/
theorem coord_identity (e : Cube 100) (ε : ℤ) (hε : ε ≠ 1) (x y : Pt 100) :
    -Complex.I * ((-1 : ℂ) ^ (x e).val * (Kv (Pi.single e 1) 1 x y * (-1 : ℂ) ^ (y e).val)) =
      Kv (Pi.single e 1) ε x y := by
  set v : Pt 100 := Pi.single e 1 with hvdef
  have hve : v e = 1 := by
    rw [hvdef]
    exact Pi.single_eq_same e 1
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hv0 : (0 : ZMod 2).val = 0 := by decide
  have hv1 : (1 : ZMod 2).val = 1 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  have hK1 : Kv v 1 x y = ka * (if x = y then 1 else 0) + kb * (if y = x + v then 1 else 0) := by
    simp only [Kv, if_true, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Xv]
  have hKε : Kv v ε x y = kb * (if x = y then 1 else 0) + ka * (if y = x + v then 1 else 0) := by
    simp only [Kv, if_neg hε, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Xv]
  rw [hK1, hKε]
  by_cases hxy : x = y
  · subst hxy
    have hne : ¬ (x = x + v) := by
      intro h
      have h' := congrFun h e
      rw [Pi.add_apply, hve] at h'
      rcases h01 (x e) with h0 | h0 <;> rw [h0] at h' <;> revert h' <;> decide
    have hsq : (-1 : ℂ) ^ (x e).val * (-1 : ℂ) ^ (x e).val = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    simp only [if_true, if_neg hne, mul_one, mul_zero, add_zero]
    calc -Complex.I * ((-1 : ℂ) ^ (x e).val * (ka * (-1 : ℂ) ^ (x e).val))
        = (-Complex.I * ka) * ((-1 : ℂ) ^ (x e).val * (-1 : ℂ) ^ (x e).val) := by ring
      _ = kb := by rw [hsq, mul_one, neg_I_mul_ka]
  · by_cases hyx : y = x + v
    · subst hyx
      have hodd : (-1 : ℂ) ^ (x e).val * (-1 : ℂ) ^ ((x + v) e).val = -1 := by
        rw [Pi.add_apply, hve]
        rcases h01 (x e) with h | h <;> rw [h]
        · rw [zero_add, hv0, hv1]
          norm_num
        · rw [h11, hv1, hv0]
          norm_num
      simp only [if_neg hxy, if_true, mul_zero, zero_add, mul_one]
      calc -Complex.I * ((-1 : ℂ) ^ (x e).val * (kb * (-1 : ℂ) ^ ((x + v) e).val))
          = (-Complex.I * kb) * ((-1 : ℂ) ^ (x e).val * (-1 : ℂ) ^ ((x + v) e).val) := by ring
        _ = ka := by rw [hodd, neg_I_mul_kb_neg]
    · simp only [if_neg hxy, if_neg hyx, mul_zero, add_zero, zero_mul]

end CCoreEdgeMatAux

open CCoreEdgeMatAux in
/-- **Inverse kernels by conjugation** (Lemma A.10 (`lem:transfer-phase`)): `(−i)^f Z^{⊗f} K_v^{⊗f} Z^{⊗f} = (K_v^{-1})^{⊗f}` for
`v = e_e` and `ε ≠ 1`, with `Z = diag((−1)^{x_e})` in every column. -/
theorem kv_conj_Z (e : Cube 100) (ε : ℤ) (hε : ε ≠ 1) (f : ℕ) :
    Matrix.diagonal (fun _ : Fin f → Pt 100 => (-Complex.I) ^ f) *
      (Matrix.diagonal (fun X : Fin f → Pt 100 => ∏ col, (-1 : ℂ) ^ (X col e).val) *
        (tpow f (Kv (Pi.single e 1) 1) *
          Matrix.diagonal (fun X : Fin f → Pt 100 => ∏ col, (-1 : ℂ) ^ (X col e).val))) =
      tpow f (Kv (Pi.single e 1) ε) := by
  ext X Y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, tpow]
  rw [← Fin.prod_const f (-Complex.I)]
  simp only [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun c _ => coord_identity e ε hε (X c) (Y c)

end SubNLogN.Math.Networks
