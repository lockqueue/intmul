import SubNLogN.Math.Networks.AppCFun3
import SubNLogN.Math.Networks.GeneralH
import SubNLogN.Math.Networks.Proofs.Prop8Edge

/-!
# Lemma A.10 (`lem:transfer-phase`) edge realization, basis extension, and [OAI26] Prop. 8 edges for general `h`

Proofs of `EdgeRealizationStmt h`, `BasisExtensionStmt h` (`AppCFun3.lean`) and of
`Prop8EdgeGenStmt h` (`GeneralH.lean`) from `Lemma6NestedGenStmt h` and
`Lemma6NondegComplexGenStmt h`, for every `h`.

## Plan (Lemma A.10 (`lem:transfer-phase`))

* `EdgeRealizationStmt`. From `M M' = 1` (hence `M' M = 1`): `P_M P_{M'} = 1` and
  `P_{M'} P_M = 1` (`permOp_mul_eq_one`, direct sum computation); `P_M X_v P_{M'} = X_{Mv}`
  (`permOp_Xv_permOp`, a local copy of `translationConj_holds`), so
  `P_M K(v, ε) P_{M'} = K(Mv, ε)`. Conjugation by mutually inverse elements commutes with list
  products (`conj_list_prod`), hence
  `P_M (Π_i K(e_{cs_i}, ε_{v_i})) P_{M'} = Π_i K(M e_{cs_i}, ε_{v_i}) = Π_i K(v_i, ε_{v_i})`; finally
  `map Prod.fst (zip B cs) = B` (equal lengths).
* `BasisExtensionStmt`. Extend the independent family `B` to a basis `Basis.sumExtend` indexed by
  `Fin r ⊕ κ` (its `inl i` vector is `B_i`, `sumExtend_inl`), transport it to a basis indexed by
  `Cube h` along an equivalence `τ : Cube h ≃ Fin r ⊕ κ` (`Basis.indexEquiv`), and put
  `cs_i = τ⁻¹(inl i)`, `M = ` matrix of this basis in the standard basis, `M' = ` the inverse change
  of basis matrix (`Basis.toMatrix_mul_toMatrix_flip`). Then `M e_{cs_i}` is the `cs_i`-th basis
  vector, i.e. `B_i`.
* `Prop8EdgeGenStmt`: the proof of `prop8Edge_of` (`Proofs/Prop8Edge.lean`) with `100 ↦ h`, using
  the generic `CU_eq_kernels_mul_CU_of_le` / `_of_ge`.
-/

namespace SubNLogN.Math.Networks

namespace EdgeRealAux

variable {h : ℕ}

/-! ### Move operators -/

/-- `P_M P_{M'} = 1` when `M M' = 1`. -/
theorem permOp_mul_eq_one {M M' : Matrix (Cube h) (Cube h) (ZMod 2)} (hMM' : M * M' = 1) :
    permOp M * permOp M' = 1 := by
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [permOp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]

/-- `P_M X_v P_{M'} = X_{Mv}` when `M M' = 1` (local copy of `translationConj_holds`,
`Proofs/AppCLayerAlg.lean`). -/
theorem permOp_Xv_permOp {M M' : Matrix (Cube h) (Cube h) (ZMod 2)} (hMM' : M * M' = 1)
    (v : Pt h) : permOp M * Xv v * permOp M' = Xv (M.mulVec v) := by
  have hM'M : M' * M = 1 := mul_eq_one_comm.mp hMM'
  have key : ∀ a b : Pt h, a = M.mulVec b ↔ b = M'.mulVec a := by
    intro a b
    constructor
    · rintro rfl
      rw [Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
    · rintro rfl
      rw [Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]
  have hcond : ∀ x y : Pt h, M'.mulVec x + v = M'.mulVec y ↔ y = x + M.mulVec v := by
    intro x y
    rw [← key, Matrix.mulVec_add, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]
  ext x y
  simp only [Matrix.mul_apply, permOp, Xv, key, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hcond]

/-- `P_M K(w, ε) P_{M'} = K(Mw, ε)` when `M M' = 1`. -/
theorem permOp_Kv_permOp {M M' : Matrix (Cube h) (Cube h) (ZMod 2)} (hMM' : M * M' = 1)
    (w : Pt h) (ε : ℤ) : permOp M * Kv w ε * permOp M' = Kv (M.mulVec w) ε := by
  have h1 := permOp_mul_eq_one hMM'
  have hX := permOp_Xv_permOp hMM' w
  unfold Kv
  split_ifs <;>
  simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h1, hX]

/-- Conjugation by mutually inverse elements of a monoid commutes with list products. -/
theorem conj_list_prod {G : Type*} [Monoid G] {P P' : G} (hP'P : P' * P = 1) (hPP' : P * P' = 1)
    (L : List G) : P * L.prod * P' = (L.map fun A => P * A * P').prod := by
  induction L with
  | nil => rw [List.prod_nil, mul_one, hPP', List.map_nil, List.prod_nil]
  | cons A L ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    calc P * (A * L.prod) * P' = P * A * (P' * P) * L.prod * P' := by
          rw [hP'P, mul_one, mul_assoc P A]
      _ = P * A * P' * (P * L.prod * P') := by simp only [mul_assoc]

/-! ### Basis extension -/

/-- The vectors `inl i` of `Basis.sumExtend` are the given family. -/
theorem sumExtend_inl {ι : Type*} {v : ι → Pt h} (hs : LinearIndependent (ZMod 2) v) (i : ι) :
    Module.Basis.sumExtend hs (Sum.inl i) = v i := by
  simp only [Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend]
  rfl

/-- An equivalence between the coordinates and the index type of the extended basis. -/
noncomputable def extEquiv (B : List (Pt h))
    (hB : LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i)) :
    Cube h ≃ (Fin B.length ⊕ Module.Basis.sumExtendIndex hB) :=
  (Pi.basisFun (ZMod 2) (Cube h)).indexEquiv (Module.Basis.sumExtend hB)

/-- The extension of `B` to a basis of `Pt h`, indexed by the coordinates. -/
noncomputable def extBasis (B : List (Pt h))
    (hB : LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i)) :
    Module.Basis (Cube h) (ZMod 2) (Pt h) :=
  (Module.Basis.sumExtend hB).reindex (extEquiv B hB).symm

theorem extBasis_apply_cs (B : List (Pt h))
    (hB : LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i)) (i : Fin B.length) :
    extBasis B hB ((extEquiv B hB).symm (Sum.inl i)) = B.get i := by
  rw [extBasis, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    sumExtend_inl]

theorem mulVec_single_one_apply (M : Matrix (Cube h) (Cube h) (ZMod 2)) (c c' : Cube h) :
    M.mulVec (Pi.single c 1) c' = M c' c := by
  rw [Matrix.mulVec_single_one]
  rfl

end EdgeRealAux

open EdgeRealAux

/-- **Lemma A.10 (`lem:transfer-phase`) edge realization** (`EdgeRealizationStmt h`): if
`M M' = 1` and `M e_{cs_i} = B_i` for all `i` (with `|B| = |cs|`), then
`Π_{v∈B} K(v, ε v) = P_M (Π_i K(e_{cs_i}, ε B_i)) P_{M'}`. No further hypotheses. -/
theorem edgeRealization_holds (h : ℕ) : EdgeRealizationStmt h := by
  intro B ε M M' cs hMM' hlen hcol
  have hPP' := permOp_mul_eq_one hMM'
  have hP'P := permOp_mul_eq_one (mul_eq_one_comm.mp hMM')
  have hpair : ∀ p ∈ B.zip cs, M.mulVec (Pi.single p.2 1) = p.1 := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
    rw [← hpi]
    have hiB : i < B.length := List.lt_length_left_of_zip hi
    have hic : i < cs.length := List.lt_length_right_of_zip hi
    have := hcol i hiB hic
    simpa only [List.get_eq_getElem, List.getElem_zip] using this
  rw [conj_list_prod hP'P hPP']
  conv_lhs => rw [← List.map_fst_zip (le_of_eq hlen)]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [permOp_Kv_permOp hMM', hpair p hp]

/-- **Basis extension** (`BasisExtensionStmt h`): a linearly independent list `B` of binary
vectors is the list of columns, at distinct coordinates `cs`, of an invertible binary matrix
`M` (with explicit inverse `M'`). No further hypotheses. -/
theorem basisExtension_holds (h : ℕ) : BasisExtensionStmt h := by
  intro B hB
  refine ⟨(List.finRange B.length).map (fun i => (extEquiv B hB).symm (Sum.inl i)),
    (Pi.basisFun (ZMod 2) (Cube h)).toMatrix (extBasis B hB),
    (extBasis B hB).toMatrix (Pi.basisFun (ZMod 2) (Cube h)), ?_, ?_, ?_, ?_⟩
  · exact (List.nodup_finRange _).map
      (fun i j hij => Sum.inl_injective ((extEquiv B hB).symm.injective hij))
  · simp
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · intro i hi hc
    funext c'
    rw [mulVec_single_one_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    have hcs : ((List.finRange B.length).map
        (fun j => (extEquiv B hB).symm (Sum.inl j))).get ⟨i, hc⟩ =
        (extEquiv B hB).symm (Sum.inl ⟨i, hi⟩) := by
      simp
    rw [hcs, extBasis_apply_cs]

/-- [OAI26] Prop. 8, edge factorization (contract C2), for every `h`, from the general-`h`
Lemma 6 contracts (nestedness of adjacent labels, nondegeneracy of complex labels): for every
edge and every orthonormal basis `B` of its residual,
`frameC head = (Π_{v∈B} K(v, epsC e v)) · frameC tail`. -/
theorem prop8EdgeGen_of (h : ℕ) (hnest : Lemma6NestedGenStmt h)
    (hU : Lemma6NondegComplexGenStmt h) : Prop8EdgeGenStmt h := by
  intro w e he B hB
  show CU (labC e.2) = _ * CU (labC e.1)
  by_cases hle : labC e.1 ≤ labC e.2
  · have hR : residC e = labC e.2 ⊓ (betaC3 h).orthogonal (labC e.1) := by
      simp only [residC, residual, if_pos hle]
    rw [hR] at hB
    have hmap : (B.map fun v => Kv v (epsC e v)) =
        B.map fun v => Kv v (if wt v % 4 = 1 then 1 else -1) := by
      apply List.map_congr_left
      intro v _
      simp only [epsC, if_pos hle, one_mul]
    rw [hmap]
    exact CU_eq_kernels_mul_CU_of_le hle (hU e.1) (hU e.2) hB
  · have hge : labC e.2 ≤ labC e.1 := (hnest.2 w e he).resolve_left hle
    have hR : residC e = labC e.1 ⊓ (betaC3 h).orthogonal (labC e.2) := by
      simp only [residC, residual, if_neg hle]
    rw [hR] at hB
    have hmap : (B.map fun v => Kv v (epsC e v)) =
        B.map fun v => Kv v (if wt v % 4 = 1 then -1 else 1) := by
      apply List.map_congr_left
      intro v _
      simp only [epsC, if_neg hle]
      split_ifs <;> norm_num
    rw [hmap]
    exact CU_eq_kernels_mul_CU_of_ge hge (hU e.1) (hU e.2) hB

end SubNLogN.Math.Networks
