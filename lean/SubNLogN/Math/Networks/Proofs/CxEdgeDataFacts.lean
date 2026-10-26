import SubNLogN.Math.Networks.AppCCore
import SubNLogN.Math.Networks.AppCFun3

/-!
# Networks: existence of valid complex edge data (`ExistsValidCxDataStmt`, Lemma A.10 (`lem:transfer-phase`) edges)

`existsValidCxData_of`: from an orthonormal residual basis per edge (`Lemma6OnbStmt`), basis
extension (`BasisExtensionStmt 100`) and binary row-addition words (`BinaryRowAdditionsStmt`), every
edge of the complex network gets data satisfying `CxEdgeData.Valid`:
* the basis `B` is the given ONB, and `eps = B.map (epsC e)`;
* an ONB over `𝔽₂` is linearly independent (`linIndep_of_isONB`). Basis extension gives an
  invertible `M` whose columns at distinct coordinates `cs` are `B`; permuting columns by a
  permutation `σ` with `σ (cubeEquiv.symm t) = cs[t]` (`perm_exists`, via `Equiv.extendSubtype`)
  moves them to the first coordinates in physical order (`M₁ = M.submatrix id σ`,
  `M₁⁻¹ = M⁻¹.submatrix σ id`);
* `rowsMove` applies a word in time order, so the reversed word of `M₁ = Π rowAdd` (reindexed to
  `Fin mH` by `cubeEquiv`) realizes `x ↦ M₁ x` (`rowsMove_eq_mulVec`); likewise for `M₁⁻¹`.
Helpers live in `SubNLogN.Math.Networks.CxEdgeDataAux`.
-/

namespace SubNLogN.Math.Networks

namespace CxEdgeDataAux

theorem dotC_comm {h : ℕ} (x y : Pt h) : dotC x y = dotC y x := by
  unfold dotC
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem dotC_sum_smul {h : ℕ} {ι : Type*} (s : Finset ι) (g : ι → ZMod 2) (v : ι → Pt h)
    (w : Pt h) : dotC (∑ i ∈ s, g i • v i) w = ∑ i ∈ s, g i * dotC (v i) w := by
  unfold dotC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

theorem dotC_zero_left {h : ℕ} (w : Pt h) : dotC 0 w = 0 := by
  simp [dotC]

/-- An orthonormal list over `𝔽₂` is linearly independent. -/
theorem linIndep_of_isONB {h : ℕ} {E : Submodule (ZMod 2) (Pt h)} {B : List (Pt h)}
    (hB : IsONB E B) : LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i) := by
  obtain ⟨hnorm, hpair, -⟩ := hB
  have horth : ∀ i j : Fin B.length, i ≠ j → dotC (B.get i) (B.get j) = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · simpa using List.pairwise_iff_getElem.mp hpair i j i.isLt j.isLt (Fin.lt_def.mp hlt)
    · rw [dotC_comm]
      simpa using List.pairwise_iff_getElem.mp hpair j i j.isLt i.isLt (Fin.lt_def.mp hlt)
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have h1 := congrArg (fun v => dotC v (B.get i)) hsum
  rw [dotC_sum_smul, Finset.sum_eq_single i, hnorm _ (by simp), mul_one, dotC_zero_left] at h1
  · exact h1
  · intro j _ hji
    rw [horth j i hji, mul_zero]
  · intro hi'
    exact absurd hi hi'

theorem card_cube : Fintype.card (Cube 100) = mH := by
  rw [Fintype.card_congr cubeEquiv, Fintype.card_fin]

/-- A permutation of the cube sending the first `|cs|` coordinates (physical order) to `cs`. -/
theorem perm_exists (cs : List (Cube 100)) (hnd : cs.Nodup) (hn : cs.length ≤ mH) :
    ∃ σ : Equiv.Perm (Cube 100), ∀ t : Fin cs.length,
      σ (cubeEquiv.symm ⟨t.val, lt_of_lt_of_le t.isLt hn⟩) = cs.get t := by
  classical
  let g : Fin cs.length → Cube 100 := fun t => cubeEquiv.symm ⟨t.val, lt_of_lt_of_le t.isLt hn⟩
  have hg : Function.Injective g := by
    intro a b hab
    have h2 := cubeEquiv.symm.injective hab
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  have hf : Function.Injective cs.get := List.nodup_iff_injective_get.mp hnd
  let e : Set.range g ≃ Set.range cs.get :=
    (Equiv.ofInjective g hg).symm.trans (Equiv.ofInjective cs.get hf)
  refine ⟨e.extendSubtype, fun t => ?_⟩
  have hmem : g t ∈ Set.range g := ⟨t, rfl⟩
  rw [Equiv.extendSubtype_apply_of_mem e (g t) hmem]
  simp [e, Equiv.ofInjective_symm_apply]

/-- One row addition `x_i ← x_i + x_j`, read through `cubeEquiv`. -/
theorem step_eq (i j : Fin mH) (x : Pt 100) :
    (Function.update x (cubeEquiv.symm i) (x (cubeEquiv.symm i) + x (cubeEquiv.symm j))) ∘
        cubeEquiv.symm =
      (rowAdd i j).mulVec (x ∘ cubeEquiv.symm) := by
  funext k
  simp only [Function.comp_apply, rowAdd, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  by_cases hk : k = i
  · subst hk
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · rw [Function.update_of_ne (fun h => hk (cubeEquiv.symm.injective h))]
    simp [Matrix.mulVec, dotProduct, Ne.symm hk]

theorem rowsMove_eq (l : List (Fin mH × Fin mH)) (x : Pt 100) :
    rowsMove l x ∘ cubeEquiv.symm =
      ((l.reverse.map fun p => rowAdd p.1 p.2).prod).mulVec (x ∘ cubeEquiv.symm) := by
  induction l generalizing x with
  | nil => simp [rowsMove]
  | cons p l ih =>
    have h1 : rowsMove (p :: l) x = rowsMove l (Function.update x (cubeEquiv.symm p.1)
        (x (cubeEquiv.symm p.1) + x (cubeEquiv.symm p.2))) := rfl
    rw [h1, ih, step_eq]
    simp [List.reverse_cons, List.map_append, List.prod_append, Matrix.mulVec_mulVec]

theorem reindex_mulVec (M : Matrix (Cube 100) (Cube 100) (ZMod 2)) (x : Pt 100) (q : Cube 100) :
    (Matrix.reindex cubeEquiv cubeEquiv M).mulVec (x ∘ cubeEquiv.symm) (cubeEquiv q) =
      M.mulVec x q := by
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Function.comp_apply, Equiv.symm_apply_apply]
  exact Equiv.sum_comp cubeEquiv.symm (fun q' => M q q' * x q')

theorem rowsMove_eq_mulVec (l : List (Fin mH × Fin mH)) (M : Matrix (Cube 100) (Cube 100) (ZMod 2))
    (hM : Matrix.reindex cubeEquiv cubeEquiv M = (l.map fun p => rowAdd p.1 p.2).prod)
    (x : Pt 100) : rowsMove l.reverse x = M.mulVec x := by
  funext q
  have h := congrFun (rowsMove_eq l.reverse x) (cubeEquiv q)
  rw [List.reverse_reverse, ← hM] at h
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at h
  rw [h, reindex_mulVec]

/-- Valid edge data exist for every edge of the complex network. -/
theorem exists_valid (honb : Lemma6OnbStmt) (hext : BasisExtensionStmt 100)
    (hrow : BinaryRowAdditionsStmt) (e : Vertex .complex 100 × Vertex .complex 100)
    (he : ∃ w, e ∈ edges w) : ∃ Dd : CxEdgeData, Dd.Valid e := by
  classical
  obtain ⟨w, hw⟩ := he
  obtain ⟨B, hB⟩ := honb w e hw
  obtain ⟨cs, M, M', hnd, hlen, hMM', hcol⟩ := hext B (linIndep_of_isONB hB)
  have hn : cs.length ≤ mH := card_cube ▸ hnd.length_le_card
  obtain ⟨σ, hσ⟩ := perm_exists cs hnd hn
  let M₁ : Matrix (Cube 100) (Cube 100) (ZMod 2) := M.submatrix id σ
  let M₁' : Matrix (Cube 100) (Cube 100) (ZMod 2) := M'.submatrix σ id
  have hM1 : M₁ * M₁' = 1 := by
    simp only [M₁, M₁']
    rw [Matrix.submatrix_mul_equiv, hMM', Matrix.submatrix_id_id]
  have hdet : M₁.det * M₁'.det = 1 := by rw [← Matrix.det_mul, hM1, Matrix.det_one]
  have hu1 : IsUnit (Matrix.reindex cubeEquiv cubeEquiv M₁).det := by
    rw [Matrix.det_reindex_self]
    exact isUnit_iff_exists_inv.mpr ⟨_, hdet⟩
  have hu2 : IsUnit (Matrix.reindex cubeEquiv cubeEquiv M₁').det := by
    rw [Matrix.det_reindex_self]
    exact isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact hdet⟩
  obtain ⟨l, hl1, hl2, hl3⟩ := hrow mH _ hu1
  obtain ⟨l', hl1', hl2', hl3'⟩ := hrow mH _ hu2
  refine ⟨⟨B, B.map (epsC e), l'.reverse, l.reverse⟩, hB, rfl, ?_, ?_, ?_, M₁, M₁', hM1, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hl1' p (List.mem_reverse.mp hp)
    · exact hl1 p (List.mem_reverse.mp hp)
  · simpa using hl2'
  · simpa using hl2
  · intro t ht htm p
    have hc : t < cs.length := hlen ▸ ht
    have h1 : σ (cubeEquiv.symm ⟨t, htm⟩) = cs.get ⟨t, hc⟩ := hσ ⟨t, hc⟩
    show M p (σ (cubeEquiv.symm ⟨t, htm⟩)) = B.get ⟨t, ht⟩ p
    rw [h1, ← hcol t ht hc, Matrix.mulVec_single_one]
    rfl
  · exact fun x => rowsMove_eq_mulVec l M₁ hl3 x
  · exact fun x => rowsMove_eq_mulVec l' M₁' hl3' x

end CxEdgeDataAux

/-- **Existence of valid complex edge data** (`ExistsValidCxDataStmt`) from the [OAI26] Lemma 6 ONB, basis
extension and binary row additions. -/
theorem existsValidCxData_of (honb : Lemma6OnbStmt) (hext : BasisExtensionStmt 100)
    (hrow : BinaryRowAdditionsStmt) : ExistsValidCxDataStmt := by
  classical
  refine ⟨fun e => if he : ∃ w, e ∈ edges w then
      Classical.choose (CxEdgeDataAux.exists_valid honb hext hrow e he) else ⟨[], [], [], []⟩, ?_⟩
  intro w e he
  have hex : ∃ w, e ∈ edges w := ⟨w, he⟩
  simp only [dif_pos hex]
  exact Classical.choose_spec (CxEdgeDataAux.exists_valid honb hext hrow e hex)

end SubNLogN.Math.Networks
