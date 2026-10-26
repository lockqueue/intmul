import SubNLogN.Math.Networks.Cert
import SubNLogN.Math.Networks.Proofs.Bruhat

/-!
# Proof of `ExistsValidFacStmt` (Lemma A.6 (`lem:transfer-shear`) specialization at `h = 100`)

Lemma A.6 (`lem:transfer-shear`), Appendix A.2 (`sec:transfer-power`); [OAI26, Lemmas 9–10, §4.1].

We prove `existsValidFac_holds : ExistsValidFacStmt`: there are an odd prime `q` and factorization
data `fac A` for every rational `mH × mH` matrix `A` such that all frame entries `matB v i j` are
`q`-integral and `fac (edgeMatFin e)` is valid at `q` for every edge `e` of every role of the bit
network at `h = 100`.

## Plan

1. For every `A`, [OAI26] Lemma 9 (`lemma9_holds`) gives `A = E₁ * Π * E₂` with `E₁, E₂` lower triangular
   of unit determinant and `Π` a partial permutation with exactly `rank A` ones; we pick such data
   by `choose`. The factorization data is `mkFac E₁ E₂ Π = ⟨E₁, E₁⁻¹, E₂, E₂⁻¹, piv⟩` with `piv` the
   list (`Finset.toList`) of the positions of the ones of `Π`.
   * `E⁻¹` is lower triangular (`Matrix.blockTriangular_inv_of_blockTriangular`) and
     `E * E⁻¹ = 1` (`Matrix.mul_nonsing_inv`).
   * The projections of `piv` are duplicate-free by the partial-permutation property, and
     `piv.length = #ones = rank A`.
   * `Matrix.of (indicator of piv) = Π`.
   * The diagonal entries of `E` and of `E⁻¹` are nonzero (lower triangular with unit
     determinant: the determinant is the product of the diagonal).
2. All rationals to be avoided are the values of one function `avoidVal E₁ E₂` on the finite
   index type `AvoidIdx` (frame entries `matB v i j`, and the entries of the four matrices
   `E₁, E₁⁻¹, E₂, E₂⁻¹` chosen for `edgeMatFin e`, for **all** pairs `e` of vertices -- a superset
   of the edges). The prime of `existsOddPrimeAvoiding_holds` applied to the image `bigSet` of
   `avoidVal E₁ E₂` is odd, makes all these entries `q`-integral, and divides no numerator of a
   nonzero one, in particular no diagonal numerator.

Implementation note: membership in `Finset.univ` of a *product* type such as
`Fin mH × Fin mH` must not be checked by unfolding (Lean's unifier would evaluate the product
`Finset`, exceeding the recursion limit). All such facts are therefore derived from lemmas stated
for an arbitrary `Fintype` or field (`forall_mem_bigSet`, `mem_pivList`, `length_pivList`) and
only instantiated here by first-order unification, and no bound variable has a type of the form
`x ∈ s` for such a `Finset` `s`.
-/

namespace SubNLogN.Math.Networks

namespace ValidFacAux

/-! ### Generic finiteness lemmas (stated for an arbitrary `Fintype`) -/

/-- The finite set of values of a function on a finite type. -/
def bigSet {T : Type} [Fintype T] (g : T → ℚ) : Finset ℚ :=
  Finset.univ.image g

theorem mem_bigSet {T : Type} [Fintype T] (g : T → ℚ) (t : T) : g t ∈ bigSet g :=
  Finset.mem_image_of_mem g (Finset.mem_univ t)

/-- A property of all elements of `bigSet g` holds for every value of `g`. (Applying this lemma
only requires first-order unification with the hypothesis, never a membership check.) -/
theorem forall_mem_bigSet {T : Type} [Fintype T] {g : T → ℚ} {P : ℚ → Prop}
    (h : ∀ r ∈ bigSet g, P r) (t : T) : P (g t) :=
  h _ (mem_bigSet g t)

/-- The list of the positions of the ones of a square matrix. -/
noncomputable def pivList {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (Pm : Matrix (Fin n) (Fin n) K) : List (Fin n × Fin n) :=
  (Finset.univ.filter (fun p : Fin n × Fin n => Pm p.1 p.2 = 1)).toList

theorem mem_pivList {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (Pm : Matrix (Fin n) (Fin n) K) (p : Fin n × Fin n) : p ∈ pivList Pm ↔ Pm p.1 p.2 = 1 := by
  rw [pivList, Finset.mem_toList, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ p, h⟩⟩

theorem nodup_pivList {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (Pm : Matrix (Fin n) (Fin n) K) : (pivList Pm).Nodup :=
  Finset.nodup_toList _

/-- For a partial permutation matrix with `a` ones, `pivList` has length `a`. -/
theorem length_pivList {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (Pm : Matrix (Fin n) (Fin n) K) {a : ℕ} (h : IsPartialPerm Pm a) :
    (pivList Pm).length = a := by
  obtain ⟨-, -, -, hcard⟩ := h
  rw [← hcard, pivList, Finset.length_toList]
  congr 1
  exact (Finset.filter_congr_decidable _ _ _).symm

/-! ### Triangular matrices -/

variable {n : ℕ}

theorem isLowerTriangular_of_isLowerTri {K : Type} [Field K] {E : Matrix (Fin n) (Fin n) K}
    (hE : IsLowerTri E) : E.IsLowerTriangular :=
  fun i j h => hE i j h

/-- The inverse of an invertible lower triangular matrix is lower triangular. -/
theorem lowerTri_inv {K : Type} [Field K] {E : Matrix (Fin n) (Fin n) K} (hE : IsLowerTri E)
    (hdet : IsUnit E.det) : IsLowerTri E⁻¹ := by
  have := Matrix.invertibleOfIsUnitDet E hdet
  have h := Matrix.blockTriangular_inv_of_blockTriangular (isLowerTriangular_of_isLowerTri hE)
  intro i j hij
  exact h (OrderDual.toDual_lt_toDual.mpr hij)

/-- A lower triangular matrix of unit determinant has nonzero diagonal entries. -/
theorem diag_ne_zero {K : Type} [Field K] {E : Matrix (Fin n) (Fin n) K} (hE : IsLowerTri E)
    (hdet : IsUnit E.det) (i : Fin n) : E i i ≠ 0 := by
  have h := hdet.ne_zero
  rw [Matrix.det_of_isLowerTriangular E (isLowerTriangular_of_isLowerTri hE)] at h
  exact Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)

/-! ### The factorization data and its validity -/

/-- Factorization data from [OAI26] Lemma 9 data `E₁, E₂, Pm`: the factors, their inverses, and the list
of positions of the ones of `Pm`. -/
noncomputable def mkFac (E₁ E₂ Pm : Matrix (Fin mH) (Fin mH) ℚ) : FacData :=
  ⟨E₁, E₁⁻¹, E₂, E₂⁻¹, pivList Pm⟩

/-- All entries of `M` are `q`-integral, and nonzero entries have numerators not divisible
by `q`. -/
def EntriesOK (q : ℕ) (M : Matrix (Fin mH) (Fin mH) ℚ) : Prop :=
  ∀ i j, QIntegral q (M i j) ∧ (M i j ≠ 0 → ¬ (q : ℤ) ∣ (M i j).num)

/-- Validity of `mkFac E₁ E₂ Pm` for [OAI26] Lemma 9 data `A = E₁ * Pm * E₂` (`Pm` a partial permutation
matrix whose `pivList` has length `rank A`), given the prime conditions on all entries of
`E₁, E₁⁻¹, E₂, E₂⁻¹`. -/
theorem valid_of_lemma9 (q : ℕ) (A E₁ E₂ Pm : Matrix (Fin mH) (Fin mH) ℚ)
    (hlt₁ : IsLowerTri E₁) (hlt₂ : IsLowerTri E₂) (hdet₁ : IsUnit E₁.det)
    (hdet₂ : IsUnit E₂.det) (hzo : ∀ i j, Pm i j = 0 ∨ Pm i j = 1)
    (hrow : ∀ i j j', Pm i j = 1 → Pm i j' = 1 → j = j')
    (hcol : ∀ i i' j, Pm i j = 1 → Pm i' j = 1 → i = i')
    (hlen : (pivList Pm).length = A.rank) (heq : A = E₁ * Pm * E₂)
    (hq₁ : EntriesOK q E₁) (hq₁' : EntriesOK q E₁⁻¹) (hq₂ : EntriesOK q E₂)
    (hq₂' : EntriesOK q E₂⁻¹) :
    FacData.Valid q A (mkFac E₁ E₂ Pm) := by
  have hdet₁' : IsUnit E₁⁻¹.det := Matrix.isUnit_nonsing_inv_det E₁ hdet₁
  have hdet₂' : IsUnit E₂⁻¹.det := Matrix.isUnit_nonsing_inv_det E₂ hdet₂
  have hlt₁' : IsLowerTri E₁⁻¹ := lowerTri_inv hlt₁ hdet₁
  have hlt₂' : IsLowerTri E₂⁻¹ := lowerTri_inv hlt₂ hdet₂
  refine ⟨hlt₁, hlt₁', hlt₂, hlt₂', Matrix.mul_nonsing_inv E₁ hdet₁,
    Matrix.mul_nonsing_inv E₂ hdet₂, ?_, ?_, hlen, ?_, ?_, ?_⟩
  · -- distinct pivot rows
    refine List.Nodup.map_on ?_ (nodup_pivList Pm)
    intro x hx y hy hxy
    exact Prod.ext hxy (hrow x.1 x.2 y.2 ((mem_pivList Pm x).mp hx)
      (by rw [hxy]; exact (mem_pivList Pm y).mp hy))
  · -- distinct pivot columns
    refine List.Nodup.map_on ?_ (nodup_pivList Pm)
    intro x hx y hy hxy
    exact Prod.ext (hcol x.1 y.1 x.2 ((mem_pivList Pm x).mp hx)
      (by rw [hxy]; exact (mem_pivList Pm y).mp hy)) hxy
  · -- the factorization
    have hPm : (Matrix.of fun i j => if (i, j) ∈ pivList Pm then (1 : ℚ) else 0) = Pm := by
      ext i j
      rw [Matrix.of_apply]
      by_cases h : Pm i j = 1
      · rw [if_pos ((mem_pivList Pm (i, j)).mpr h), h]
      · rw [if_neg (fun hm => h ((mem_pivList Pm (i, j)).mp hm))]
        rcases hzo i j with h0 | h1
        · exact h0.symm
        · exact absurd h1 h
    show A = E₁ * (Matrix.of fun i j => if (i, j) ∈ pivList Pm then (1 : ℚ) else 0) * E₂
    rw [hPm]
    exact heq
  · -- `q`-integrality of all entries
    intro i j
    exact ⟨(hq₁ i j).1, (hq₁' i j).1, (hq₂ i j).1, (hq₂' i j).1⟩
  · -- diagonal numerators
    intro i
    exact ⟨(hq₁ i i).2 (diag_ne_zero hlt₁ hdet₁ i), (hq₁' i i).2 (diag_ne_zero hlt₁' hdet₁' i),
      (hq₂ i i).2 (diag_ne_zero hlt₂ hdet₂ i), (hq₂' i i).2 (diag_ne_zero hlt₂' hdet₂' i)⟩

/-! ### The finitely many rationals to be avoided by the prime -/

/-- Index of the entries of the four factor matrices of one vertex pair. -/
abbrev EdgeIdx : Type := (Vertex .bit 100 × Vertex .bit 100) × Fin mH × Fin mH

/-- Index type of all rationals to be avoided: frame entries, then the entries of `E₁`, `E₁⁻¹`,
`E₂`, `E₂⁻¹` for every vertex pair. -/
abbrev AvoidIdx : Type :=
  (Vertex .bit 100 × Cube 100 × Cube 100) ⊕ EdgeIdx ⊕ EdgeIdx ⊕ EdgeIdx ⊕ EdgeIdx

/-- The rationals to be avoided, for the chosen factor families `E₁, E₂`. -/
noncomputable def avoidVal (E₁ E₂ : Matrix (Fin mH) (Fin mH) ℚ → Matrix (Fin mH) (Fin mH) ℚ) :
    AvoidIdx → ℚ
  | .inl (v, i, j) => matB v i j
  | .inr (.inl (e, i, j)) => E₁ (edgeMatFin e) i j
  | .inr (.inr (.inl (e, i, j))) => (E₁ (edgeMatFin e))⁻¹ i j
  | .inr (.inr (.inr (.inl (e, i, j)))) => E₂ (edgeMatFin e) i j
  | .inr (.inr (.inr (.inr (e, i, j)))) => (E₂ (edgeMatFin e))⁻¹ i j

end ValidFacAux

open ValidFacAux in
/-- Lemma A.6 (`lem:transfer-shear`) specialization: there are an odd prime `q` and
factorization data valid at `q` ([OAI26] Lemma 9 factors with lower-triangular inverses, `q`-integral
entries and diagonal numerators prime to `q`) for every edge matrix of the bit network at
`h = 100`, and all frame entries `matB v i j` are `q`-integral. -/
theorem existsValidFac_holds : ExistsValidFacStmt := by
  have h9 : Lemma9Stmt := lemma9_holds
  choose E₁ E₂ Pm hlt₁ hlt₂ hdet₁ hdet₂ hPP heq using
    (fun A : Matrix (Fin mH) (Fin mH) ℚ => h9 A)
  obtain ⟨q, hq, hq2, hS⟩ := existsOddPrimeAvoiding_holds (bigSet (avoidVal E₁ E₂))
  refine ⟨q, fun A => mkFac (E₁ A) (E₂ A) (Pm A), hq, hq2, ?_, ?_⟩
  · -- frame entries
    intro v i j
    exact (forall_mem_bigSet hS (.inl (v, i, j))).1
  · -- edge factorizations
    intro w e _
    exact valid_of_lemma9 q (edgeMatFin e) (E₁ (edgeMatFin e)) (E₂ (edgeMatFin e))
      (Pm (edgeMatFin e)) (hlt₁ _) (hlt₂ _) (hdet₁ _) (hdet₂ _) (hPP _).1 (hPP _).2.1
      (hPP _).2.2.1 (length_pivList _ (hPP _)) (heq _)
      (fun i j => forall_mem_bigSet hS (.inr (.inl (e, i, j))))
      (fun i j => forall_mem_bigSet hS (.inr (.inr (.inl (e, i, j)))))
      (fun i j => forall_mem_bigSet hS (.inr (.inr (.inr (.inl (e, i, j))))))
      (fun i j => forall_mem_bigSet hS (.inr (.inr (.inr (.inr (e, i, j))))))

end SubNLogN.Math.Networks
