import SubNLogN.Math.Networks.AppCLayer
import SubNLogN.Math.Networks.CellCalc
import SubNLogN.Math.Networks.Instances

/-!
# Typed network certificates for the two triple networks at `h = 100`

In Appendix A, Definition A.1 (`def:fixed-network-premises`) and Fact 3.4 (`fact:oai-networks`)
state the fixed finite-network premises partly by reference to [OAI26].
Here they are *typed*: every field is a precise Lean statement about the concrete Lean networks of
`Basic.lean`/`Scalar.lean`/`Labels.lean`/`BitFrames.lean`/`PhaseFrames.lean`/`Framed.lean`
(roles, gates, the eight-row schedule, labels, rational frames, phase frames, the framed
execution). Appendix A (Lemma A.6, Proposition A.7, Lemmas A.8–A.10, Proposition A.11) consumes only these structures;
the `h = 100` instances are assembled from the `_holds` theorems of `Networks/Proofs/` (no field is assumed).

`ExistsValidFacStmt` is the specialization step of Lemma A.6 (`lem:transfer-shear`): one odd prime `q`
and, for every edge, a lower-triangular factorization `A_e = E₁ Π E₂` ([OAI26] Lemma 9) whose factors and
their inverses are `q`-integral with unit diagonals mod `q`, in the physical field order of the
`m = h³` coordinates (`cubeEquiv`: lexicographic order of the cube, first coordinate most
significant). The shared definitions `mH`, `cubeEquiv`, `FacData`, `edgeMatFin` live here and are
used by the Proposition A.7 (`prop:transfer11`) procedure (`AppCProc.lean`).
-/

namespace SubNLogN.Math.Networks

/-- `m = h³` at `h = 100`, as the explicit product `100 * (100 * 100)`. -/
abbrev mH : ℕ := 100 * (100 * 100)

/-- The physical order of the `m` address fields of a chunk: lexicographic order of the cube
`[100]³` (first coordinate most significant), via `finProdFinEquiv`. -/
def cubeEquiv : Cube 100 ≃ Fin mH :=
  (Equiv.prodCongr (Equiv.refl (Fin 100)) finProdFinEquiv).trans finProdFinEquiv

/-- Factorization data `A = E₁ Π E₂` of an edge matrix (with inverses and the pivot list of `Π`). -/
structure FacData where
  /-- `E₁` -/
  E₁ : Matrix (Fin mH) (Fin mH) ℚ
  /-- `E₁⁻¹` -/
  E₁' : Matrix (Fin mH) (Fin mH) ℚ
  /-- `E₂` -/
  E₂ : Matrix (Fin mH) (Fin mH) ℚ
  /-- `E₂⁻¹` -/
  E₂' : Matrix (Fin mH) (Fin mH) ℚ
  /-- positions of the ones of `Π` -/
  piv : List (Fin mH × Fin mH)

/-- Validity of factorization data for `A` at the prime `q` ([OAI26] Lemma 9 specialized mod `q^b`):
lower-triangular factors with lower-triangular inverses, `Π` with distinct pivot rows and columns
and exactly `rank A` ones, all entries `q`-integral, diagonal numerators prime to `q`. -/
def FacData.Valid (q : ℕ) (A : Matrix (Fin mH) (Fin mH) ℚ) (F : FacData) : Prop :=
  IsLowerTri F.E₁ ∧ IsLowerTri F.E₁' ∧ IsLowerTri F.E₂ ∧ IsLowerTri F.E₂' ∧
  F.E₁ * F.E₁' = 1 ∧ F.E₂ * F.E₂' = 1 ∧
  (F.piv.map Prod.fst).Nodup ∧ (F.piv.map Prod.snd).Nodup ∧ F.piv.length = A.rank ∧
  A = F.E₁ * Matrix.of (fun i j => if (i, j) ∈ F.piv then (1 : ℚ) else 0) * F.E₂ ∧
  (∀ i j, QIntegral q (F.E₁ i j) ∧ QIntegral q (F.E₁' i j) ∧ QIntegral q (F.E₂ i j) ∧
    QIntegral q (F.E₂' i j)) ∧
  (∀ i, ¬ (q : ℤ) ∣ (F.E₁ i i).num ∧ ¬ (q : ℤ) ∣ (F.E₁' i i).num ∧ ¬ (q : ℤ) ∣ (F.E₂ i i).num ∧
    ¬ (q : ℤ) ∣ (F.E₂' i i).num)

/-- Edge matrix `A_e = M_head − M_tail` of the bit network in the physical coordinate order. -/
noncomputable def edgeMatFin (e : Vertex .bit 100 × Vertex .bit 100) : Matrix (Fin mH) (Fin mH) ℚ :=
  Matrix.reindex cubeEquiv cubeEquiv (matB e.2 - matB e.1)

/-- CONTRACT (Lemma A.6 (`lem:transfer-shear`) specialization; [OAI26, Lemmas 9–10, §4.1], prime radix
choice). There are an odd prime `q` and factorization
data valid at `q` for every edge matrix of the bit network at `h = 100`, with all frame entries
`q`-integral. -/
def ExistsValidFacStmt : Prop :=
  ∃ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData), q.Prime ∧ q ≠ 2 ∧
    (∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j)) ∧
    ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e)

/-- **Typed network certificate of the bit network at `h = 100`** (Appendix A Definition A.1(a); [OAI26] Lemma 5,
Prop 7; Appendix D.2, Proposition D.3 (`oai:networks`)). All fields are statements about the concrete Lean network. -/
structure BitNetCert : Prop where
  /-- `W_b` roles. -/
  card_roles : Fintype.card (Role .bit 100) = tripleWb 100
  /-- B1: the scalar circuit is the role permutation `ρ`, for arbitrary scratch values. -/
  scalar : Lemma5BitStmt 100
  /-- Frame invariant (5) ([OAI26, §3.2, (5)]) of the framed execution. -/
  frame_invariant : FrameInvariantStmt 100
  /-- B2: `M_{sink ρ(w)} − M_{source w} = I_m`. -/
  endpoint : Prop7EndpointStmt
  /-- B3: framed execution with edge shears `Φ_{A_e}` shears every role by `H ← H + D`. -/
  array_corollary : BitArrayCorollaryStmt
  /-- B4: `Σ_e rank_ℚ A_e = s_b`. -/
  rank_sum : ∑ w : Role .bit 100, ((edges w).map fun e => rankQ (edgeMatB e)).sum = tripleSb 100
  /-- `s_b < W_b m`. -/
  deficit : tripleSb 100 < tripleWb 100 * tripleM 100
  /-- Lemma A.6 (`lem:transfer-shear`): the prime radix and the edge factorizations. -/
  radix : ExistsValidFacStmt

/-- **Typed network certificate of the complex network at `h = 100`** (Appendix A Definition A.1(b);
[OAI26] Lemmas 5-6, Prop 8; Appendix D.2, Proposition D.3 (`oai:prop8`)). All fields are statements about the concrete
Lean network: signed scalar action, nondegenerate nested binary labels, orthonormal residual
bases, the edge factorization, the endpoint corrections (`Z_{a,k}`, `i^{27k}`, bank negation) in
one and in `k` columns, and the exact child count `Σ dim = s_c`. -/
structure ComplexNetCert : Prop where
  /-- `W_c` roles. -/
  card_roles : Fintype.card (Role .complex 100) = tripleWc 100
  /-- C1: `(X_a, Y_a) ↦ (−Y_a, X_a)`, scratch restored, for arbitrary scratch values. -/
  scalar : Lemma5ComplexStmt 100
  /-- Frame invariant (5) ([OAI26, §3.2, (5)]) of the framed execution. -/
  frame_invariant : FrameInvariantStmt 100
  /-- [OAI26] Lemma 6: every label is nondegenerate. -/
  nondeg : Lemma6NondegComplexStmt
  /-- [OAI26] Lemma 6: adjacent labels are nested. -/
  nested : ∀ w : Role .complex 100, ∀ e ∈ edges w, labC e.1 ≤ labC e.2 ∨ labC e.2 ≤ labC e.1
  /-- Every edge residual has an orthonormal basis. -/
  onb : Lemma6OnbStmt
  /-- C2: `C_V = Π_{v∈B} K_v^{±1} C_U` for every orthonormal residual basis `B`. -/
  edge : Prop8EdgeStmt
  /-- Trivial routes: `C_0 = I`, `C_𝓕 = C^{⊗m}`. -/
  zero_full : Prop8ZeroFullStmt
  /-- C3: the corrected exceptional route is `C^{⊗mk}`. -/
  endpoint : Prop8EndpointStmt
  /-- Tensor powers over columns are multiplicative. -/
  tpow_mul : TpowMulStmt
  /-- The corrected framed execution is `C^{⊗mk}` on every role (Lemma A.10 (`lem:transfer-phase`) network part). -/
  array_corollary : ComplexArrayCorollaryStmt
  /-- C4: `Σ_e dim(residual) = s_c` (exact child count). -/
  count : ∑ w : Role .complex 100,
      ((edges w).map fun e => Module.finrank (ZMod 2) (residC e)).sum = tripleSc 100
  /-- `s_c < W_c m`. -/
  deficit : tripleSc 100 < tripleWc 100 * tripleM 100

end SubNLogN.Math.Networks
