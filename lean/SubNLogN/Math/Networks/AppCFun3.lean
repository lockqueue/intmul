import SubNLogN.Math.Networks.AppCLayer

/-!
# Networks: functional specifications for Lemma A.10 (`lem:transfer-phase`) edges and for the layer assembly (Proposition A.11)

1. **Edge realization** (Lemma A.10 (`lem:transfer-phase`)): extend an orthonormal residual basis
   `B` to an invertible binary matrix `M` (columns at distinct coordinates `cs` equal to `B`); then
   the edge operator `Π_{v∈B} K_v^{±1}` equals `P_M (Π_i K_{e_{cs_i}}^{±1}) P_M⁻¹`, i.e. one
   coordinate kernel per residual vector (one child `C^{⊗f}` on slot `cs_i`, `KernelSlotStmt`)
   between the two move permutations `P_M`, `P_M⁻¹` (row additions, `BinaryRowAdditionsStmt`).
2. **Basis extension**: a linearly independent family of binary vectors extends to such an `M`.
3. **Layer assembly** (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`), eq. (`eq:oai-h0-transfer`)): `C` on a set `S`
   of selected bits (`CDon S`); `CDon` of disjoint sets compose to their union, `CDon univ = C^{⊗D}`,
   and on one bit it is the individual kernel `C(u,v) = ((u+v+i(u−v))/2, (u+v−i(u−v))/2)`. Hence
   `C^{⊗D}` = individual kernels on the first `q₀` chunks' bits ∘ C-core calls on the base-`m`
   pieces, in any order.
-/

namespace SubNLogN.Math.Networks

/-! ## 1-2. Lemma A.10 (`lem:transfer-phase`) edges -/

/-- CONTRACT (edge realization by conjugation, Lemma A.10 (`lem:transfer-phase`)). -/
def EdgeRealizationStmt (h : ℕ) : Prop :=
  ∀ (B : List (Pt h)) (ε : Pt h → ℤ) (M M' : Matrix (Cube h) (Cube h) (ZMod 2)) (cs : List (Cube h)),
    M * M' = 1 → B.length = cs.length →
    (∀ (i : ℕ) (hi : i < B.length) (hc : i < cs.length),
      M.mulVec (Pi.single (cs.get ⟨i, hc⟩) 1) = B.get ⟨i, hi⟩) →
    (B.map fun v => Kv v (ε v)).prod =
      permOp M * ((B.zip cs).map fun p => Kv (Pi.single p.2 1) (ε p.1)).prod * permOp M'

/-- CONTRACT (basis extension). A linearly independent list of binary vectors is the list of
columns, at distinct coordinates, of an invertible binary matrix. -/
def BasisExtensionStmt (h : ℕ) : Prop :=
  ∀ B : List (Pt h), LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i) →
    ∃ (cs : List (Cube h)) (M M' : Matrix (Cube h) (Cube h) (ZMod 2)),
      cs.Nodup ∧ cs.length = B.length ∧ M * M' = 1 ∧
      ∀ (i : ℕ) (hi : i < B.length) (hc : i < cs.length),
        M.mulVec (Pi.single (cs.get ⟨i, hc⟩) 1) = B.get ⟨i, hi⟩

/-! ## 3. Layer assembly -/

/-- `C` applied on the selected bits in `S` only (identity on the other selected bits). -/
noncomputable def CDon {D : ℕ} (S : Finset (Fin D)) (z : (Fin D → Bool) → ℂ) :
    (Fin D → Bool) → ℂ := fun e =>
  ∑ e' : Fin D → Bool,
    (if ∀ j, j ∉ S → e j = e' j then ∏ j ∈ S, (if e j = e' j then ka else kb) else 0) * z e'

/-- CONTRACT (tensor factorization of `C^{⊗D}` over disjoint groups of selected bits, and the
individual kernel). -/
def CDonStmt : Prop :=
  (∀ (D : ℕ) (z : (Fin D → Bool) → ℂ), CDon Finset.univ z = CD D z) ∧
  (∀ (D : ℕ) (z : (Fin D → Bool) → ℂ), CDon (∅ : Finset (Fin D)) z = z) ∧
  (∀ (D : ℕ) (S T : Finset (Fin D)) (z : (Fin D → Bool) → ℂ), Disjoint S T →
    CDon S (CDon T z) = CDon (S ∪ T) z) ∧
  (∀ (D : ℕ) (j : Fin D) (z : (Fin D → Bool) → ℂ) (e : Fin D → Bool),
    CDon {j} z e =
      let u := z (Function.update e j false)
      let v := z (Function.update e j true)
      if e j = false then (u + v + Complex.I * (u - v)) / 2 else (u + v - Complex.I * (u - v)) / 2)

end SubNLogN.Math.Networks
