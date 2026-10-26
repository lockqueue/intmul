import SubNLogN.Math.Networks.CellCalc

/-!
# Networks: the finite-network certificates for general `h` (bit: `h ≥ 7`, `h ≠ 9`; complex: `h ≥ 7`)

The `h = 100` contracts of `Labels.lean`, `BitFrames.lean`, `PhaseFrames.lean`, `CellCalc.lean`
restated for every admissible `h` (uniform proofs for `h ≥ 7`, excluding
`h = 9` for the rational-label network, whose factor form `I − J/9` is degenerate exactly at `h = 9`).
[OAI26] Lemma 5 (`Scalar.lean`), the frame invariant (`Framed.lean`) and the class counting
(`CellCalc.lean`) are already stated for every `h`. Each `…GenStmt h` specializes at `h = 100` to the
corresponding `h = 100` contract.
-/

namespace SubNLogN.Math.Networks

/-- [OAI26] Lemma 6 (bit), general `h`: every vertex label is nondegenerate. -/
def Lemma6NondegBitGenStmt (h : ℕ) : Prop :=
  ∀ v : Vertex .bit h, IsCompl (labB v) ((betaB3 h).orthogonal (labB v))

/-- [OAI26] Lemma 6 (complex), general `h`: every vertex label is nondegenerate. -/
def Lemma6NondegComplexGenStmt (h : ℕ) : Prop :=
  ∀ v : Vertex .complex h, IsCompl (labC v) ((betaC3 h).orthogonal (labC v))

/-- [OAI26] Lemma 6, general `h`: adjacent labels are nested (both networks). -/
def Lemma6NestedGenStmt (h : ℕ) : Prop :=
  (∀ w : Role .bit h, ∀ e ∈ edges w, labB e.1 ≤ labB e.2 ∨ labB e.2 ≤ labB e.1) ∧
  (∀ w : Role .complex h, ∀ e ∈ edges w, labC e.1 ≤ labC e.2 ∨ labC e.2 ≤ labC e.1)

/-- [OAI26] Lemma 6 (bit), general `h`: the decreasing edges are exactly the centre edges `3 → 4`, each
losing dimension `h` (iff form, as in [OAI26, §3.3, Lemma 6]). -/
def Lemma6DecreasingBitGenStmt (h : ℕ) : Prop :=
  ∀ (w : Role .bit h) (e : Vertex .bit h × Vertex .bit h), e ∈ edges w →
    ((¬ labB e.1 ≤ labB e.2) ↔
      ∃ j ι c, w = .center j ι c ∧ e = (.gate (.center j ι 3), .gate (.center j ι 4))) ∧
    (¬ labB e.1 ≤ labB e.2 → Module.finrank ℚ (labB e.1) = Module.finrank ℚ (labB e.2) + h)

/-- [OAI26] Lemma 6 (complex), general `h` (iff form). -/
def Lemma6DecreasingComplexGenStmt (h : ℕ) : Prop :=
  ∀ (w : Role .complex h) (e : Vertex .complex h × Vertex .complex h), e ∈ edges w →
    ((¬ labC e.1 ≤ labC e.2) ↔
      ∃ j ι c, w = .center j ι c ∧ e = (.gate (.center j ι 3), .gate (.center j ι 4))) ∧
    (¬ labC e.1 ≤ labC e.2 →
      Module.finrank (ZMod 2) (labC e.1) = Module.finrank (ZMod 2) (labC e.2) + h)

/-- Every complex edge residual has an orthonormal basis, general `h`. -/
def Lemma6OnbGenStmt (h : ℕ) : Prop :=
  ∀ (w : Role .complex h) (e : Vertex .complex h × Vertex .complex h), e ∈ edges w →
    ∃ B, IsONB (residC e) B

/-- B2 ([OAI26] Prop 7 endpoint), general `h`: `M_{sink ρ(w)} − M_{source w} = I`. -/
def Prop7EndpointGenStmt (h : ℕ) : Prop :=
  ∀ w : Role .bit h, frameB (.sink w.rho) - frameB (.source w) = 1

/-- C2 ([OAI26] Prop 8 edge factorization), general `h`. -/
def Prop8EdgeGenStmt (h : ℕ) : Prop :=
  ∀ (w : Role .complex h) (e : Vertex .complex h × Vertex .complex h), e ∈ edges w →
    ∀ B : List (Pt h), IsONB (residC e) B →
    frameC e.2 = (B.map fun v => Kv v (epsC e v)).prod * frameC e.1

/-- Trivial routes, general `h`: `C_0 = I`, `C_𝓕 = C^{⊗m}`. -/
def Prop8ZeroFullGenStmt (h : ℕ) : Prop :=
  ∀ w : Role .complex h,
    ((∀ a, w ≠ .X a) → frameC (.source w) = 1) ∧ ((∀ a, w ≠ .Y a) → frameC (.sink w) = Cfull)

/-- C3 (corrected exceptional route), general `h` (`wt u_a = 27` for every `h`). -/
def Prop8EndpointGenStmt (h : ℕ) : Prop :=
  ∀ (a : Addr h) (k : ℕ), 1 ≤ k →
    (Complex.I ^ (27 * k)) • (Zk k (ua a) * tpow k (frameC (.sink (.Y a))) *
      (tpow k (frameC (.source (.X a))))⁻¹ * Zk k (ua a)) = tpow k Cfull

/-- Cell soundness (bit), general `h`. -/
def SoundBitGenStmt (h : ℕ) : Prop :=
  ∀ w : Role .bit h,
    ((edges w).map fun e => rankQ (edgeMatB e)).sum = Cell.classRankSum h (Cell.classOf w)

/-- Cell soundness (complex), general `h`. -/
def SoundComplexGenStmt (h : ℕ) : Prop :=
  ∀ w : Role .complex h,
    ((edges w).map fun e => Module.finrank (ZMod 2) (residC e)).sum =
      Cell.classDimSum h (Cell.classOf w)

/-- B4, general `h`: `Σ_e rank_ℚ A_e = s_b(h)`. -/
def RankSumGenStmt (h : ℕ) : Prop :=
  ∑ w : Role .bit h, ((edges w).map fun e => rankQ (edgeMatB e)).sum = tripleSb h

/-- C4, general `h`: `Σ_e dim(residual) = s_c(h)`. -/
def CountGenStmt (h : ℕ) : Prop :=
  ∑ w : Role .complex h, ((edges w).map fun e => Module.finrank (ZMod 2) (residC e)).sum =
    tripleSc h

end SubNLogN.Math.Networks
