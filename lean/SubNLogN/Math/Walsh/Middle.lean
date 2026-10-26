import SubNLogN.Math.Walsh.DirectFFT
import SubNLogN.Math.Common.MiddleContract

/-!
# The Walsh middle transform meets the middle-transform contract (Corollary 6.6)

Paper: Corollary 6.6 (`cor:walsh-middle`, Section 6.5 (`sec:direct-fft-bridge`)) and the
accompanying discussion in Section 6.5; Definition 4.5 (`def:middle-contract`),
encoded as `SubNLogN.Math.Common.IsMiddleTransform` (grid precision `q = P + 2`).

`walshMiddle layer q D ℓ K a` is Theorem 6.5's procedure at precision `q` with the concrete phase
table of Lemma 6.1 (`phaseTable q ℓ`), as a map on tensors indexed by digit tuples.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-- The *ideal layer oracle*: every call returns exactly `Q_P(H z)`, the value-level output of
Proposition A.11. It satisfies `LayerSpec` by definition (`idealLayer_spec`), hence
`WalshLayerOK idealLayer` (`walshLayerOK_idealLayer`); the machine layer (`SubNLogN.Machine`) computes its
values at the call shapes listed in `WalshLayerOK`. -/
noncomputable def idealLayer : LayerOracle :=
  fun P _ _ _ _ _ ρ z => truncArr P (layerH ρ z)

/-- The ideal oracle satisfies `LayerSpec` at every precision, shape and bit. -/
theorem idealLayer_spec (P r A K D S : ℕ) (ρ : Fin K) :
    LayerSpec P r A K D S ρ (idealLayer P r A K D S ρ) :=
  fun _ _ => rfl

/-- The ideal oracle satisfies `WalshLayerOK` for every parameter choice. -/
theorem walshLayerOK_idealLayer (P D ℓ K : ℕ) (a : Fin D → ℕ) :
    WalshLayerOK idealLayer P D ℓ K a :=
  ⟨fun _ _ _ _ => idealLayer_spec _ _ _ _ _ _ _,
    fun _ _ _ _ _ _ _ => idealLayer_spec _ _ _ _ _ _ _⟩

/-- The Walsh middle transform at grid precision `q`: Theorem 6.5's procedure with the table of
Lemma 6.1, on tensors in natural order. -/
noncomputable def walshMiddle (layer : LayerOracle) (q D ℓ K : ℕ) (a : Fin D → ℕ) :
    (Idx (fftShape a ℓ) → ℂ) → (Idx (fftShape a ℓ) → ℂ) :=
  fun U => toTensor a ℓ (directFFT layer q D ℓ K a (phaseTable q ℓ) (ofTensor a ℓ U))

/-- **Corollary 6.6** (Walsh middle transform, `cor:walsh-middle`, Section 6.5 (`sec:direct-fft-bridge`)): the Walsh middle
transform at grid precision `q = P + 2` (`P` = the bridge working precision, as built into
`IsMiddleTransform`) is a middle transform (Definition 4.5) with `E_mid = 12ℓ` and `δ_mid = 0`.
Hypotheses. Paper hypotheses of Theorem 6.5 at `q` (shape and size conditions, kept verbatim):
`q ≥ 8` (`8 ≤ P + 2`), `2 ≤ ℓ < q`, `d = D + 1 ≥ 2` (`1 ≤ D`), `1 ≤ K ≤ ℓ - 1`, and the balanced
shape `t_i = 2^{a_i} ∈ {r/2, r}` for the record axes with `t_d = r = 2^ℓ` (encoded by `fftShape a ℓ`
and `a_i ∈ {ℓ-1, ℓ}`). Non-paper (reformulated) hypothesis: `WalshLayerOK layer q D ℓ K a`, i.e.
`LayerSpec` for every layer call made (chunk rounds at `q`, CNOT batches at `q + 8d`); it replaces
the fixed network premises (Definition A.1 (`def:fixed-network-premises`)) and the parameter bands of Proposition A.11 at `q` (and, via Lemma 5.3, at `q + 8d`).
Dropped (machine level only): `dℓ ≤ C_ℓ q`, the time bound. CONTRACT (proved in `Walsh/Proofs/Middle.lean`). -/
def WalshMiddleStmt : Prop :=
  ∀ (layer : LayerOracle) (P D ℓ K : ℕ) (a : Fin D → ℕ),
    8 ≤ P + 2 → 1 ≤ D → 2 ≤ ℓ → ℓ < P + 2 → 1 ≤ K → K ≤ ℓ - 1 →
    (∀ i, a i = ℓ - 1 ∨ a i = ℓ) → WalshLayerOK layer (P + 2) D ℓ K a →
    IsMiddleTransform (fftShape a ℓ) P (12 * (ℓ : ℝ)) 0 (walshMiddle layer (P + 2) D ℓ K a)

/-- **Corollary 6.6 for the ideal oracle** (target statement of the Walsh wiring,
`cor:walsh-middle`): for the paper's shape and size hypotheses of Theorem 6.5 at the grid
precision `q = P + 2` (`q ≥ 8`, `2 ≤ ℓ < q`, `d = D + 1 ≥ 2`, `1 ≤ K ≤ ℓ - 1`, `a_i ∈ {ℓ-1, ℓ}`),
the Walsh middle transform built from `idealLayer` is a middle transform (Definition 4.5) with
`E_mid = 12ℓ` and `δ_mid = 0`. Proved unconditionally as `walsh_middle_ideal` in
`Walsh/Proofs/Wiring.lean` (from `walsh_middle_ideal_of_direct_fft` and `direct_fft`). -/
def WalshMiddleIdealStmt : Prop :=
  ∀ (P D ℓ K : ℕ) (a : Fin D → ℕ), 8 ≤ P + 2 → 1 ≤ D → 2 ≤ ℓ → ℓ < P + 2 → 1 ≤ K →
    K ≤ ℓ - 1 → (∀ i, a i = ℓ - 1 ∨ a i = ℓ) →
    IsMiddleTransform (fftShape a ℓ) P (12 * (ℓ : ℝ)) 0 (walshMiddle idealLayer (P + 2) D ℓ K a)

end SubNLogN.Math.Walsh
