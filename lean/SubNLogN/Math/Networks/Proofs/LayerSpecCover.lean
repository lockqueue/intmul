import SubNLogN.Math.Networks.Proofs.LayerSpecProof
import SubNLogN.Math.Walsh.DirectFFT

/-!
# Proposition A.11: strong functional form and coverage of the layer call sites

* `prop71LayerSpec_all`: `Prop71LayerSpecStmt` without the hypotheses `H0TensorIdentityStmt` and
  `1 ≤ D` (for every `D ≤ d`, any band parameter `d`). Proof: `LayerSpecAux.layerSpec_strong`
  (`LayerSpecProof.lean`).
* `prop71LayerSpec_self`: the band parameter may be the call's own chunk count (`d := D`).
* `LayerSpecCoverAux.layerOracle cdat`: the explicit layer procedure as a `LayerOracle` (band
  parameter `d := D` at every call); `layerOracle_spec`: it satisfies `LayerSpec` at every call with
  `K ≥ 6`; `walshLayerOK_layerOracle`: hence `WalshLayerOK` (chunk rounds with `D` chunks at
  `P`, CNOT batches with `1 ≤ D' ≤ D + 1` chunks at `P + 8(D+1)`) for every `K ≥ 6`.
* `six_le_floor_rpow`: in the bands (`a_d P^ε ≤ d`, `K = ⌊d^c⌋`, `c, ε, a_d > 0`) one has `K ≥ 6`
  for all `P ≥ P₀` (pure real analysis), so the hypothesis `6 ≤ K` is available in the bands of
  Proposition A.11 (`Machine/Contracts/Layer.lean`, `LayerBands`) after enlarging the cutoff;
  `six_le_K_row46` is the instance `c = c46`, `ε = 1/15` (the bands of `Prop71GuardStmt`).
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- **Proposition A.11, functional, strong form** (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)):
for valid complex edge data, `K ≥ 6` and `D ≤ d`, the layer procedure returns exactly `Q_P(Hz)` on
every disk-grid input. Compared with `Prop71LayerSpecStmt`, the hypotheses `H0TensorIdentityStmt`
and `1 ≤ D` are dropped. -/
theorem prop71LayerSpec_all : ComplexNetCert → CCoreProcCorrectStmt → RunEightSpecStmt →
    PackedAgreeStmt → PackedProcCorrectStmt → TranslationConjStmt → Prop71FunctionalStmt →
    DecodeEncodeAddrStmt →
    ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
      (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ (P d rr K D A S : ℕ) (ρ : Fin K), 6 ≤ K → D ≤ d →
      LayerSpec P rr A K D S ρ (layerRun P A K D S rr ρ.val d cdat) :=
  LayerSpecAux.layerSpec_strong

/-- **Proposition A.11 with band parameter `d := D`** (the call's own chunk count). -/
theorem prop71LayerSpec_self (hcert : ComplexNetCert) (hCC : CCoreProcCorrectStmt)
    (hR8 : RunEightSpecStmt) (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt)
    (hTC : TranslationConjStmt) (hFun : Prop71FunctionalStmt) (hDE : DecodeEncodeAddrStmt)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hcdat : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (P rr K D A S : ℕ) (ρ : Fin K) (hK : 6 ≤ K) :
    LayerSpec P rr A K D S ρ (layerRun P A K D S rr ρ.val D cdat) :=
  prop71LayerSpec_all hcert hCC hR8 hPA hPP hTC hFun hDE cdat hcdat P D rr K D A S ρ hK le_rfl

namespace LayerSpecCoverAux

/-- The explicit layer procedure as a `LayerOracle`; every call uses its own chunk count as the
band parameter (`d := D`). -/
noncomputable def layerOracle (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    LayerOracle :=
  fun P r A K D S ρ => layerRun P A K D S r ρ.val D cdat

end LayerSpecCoverAux

/-- The layer oracle satisfies `LayerSpec` at every call with `K ≥ 6`. -/
theorem layerOracle_spec (hcert : ComplexNetCert) (hCC : CCoreProcCorrectStmt)
    (hR8 : RunEightSpecStmt) (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt)
    (hTC : TranslationConjStmt) (hFun : Prop71FunctionalStmt) (hDE : DecodeEncodeAddrStmt)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hcdat : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (P r A K D S : ℕ) (ρ : Fin K) (hK : 6 ≤ K) :
    LayerSpec P r A K D S ρ (LayerSpecCoverAux.layerOracle cdat P r A K D S ρ) :=
  prop71LayerSpec_self hcert hCC hR8 hPA hPP hTC hFun hDE cdat hcdat P r K D A S ρ hK

/-- **`WalshLayerOK` for the explicit layer procedure** (`DirectFFT.lean`): for `K ≥ 6`, every
chunk round (`D` chunks at precision `P`) and every CNOT batch inside the positional maps
(`1 ≤ D' ≤ D + 1` chunks at precision `P + 8(D+1)`) satisfies `LayerSpec`. -/
theorem walshLayerOK_layerOracle (hcert : ComplexNetCert) (hCC : CCoreProcCorrectStmt)
    (hR8 : RunEightSpecStmt) (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt)
    (hTC : TranslationConjStmt) (hFun : Prop71FunctionalStmt) (hDE : DecodeEncodeAddrStmt)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hcdat : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (P D ℓ K : ℕ) (a : Fin D → ℕ) (hK : 6 ≤ K) :
    WalshLayerOK (LayerSpecCoverAux.layerOracle cdat) P D ℓ K a :=
  ⟨fun j₀ nS ρ _ => layerOracle_spec hcert hCC hR8 hPA hPP hTC hFun hDE cdat hcdat
      P (2 ^ ℓ) (2 ^ j₀) K D (2 ^ nS) ρ hK,
    fun j₀ D' nS ρ _ _ _ => layerOracle_spec hcert hCC hR8 hPA hPP hTC hFun hDE cdat hcdat
      (P + 8 * (D + 1)) (2 ^ ℓ) (2 ^ j₀) K D' (2 ^ nS) ρ hK⟩

/-- **`K ≥ 6` in the bands** (pure real analysis): for `a_d, c, ε > 0` there is `P₀` such that
`a_d P^ε ≤ d` and `P ≥ P₀` imply `6 ≤ ⌊d^c⌋₊`. With `K = ⌊d^c⌋₊` (`LayerBands`,
`Prop71GuardStmt`) this supplies the hypothesis `6 ≤ K` above the cutoff. -/
theorem six_le_floor_rpow (a_d c ε : ℝ) (had : 0 < a_d) (hc : 0 < c) (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P d : ℕ, P₀ ≤ P → a_d * (P : ℝ) ^ ε ≤ d → 6 ≤ ⌊(d : ℝ) ^ c⌋₊ := by
  have hY0 : 0 < (6 : ℝ) ^ c⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hYa : 0 < (6 : ℝ) ^ c⁻¹ / a_d := div_pos hY0 had
  have hX0 : 0 ≤ ((6 : ℝ) ^ c⁻¹ / a_d) ^ ε⁻¹ := Real.rpow_nonneg hYa.le _
  refine ⟨⌈((6 : ℝ) ^ c⁻¹ / a_d) ^ ε⁻¹⌉₊, fun P d hP hd => ?_⟩
  have hPX : ((6 : ℝ) ^ c⁻¹ / a_d) ^ ε⁻¹ ≤ (P : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hP)
  have h1 : (6 : ℝ) ^ c⁻¹ / a_d ≤ (P : ℝ) ^ ε := by
    have := Real.rpow_le_rpow hX0 hPX hε.le
    rwa [Real.rpow_inv_rpow hYa.le hε.ne'] at this
  have h2 : (6 : ℝ) ^ c⁻¹ ≤ (d : ℝ) := by
    have h1' : (6 : ℝ) ^ c⁻¹ ≤ (P : ℝ) ^ ε * a_d := (div_le_iff₀ had).1 h1
    have hcomm : (P : ℝ) ^ ε * a_d = a_d * (P : ℝ) ^ ε := mul_comm _ _
    linarith
  have h3 : (6 : ℝ) ≤ (d : ℝ) ^ c := by
    have := Real.rpow_le_rpow hY0.le h2 hc.le
    rwa [Real.rpow_inv_rpow (by norm_num) hc.ne'] at this
  exact Nat.le_floor (by exact_mod_cast h3)

namespace LayerSpecCoverAux

theorem c46_pos : 0 < c46 := by
  unfold c46 xi46; positivity

end LayerSpecCoverAux

/-- **`K ≥ 6` at the `κ = 2^{-46}` row** (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`), the bands of `Prop71GuardStmt`):
for `a_d > 0` there is `P₀` such that `P ≥ P₀`, `a_d P^{1/15} ≤ d` and `K = ⌊d^{c46}⌋₊` imply
`6 ≤ K`. -/
theorem six_le_K_row46 (aD : ℝ) (haD : 0 < aD) :
    ∃ P₀ : ℕ, ∀ P d K : ℕ, P₀ ≤ P → aD * (P : ℝ) ^ ((1 : ℝ) / 15) ≤ d →
      K = ⌊(d : ℝ) ^ c46⌋₊ → 6 ≤ K := by
  obtain ⟨P₀, hP₀⟩ := six_le_floor_rpow aD c46 ((1 : ℝ) / 15) haD LayerSpecCoverAux.c46_pos
    (by norm_num)
  exact ⟨P₀, fun P d K hP hd hK => hK ▸ hP₀ P d hP hd⟩

end SubNLogN.Math.Networks
