import SubNLogN.Math.Networks.AppCProc6
import SubNLogN.Math.Networks.Proofs.H2Final
import SubNLogN.Math.Networks.Proofs.AppCLeaves
import SubNLogN.Math.Networks.Proofs.AppCShearProofs
import SubNLogN.Math.Networks.Proofs.AppCLayerAlg
import SubNLogN.Math.Networks.Proofs.AppCAnalysis
import SubNLogN.Math.Networks.Proofs.PackedAgree
import SubNLogN.Math.Networks.Proofs.LayerCoreFacts
import SubNLogN.Math.Networks.Proofs.CxEdgeDataFacts
import SubNLogN.Math.Networks.Proofs.EdgeRealization
import SubNLogN.Math.Networks.Proofs.Deficit
import SubNLogN.Math.Networks.Proofs.InterchangeWFProof
import SubNLogN.Math.Networks.Proofs.PackedProcWF
import SubNLogN.Math.Networks.Proofs.CCoreWF
import SubNLogN.Math.Networks.Proofs.LayerSpecProof
import SubNLogN.Math.Networks.Proofs.PackedProc
import SubNLogN.Math.Networks.Proofs.Interchange6
import SubNLogN.Math.Networks.Proofs.InterchangeCorrect
import SubNLogN.Math.Networks.Proofs.CCoreCorrect

/-!
# Appendix A: final assembly (`app:parameter-transfer`)

Composes the Appendix A procedures (Proposition A.7 power-width interchange, Lemma A.8 arbitrary-width
interchange, Lemma A.9 packed addition, Lemma A.10 complex core, Proposition A.11 butterfly layer) with
the proved network certificates (`H2Final.lean`) and leaves. (`AppC`, `prop71`, and `C5` in identifiers/filenames
are historical prefixes retained for stability, corresponding to Appendix A, Proposition A.11, and Proposition A.7.) No statement
here concerns `FinTM2` time: `ProcK.cost` is the nominal model cost of `AppCModel.lean`.

## Contract discharge summary: contract → theorem used → file

| contract (`Stmt`) | discharged by | file (`Networks/Proofs/`) |
|---|---|---|
| `ComplexNetCert`, `BitNetCert` | `complexNetCert_holds`, `bitNetCert_holds` | `H2Final.lean` |
| `RunEightSpecStmt`, `PivotTripleEqStmt`, `ThreeShearsSwapStmt` | `runEightSpec_holds`, `pivotTripleEq_holds`, `threeShearsSwap_holds` | `AppCLeaves.lean` |
| `ShearFactorizationStmt`, `LinDLowerTriStreamingStmt`, `RatModMatrixMulStmt`, `InterchangeRecurrenceStmt` | `shearFactorization_holds`, `linDLowerTriStreaming_holds`, `ratModMatrixMul_holds`, `interchangeRecurrence_holds` | `AppCShearProofs.lean` |
| `ShearFacts` (the five Lemma A.6 (`lem:transfer-shear`) facts) | `AppCFinalAux.shearFacts_holds` | this file |
| `PackedAgreeStmt` | `packedAgree_holds` | `PackedAgree.lean` |
| `TranslationConjStmt`, `H0TensorIdentityStmt`, `Prop71FunctionalStmt`, `BinaryRowAdditionsStmt` | `translationConj_holds`, `h0TensorIdentity_holds`, `prop71Functional_holds`, `binaryRowAdditions_holds` | `AppCLayerAlg.lean` |
| `GuardGrowthStmt`, `GuardSmallStmt` | `guardGrowth_holds`, `guardSmall_holds` | `AppCAnalysis.lean` |
| `DecodeEncodeAddrStmt` | `decodeEncodeAddr_holds` | `LayerCoreFacts.lean` |
| `DeficitsH100Stmt` | `deficitsH100_holds` | `Deficit.lean` |
| `ExistsValidFacStmt` (radix `q`, factorizations `fac`) | `existsValidFac_holds` | `ValidFac.lean` |
| `ExistsValidCxDataStmt` (complex edge data) | `AppCFinalAux.existsValidCxData_holds` (from `WP6c.lemma6Onb_holds`, `basisExtension_holds 100`, `binaryRowAdditions_holds`) | this file; `CxEdgeDataFacts.lean`, `Lemma6COnb.lean`, `EdgeRealization.lean` |
| `Prop71LayerSpecStmt` | `prop71LayerSpec_holds` | `LayerSpecProof.lean` |
| `PackedProcCorrectStmt`, `PackedProcWFStmt` | `packedProcCorrect_holds`, `packedProcWF_holds` | `PackedProc.lean`, `PackedProcWF.lean` |
| `CCoreProcWFStmt` | `cCoreProcWF_holds` | `CCoreWF.lean` |
| `InterchangeProcWFStmt` | `interchangeProcWF_holds` | `InterchangeWFProof.lean` |
| `Interchange6CorrectStmt`, `InterchangeUCorrectStmt` (from Proposition A.7 correctness) | `interchange6Correct_holds`, `interchangeUCorrect_holds` | `Interchange6.lean` (with `Interchange6Binary.lean`) |
| `CCoreProcCorrectStmt` | `cCoreProcCorrect_holds` | `CCoreCorrect.lean` |
| **`Prop71GuardStmt`** | hypothesis `hGd` of `prop71_guard_of`, `prop71_of` | discharged in `AppCGuardFinal.lean` (`LayerGuard.lean`) |
| `InterchangeProcCorrectStmt` | `interchangeProcCorrect_holds` | `InterchangeCorrect.lean` |
| **`InterchangeProcCostStmt`** | hypothesis `hCost` of `interchange_cost_of` only | nominal model cost; machine step bounds are in `SubNLogN/Machine/` |

## Final statements
* `prop71_layerSpec` (unconditional): for every valid choice of complex edge data the layer
  procedure is exact (`LayerSpec`) on every admissible tuple; `prop71_guard_of hGd`: guards in the
  bands; `prop71_of hGd`: one valid choice with both.
* `cCoreProc_correct` (Lemma A.10 (`lem:transfer-phase`) exactness) and `cCoreProc_wf` (well-formedness), unconditional.
* `packedAdd_correct`, `packedAdd_wf` (Lemma A.9 (`lem:transfer13`), unconditional).
* `interchange` (unconditional): one odd prime `q` and factorizations `fac` for which Proposition A.7 and both
  Lemma A.8 procedures are the interchanges; `interchange_wf` (Proposition A.7 well-formedness, unconditional);
  `interchange_cost_of hCost` (Proposition A.7 nominal cost; the only use of `InterchangeProcCostStmt`).
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh SubNLogN.Math.Common

namespace AppCFinalAux

/-- The Lemma A.6 (`lem:transfer-shear`) shear facts used by Proposition A.7 (`prop:transfer11`), all proved. -/
theorem shearFacts_holds : ShearFacts :=
  ⟨pivotTripleEq_holds, shearFactorization_holds, linDLowerTriStreaming_holds,
    ratModMatrixMul_holds, threeShearsSwap_holds⟩

/-- Valid complex edge data exist ([OAI26] Lemma 6 orthonormal bases, basis extension, row additions). -/
theorem existsValidCxData_holds : ExistsValidCxDataStmt :=
  existsValidCxData_of WP6c.lemma6Onb_holds (basisExtension_holds 100) binaryRowAdditions_holds

/-- The layout part of `InterchangeHyps` (everything except the parameter part `C5Params`). -/
def InterchangeLayout (L : Layout) (q k h₀ d₀ : ℕ) (c : RowClass L) : Prop :=
  (∀ i : Fin L.n, (h₀ ≤ i.val ∧ i.val < h₀ + mH ^ k) ∨ (d₀ ≤ i.val ∧ i.val < d₀ + mH ^ k) →
    L.r i = q) ∧
  h₀ + mH ^ k ≤ d₀ ∧ d₀ + mH ^ k ≤ L.n ∧ c.row.val < h₀ ∧ c.μ * Wb ^ k ∣ L.r c.row

theorem interchangeHyps_of {L : Layout} {q : ℕ} {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    {k h₀ d₀ : ℕ} {c : RowClass L} (hq : C5Params q fac) (hL : InterchangeLayout L q k h₀ d₀ c) :
    InterchangeHyps L q fac k h₀ d₀ c :=
  ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, hL⟩

end AppCFinalAux

/-! ## Proposition A.11 (`prop:prop14-param`): layer value semantics and guards -/

/-- **Proposition A.11, value level** (unconditional): for every valid choice of complex edge data the
layer procedure returns exactly `Q_P(Hz)` on every disk-grid input, for every tuple with `K ≥ 6`,
`1 ≤ D ≤ d`. -/
theorem prop71_layerSpec :
    ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
      (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ (P d rr K D A S : ℕ) (ρ : Fin K), 6 ≤ K → 1 ≤ D → D ≤ d →
      LayerSpec P rr A K D S ρ (layerRun P A K D S rr ρ.val d cdat) :=
  prop71LayerSpec_holds complexNetCert_holds cCoreProcCorrect_holds runEightSpec_holds
    packedAgree_holds
    packedProcCorrect_holds translationConj_holds h0TensorIdentity_holds prop71Functional_holds
    decodeEncodeAddr_holds

/-- **Proposition A.11, guards**, from the guard contract (`Prop71GuardStmt`): for every valid choice of complex edge
data, in the bands, all intermediate arrays of a layer run are on the guard grid. -/
theorem prop71_guard_of (hGd : Prop71GuardStmt) :
    ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
      (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ (aD bD : ℝ), 0 < aD → aD ≤ bD → ∃ P₀ : ℝ, ∀ (P d rr K D A S : ℕ) (ρ : Fin K)
      (z : RArr (LayerAddr A K D S) rr),
      P₀ ≤ P → aD * (P : ℝ) ^ ((1 : ℝ) / 15) ≤ d → (d : ℝ) ≤ bD * (P : ℝ) ^ ((1 : ℝ) / 15) →
      K = ⌊(d : ℝ) ^ c46⌋₊ → 1 ≤ D → D ≤ d → ArrOnDiskGrid P z →
        LayerGuarded P A K D S rr ρ.val d ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ cdat z :=
  hGd complexNetCert_holds guardGrowth_holds guardSmall_holds

/-- **Proposition A.11, final form**: there is ONE valid choice `cdat` of complex edge data for which the
layer procedure is exact (`LayerSpec`) on every admissible tuple and all its intermediate arrays are
guarded in the bands. Remaining hypothesis: the guard contract. -/
theorem prop71_of (hGd : Prop71GuardStmt) :
    ∃ cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData,
      (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) ∧
      (∀ (P d rr K D A S : ℕ) (ρ : Fin K), 6 ≤ K → 1 ≤ D → D ≤ d →
        LayerSpec P rr A K D S ρ (layerRun P A K D S rr ρ.val d cdat)) ∧
      (∀ (aD bD : ℝ), 0 < aD → aD ≤ bD → ∃ P₀ : ℝ, ∀ (P d rr K D A S : ℕ) (ρ : Fin K)
        (z : RArr (LayerAddr A K D S) rr),
        P₀ ≤ P → aD * (P : ℝ) ^ ((1 : ℝ) / 15) ≤ d → (d : ℝ) ≤ bD * (P : ℝ) ^ ((1 : ℝ) / 15) →
        K = ⌊(d : ℝ) ^ c46⌋₊ → 1 ≤ D → D ≤ d → ArrOnDiskGrid P z →
          LayerGuarded P A K D S rr ρ.val d ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ cdat z) := by
  obtain ⟨cdat, hv⟩ := AppCFinalAux.existsValidCxData_holds
  exact ⟨cdat, hv, prop71_layerSpec cdat hv, prop71_guard_of hGd cdat hv⟩

/-! ## Lemma A.10 (`lem:transfer-phase`): the exact C-core -/

/-- **Lemma A.10 (`lem:transfer-phase`) core exactness** (unconditional). -/
theorem cCoreProc_correct :
    ∀ (A K D S rr kLeaf : ℕ) (ρ : Fin K)
      (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
      (k j0 : ℕ) (c : RowClass (layerLayout A K D S)) (h : j0 + mH ^ k ≤ D),
      CCoreHyps A K D S ρ.val cdat k j0 c → ∀ z : RArr (LayerAddr A K D S) rr,
        decodeArr (ProcK.run k (cCoreProc A K D S rr ρ.val kLeaf cdat k j0) c (encodeArr z)) =
          fun x => if c.mem (encodeAddr x) then cCoreVal ρ j0 (mH ^ k) h z x else z x :=
  cCoreProcCorrect_holds complexNetCert_holds runEightSpec_holds packedAgree_holds
    packedProcCorrect_holds translationConj_holds

/-- **Lemma A.10 (`lem:transfer-phase`) core well-formedness** (unconditional): every primitive of the C-core satisfies its side
condition (radix bound `2`). -/
theorem cCoreProc_wf :
    ∀ (A K D S rr ρ kLeaf : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
      (k j0 : ℕ) (c : RowClass (layerLayout A K D S)), CCoreHyps A K D S ρ cdat k j0 c →
        ProcK.WF 2 k (cCoreProc A K D S rr ρ kLeaf cdat k j0) :=
  cCoreProcWF_holds complexNetCert_holds packedAgree_holds

/-! ## Lemma A.9 (`lem:transfer13`): packed selected-bit addition -/

/-- **Lemma A.9 (`lem:transfer13`) correctness** (unconditional). -/
theorem packedAdd_correct :
    ∀ (Ly : Layout) (β : Type) (L K ρ f : ℕ) (C : Chunks3), PackedHyps Ly L K ρ f C →
      ∀ (c : RowClass Ly), (c.row.val < C.px ∨ C.px + L ≤ c.row.val) →
        (c.row.val < C.py ∨ C.py + L ≤ c.row.val) → (c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) →
      ∀ (A : Ly.Addr → β),
        ProcK.run 0 (packedAddProc (Ly := Ly) (β := β) L K ρ f C) c A =
          fun a => if c.mem a then A (addrXorAll L K ρ f C a) else A a :=
  packedProcCorrect_holds runEightSpec_holds packedAgree_holds

/-- **Lemma A.9 (`lem:transfer13`) well-formedness** (unconditional). -/
theorem packedAdd_wf :
    ∀ (Ly : Layout) (β : Type) (L K ρ f : ℕ) (C : Chunks3), PackedHyps Ly L K ρ f C →
      ProcK.WF 2 0 (packedAddProc (Ly := Ly) (β := β) L K ρ f C) :=
  packedProcWF_holds packedAgree_holds

/-! ## Proposition A.7 (`prop:transfer11`) and Lemma A.8 (`lem:transfer12`): interchanges, with the proved radix data -/

/-- **Proposition A.7 (`prop:transfer11`) and Lemma A.8 (`lem:transfer12`), final form**: there are ONE odd prime `q` and ONE family of factorizations `fac`
(valid for every edge matrix of the bit network, all frame entries `q`-integral) such that
* (Proposition A.7) `interchangeProc q fac k h₀ d₀` interchanges the two chunks of `m^k` radix-`q` digit fields
  in every admissible class (`InterchangeLayout`);
* (Lemma A.8, q-ary) `interchangeQ` interchanges two disjoint chunks of `len` radix-`q` fields;
* (Lemma A.8, binary) `interchangeU` interchanges two disjoint chunks of `u` binary fields;
for every layout, payload (`𝔽₂`-module) and data. Unconditional. -/
theorem interchange :
    ∃ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData), C5Params q fac ∧
      (∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β] (k h₀ d₀ : ℕ)
        (c : RowClass L), AppCFinalAux.InterchangeLayout L q k h₀ d₀ c → ∀ A : L.Addr → β,
          ProcK.run k (interchangeProc (L := L) (β := β) q fac k h₀ d₀) c A =
            (Step.swapBlocks h₀ d₀ (mH ^ k) : Step L β).runIn c A) ∧
      (∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β] (len t₀ s₀ : ℕ),
        TwoBlocks L q len t₀ s₀ → ∀ A : L.Addr → β,
          interchangeQ L β q fac len t₀ s₀ A = (Step.swapBlocks t₀ s₀ len : Step L β).run A) ∧
      (∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β] (u t₀ s₀ : ℕ),
        TwoBlocks L 2 u t₀ s₀ → ∀ A : L.Addr → β,
          interchangeU L β q fac u t₀ s₀ A = (Step.swapBlocks t₀ s₀ u : Step L β).run A) := by
  obtain ⟨q, fac, hq⟩ := existsValidFac_holds
  refine ⟨q, fac, hq, ?_, ?_, ?_⟩
  · intro L β _ _ k h₀ d₀ c hL A
    exact interchangeProcCorrect_holds bitNetCert_holds AppCFinalAux.shearFacts_holds L β q fac k h₀ d₀ c
      (AppCFinalAux.interchangeHyps_of hq hL) A
  · intro L β _ _ len t₀ s₀ hb A
    exact interchange6Correct_holds bitNetCert_holds AppCFinalAux.shearFacts_holds
      interchangeProcCorrect_holds L β q fac len
      t₀ s₀ hq hb A
  · intro L β _ _ u t₀ s₀ hb A
    exact interchangeUCorrect_holds bitNetCert_holds AppCFinalAux.shearFacts_holds
      interchangeProcCorrect_holds L β q fac u
      t₀ s₀ hq hb A

/-- **Proposition A.7 (`prop:transfer11`) well-formedness** (unconditional): every primitive of `interchangeProc` satisfies its
side condition (radix bound `q`). -/
theorem interchange_wf :
    ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
      (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) (c : RowClass L),
      InterchangeHyps L q fac k h₀ d₀ c →
        ProcK.WF q k (interchangeProc (L := L) (β := β) q fac k h₀ d₀) :=
  interchangeProcWF_holds

/-- **Proposition A.7 (`prop:transfer11`) nominal model cost**, from the nominal cost contract
(`ProcK.cost`; machine-level step bounds are proved in `SubNLogN/Machine/`); the bound uses the proved
`BitNetCert`, `DeficitsH100Stmt` (`τ = 1 − 2^{−40}`) and `InterchangeRecurrenceStmt`. -/
theorem interchange_cost_of (hCost : InterchangeProcCostStmt) :
    ∀ P : CostParams, 0 ≤ P.c₀ →
      ∃ C : ℝ, ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
        (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) (c : RowClass L),
        InterchangeHyps L q fac k h₀ d₀ c → 0 ≤ P.w →
          ProcK.cost P k (interchangeProc (L := L) (β := β) q fac k h₀ d₀) c ≤
            C * c.vol P * ((mH ^ k : ℕ) : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 40) :=
  hCost bitNetCert_holds deficitsH100_holds interchangeRecurrence_holds

end SubNLogN.Math.Networks
