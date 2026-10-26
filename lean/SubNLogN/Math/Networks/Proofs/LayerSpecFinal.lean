import SubNLogN.Math.Networks.Proofs.LayerSpecProof
import SubNLogN.Math.Networks.Proofs.AppCLayerAlg
import SubNLogN.Math.Networks.Proofs.AppCLeaves
import SubNLogN.Math.Networks.Proofs.PackedAgree
import SubNLogN.Math.Networks.Proofs.PackedProc
import SubNLogN.Math.Networks.Proofs.CCoreCorrect
import SubNLogN.Math.Networks.Proofs.H2Final

/-!
# Proposition A.11 (`prop:prop14-param`), value level, unconditional

All premises of `LayerSpecAux.layerSpec_strong` are now proved (`complexNetCert_holds`,
`cCoreProcCorrect_holds`, `runEightSpec_holds`, `packedAgree_holds`, `packedProcCorrect_holds`,
`translationConj_holds`, `LayerSpecPadAux.decodeEncodeAddr_holds`; the value-level identity
`H₀^{⊗D} = b^D 𝒮_D C^{⊗D} 𝒮_D` is `h0TensorIdentity_holds`).

* `layerRun_eq_trunc_layerH`: for valid complex edge data, `K ≥ 6` and `D ≤ d`, the layer procedure
  returns exactly `Q_P(H z)` for **every** array `z` (no disk or grid condition): its value is
  `Q_P(b^D 𝒮_D C^{⊗D} 𝒮_D z)` (`LayerSpecFinalAux.layerRun_eq_key`, the phase computation of
  `LayerSpecProof.lean`) and `b^D 𝒮_D C^{⊗D} 𝒮_D = H₀^{⊗D}` on the selected bits
  (`LayerSpecFinalAux.functional_eq`, the computation of `prop71Functional_holds` without its unused
  disk-grid hypothesis).
* `prop71LayerSpec_unconditional`: hence `LayerSpec` for every `D ≤ d`, with no `…Stmt`
  hypotheses (`Prop71LayerSpecStmt` is discharged a fortiori).

Helpers live in `SubNLogN.Math.Networks.LayerSpecFinalAux`.
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh SubNLogN.Math.Common

namespace LayerSpecFinalAux

/-- `Q_P(b^D 𝒮_D Csch 𝒮_D z) = Q_P(H z)` for every array `z`, whenever `Csch` is `C^{⊗D}` on the
selected bits (the computation of `prop71Functional_holds`; no disk-grid hypothesis). -/
theorem functional_eq {P r A K D S : ℕ} (ρ : Fin K)
    (Csch : RArr (LayerAddr A K D S) r → RArr (LayerAddr A K D S) r)
    (hC : ∀ z x₀ e₀ k, Csch z (setSelBits ρ x₀ e₀) k = CD D (fun e => z (setSelBits ρ x₀ e) k) e₀)
    (z : RArr (LayerAddr A K D S) r) :
    truncArr P (fun x k => bD D *
      (Complex.I ^ (Finset.univ.filter fun j => x.2.1 j ρ = true).card *
        Csch (fun y k' => Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card *
          z y k') x k)) = truncArr P (layerH ρ z) := by
  congr 1
  funext x k
  have h1 := hC (fun y k' => Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card *
    z y k') x (fun j => x.2.1 j ρ) k
  rw [AppCLayerAlg.setSelBits_self] at h1
  rw [h1]
  simp only [AppCLayerAlg.setSelBits_sel]
  have h2 := congrFun (h0TensorIdentity_holds D (fun e => z (setSelBits ρ x e) k))
    (fun j => x.2.1 j ρ)
  simp only [H0D, SD, Pi.smul_apply, smul_eq_mul] at h2
  exact h2.symm

/-- The value of the layer procedure: `Q_P(b^D 𝒮_D C^{⊗D} 𝒮_D z)` for every array `z` (phase
computation of `LayerSpecAux.layerSpec_strong`, all premises discharged). -/
theorem layerRun_eq_key (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hdata : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) {P d rr K D A S : ℕ}
    (hK : 6 ≤ K) (hDd : D ≤ d) (ρ : Fin K) (z : RArr (LayerAddr A K D S) rr) :
    layerRun P A K D S rr ρ.val d cdat z = truncArr P (fun x k => bD D *
      (Complex.I ^ (Finset.univ.filter fun j => x.2.1 j ρ = true).card *
        LayerSpecAux.selOp ρ Finset.univ (fun y k' =>
          Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card * z y k') x k)) := by
  have hDE := LayerSpecPadAux.decodeEncodeAddr_holds
  have hA1 : ProcK.run 0 (layerPhase1 A K D S rr ρ.val d) (topClass A K D S) (encodeArr z) =
      encodeArr (LayerSpecAux.selOp ρ (LayerSpecAux.iv 0 (min (q0Of d) D)) (fun y k' =>
        Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card * z y k')) := by
    rw [LayerSpecPadAux.phase1_eq, LayerSpecAux.kernels_run hDE ρ _ (min_le_right _ _)]
  by_cases h : useRows D K d
  · have e : layerRun P A K D S rr ρ.val d cdat z =
        decodeArr (ProcK.run 0 (layerPhase3 A K D S rr ρ.val P) (topClass A K D S)
          (restrictArr h.2 h.1.le (PSeq.run (layerPhase2 A K D S rr ρ.val d cdat)
            (topClass (A * padR d K) K (D - q0Of d) S) (embedArr h.2 h.1.le
              (ProcK.run 0 (layerPhase1 A K D S rr ρ.val d) (topClass A K D S)
                (encodeArr z)))))) := by
      simp only [layerRun, dif_pos h]
    rw [e, LayerSpecPadAux.phase3_decode,
      LayerSpecAux.phase2_run complexNetCert_holds cCoreProcCorrect_holds runEightSpec_holds
        packedAgree_holds packedProcCorrect_holds translationConj_holds hDE ρ hK cdat hdata hDd,
      hA1, LayerSpecAux.transfer h.2 h.1.le (LayerSpecAux.padR_ge d K) ρ,
      LayerSpecAux.decodeArr_encodeArr hDE, min_eq_left h.1.le,
      LayerSpecAux.selOp_selOp ρ (LayerSpecAux.iv_disjoint 0 _ D),
      LayerSpecAux.iv_union (Nat.zero_le _) h.1.le, LayerSpecAux.iv_univ]
  · have hq : D ≤ q0Of d := by
      by_contra hlt
      exact h ⟨by omega, LayerSpecAux.padR_pos d K⟩
    have e : layerRun P A K D S rr ρ.val d cdat z =
        decodeArr (ProcK.run 0 (layerPhase3 A K D S rr ρ.val P) (topClass A K D S)
          (ProcK.run 0 (layerPhase1 A K D S rr ρ.val d) (topClass A K D S) (encodeArr z))) := by
      simp only [layerRun, dif_neg h]
    rw [e, LayerSpecPadAux.phase3_decode, hA1, LayerSpecAux.decodeArr_encodeArr hDE,
      min_eq_right hq, LayerSpecAux.iv_univ]

end LayerSpecFinalAux

/-- **Proposition A.11, value level, unconditional** (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)):
for valid complex edge data, `K ≥ 6` and `D ≤ d`, the layer procedure returns exactly `Q_P(H z)`
for every array `z` (no disk or grid condition). -/
theorem layerRun_eq_trunc_layerH (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hdata : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) {P d rr K D A S : ℕ}
    (hK : 6 ≤ K) (hDd : D ≤ d) (ρ : Fin K) (z : RArr (LayerAddr A K D S) rr) :
    layerRun P A K D S rr ρ.val d cdat z = truncArr P (layerH ρ z) := by
  rw [LayerSpecFinalAux.layerRun_eq_key cdat hdata hK hDd ρ z]
  refine LayerSpecFinalAux.functional_eq ρ (LayerSpecAux.selOp ρ Finset.univ) ?_ z
  intro w x₀ e₀ k
  rw [LayerSpecAux.selOp_univ]
  simp only [LayerSpecAux.setSelBits_setSelBits, LayerSpecAux.selBits_setSelBits]

/-- **Proposition A.11, `LayerSpec` form, unconditional**: for valid complex edge data, `K ≥ 6` and
`D ≤ d`, the layer procedure satisfies `LayerSpec` (no `…Stmt` hypotheses). -/
theorem prop71LayerSpec_unconditional
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hdata : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (P d rr K D A S : ℕ) (ρ : Fin K) (hK : 6 ≤ K) (hDd : D ≤ d) :
    LayerSpec P rr A K D S ρ (layerRun P A K D S rr ρ.val d cdat) :=
  fun z _ => layerRun_eq_trunc_layerH cdat hdata hK hDd ρ z

end SubNLogN.Math.Networks
