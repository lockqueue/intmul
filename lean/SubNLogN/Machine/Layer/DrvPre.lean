/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreChain
import SubNLogN.Machine.Layer.DrvPreShl
import SubNLogN.Machine.Layer.DrvPreMidT1
import SubNLogN.Machine.Layer.DrvPreBandsT1

/-!
# Layer driver pre-phase: the reduction (`Machine/Layer/DrvPre.lean`)

**Scope (honest summary).** Proves `drvPre_of_parts`: from the parameter kernel
(`DrvPreParamsStmt`), the individual-kernel pass (`DrvCKernelStmt`), the padding (`DrvPadStmt`), the
descriptors (`DrvDescStmt`), the phase scan (`DrvPhaseScanStmt`), the value bridges
(`DrvPh1BridgeStmt`, `DrvPadBridgeStmt`) and the step count (`DrvPreCostStmt`), with `p.OK`,
`DrvPreStmt p` holds (the exact left shift is `Arith.shl_holds`). The program, on the array, header
and descriptor stacks plus sixteen own stacks and the kernels' private stacks:
1. `mark` floors; the parameter kernel pushes `w, w_g, Δ`, the scan header, `min(q₀, D)`, `W₀`, `K`,
   the rows flag, `drvKeep`, `drvNpad`, `r` on the own stacks `0, …, 10`;
2. exact left shift by `Δ` (array → own stack `11`), then on stack `11`: the phase scan `𝒮_D`, the
   first kernel pass, `min(q₀, D) - 1` times (halve the bit weight `W` by dropping `K` bits; kernel
   pass), the padding (unconditional: `drvNpad = 0` in the no-rows case);
3. the descriptors; two record-order reversals (stack `11` → `12` → array); drop everything.
Helpers live in `SubNLogN.Machine.Layer.DrvPPAux`.
The program, its steps and the chain are in `DrvPreProg.lean`, `DrvPreSteps.lean`,
`DrvPreChain.lean`.
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open DrvPPAux
open SubNLogN.Math.Networks (padR q0Of)

/-- **Proposition A.11 driver pre-phase, from its parts.** With `p.OK`: the parameter kernel, the
individual-kernel pass, the padding, the descriptors, the phase scan, the two value bridges and the
step-count bound give `DrvPreStmt p` (the exact left shift is `Arith.shl_holds`). -/
theorem drvPre_of_parts (p : LayerParams) (hp : p.OK) (hParams : DrvPreParamsStmt)
    (hCK : DrvCKernelStmt) (hPad : DrvPadStmt) (hDesc : DrvDescStmt) (hScan : DrvPhaseScanStmt)
    (hPh1 : DrvPh1BridgeStmt) (hPadB : DrvPadBridgeStmt) (hCost : DrvPreCostStmt) :
    DrvPreStmt p := by
  obtain ⟨Jpar, Cpar, hParK⟩ := hParams
  obtain ⟨Cck, hCkK⟩ := hCK
  obtain ⟨Cpad, hPadK⟩ := hPad
  obtain ⟨Jd, Cdesc, hDscK⟩ := hDesc
  obtain ⟨Jsc, Csc, hScK⟩ := hScan
  obtain ⟨Cshl, hShlK⟩ := Arith.shl_holds
  obtain ⟨Epar, iFpar, iDpar, Rpar, Ppar, hfinPar, hnePar, hclPar, hspecPar⟩ := hParK ()
  obtain ⟨Eshl, iFshl, iDshl, Rshl, Pshl, hfinShl, hneShl, hclShl, hspecShl⟩ := hShlK ()
  obtain ⟨Esc, iFsc, iDsc, Rsc, Psc, hfinSc, hneSc, hclSc, hspecSc⟩ := hScK ()
  obtain ⟨Eck, iFck, iDck, Rck, Pck, hfinCk, hneCk, hclCk, hspecCk⟩ := hCkK ()
  obtain ⟨Epad, iFpad, iDpad, Rpad, Ppad, hfinPad, hnePad, hclPad, hspecPad⟩ := hPadK ()
  obtain ⟨Edsc, iFdsc, iDdsc, Rdsc, Pdsc, hfinDsc, hneDsc, hclDsc, hspecDsc⟩ := hDscK ()
  have hpar : ParSpecQ Jpar Cpar Ppar := hspecPar
  have hshl : ShlSpec Cshl Pshl := hspecShl
  have hsc : ScSpec Jsc Csc Psc := hspecSc
  have hck : CkSpec Cck Pck := hspecCk
  have hpad : PadSpec Cpad Ppad := hspecPad
  have hdsc : DscSpec Jd Cdesc Pdsc := hspecDsc
  obtain ⟨P₁, C, hC⟩ := hCost p hp Cpar Jpar Cshl Csc Jsc Cck Cpad Cdesc Jd
  obtain ⟨P₂, hP₂⟩ := DrvBandsT1.q0Of_succ_le_P p hp
  obtain ⟨a0⟩ := hnePar
  obtain ⟨b0⟩ := hneShl
  obtain ⟨c0⟩ := hneSc
  obtain ⟨d0⟩ := hneCk
  obtain ⟨e0⟩ := hnePad
  obtain ⟨f0⟩ := hneDsc
  refine ⟨max (max P₁ P₂) 1, C, fun _ => ⟨QE Epar Eshl Esc Eck Epad Edsc, inferInstance,
    inferInstance, QReg Rpar Rshl Rsc Rck Rpad Rdsc, preProg Ppar Pshl Psc Pck Ppad Pdsc,
    inferInstance, ⟨(none, a0, b0, c0, d0, e0, f0)⟩,
    closed_preProg hclPar hclShl hclSc hclCk hclPad hclDsc, ?_⟩⟩
  intro t hA hS z rest hrest S hband hw hz hrestT h0 h1
  have hb1 : LayerBands p P₁ t :=
    ⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hband.1, hband.2⟩
  have hb2 : LayerBands p P₂ t :=
    ⟨le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hband.1, hband.2⟩
  have hP1 : 1 ≤ t.P := le_trans (le_max_right _ _) hband.1
  have hq0 := hP₂ t hb2
  have hρ : t.ρ < t.K := hband.2.2.2.2.2.2.2.2.2.2.1
  have hD1 : 1 ≤ t.D := hband.2.2.2.2.2.2.1
  have hK1 : 1 ≤ t.K := by clear * - hρ; omega
  have hS1 : 1 ≤ t.S := hS
  have hw1 : 1 ≤ t.w := by clear * - hw; omega
  have hq1 : 1 ≤ drvQ1 t := DrvBandsT1.one_le_drvQ1 p hp _ t hband hP1
  have hq1le : drvQ1 t ≤ q0Of t.d := min_le_left _ _
  have hq1D : drvQ1 t ≤ t.D := min_le_right _ _
  have hqΔ : drvQ1 t ≤ drvDelta t := le_trans hq1le (Nat.le_of_succ_le hq0)
  clear hq0 hq1le hP₂
  have hkeep : 1 ≤ drvKeep t := by
    unfold drvKeep
    exact Nat.mul_pos (Nat.two_pow_pos _) hS
  have hkM : drvKeep t * t.A = t.M := by
    unfold drvKeep LayerRT.M
    ring
  -- the data
  have hlen0 : (encLayer hA hS t.P z).length = t.M := by
    unfold encLayer
    rw [encArr_length', layerAddrs_length']
    unfold LayerRT.M
    ring
  have hsh0 : ∀ cs ∈ encLayer hA hS t.P z, cs.length = t.r := encArr_shape _ _ _
  have habs0 := DrvPreShlAux.CAbs_shl _ (drvDelta t) _ (DrvPreShlAux.CAbs_encLayer t hA hS z hz)
  have hlenS : (mapC (shlC (drvDelta t)) (encLayer hA hS t.P z)).length = t.M := by
    unfold mapC
    rw [List.length_map, hlen0]
  have hshS : ∀ cs ∈ mapC (shlC (drvDelta t)) (encLayer hA hS t.P z), cs.length = t.r := by
    intro cs hcs
    unfold mapC at hcs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcs
    rw [List.length_map]
    exact hsh0 c hc
  have hlenL0 : ((mapC (shlC (drvDelta t)) (encLayer hA hS t.P z)).mapIdx
      (phaseRec t.S t.K t.ρ t.D 0 0)).length = t.M := by
    rw [List.length_mapIdx, hlenS]
  have hshL0 := DrvPreShlAux.shape_phase _ t.r hshS t.S t.K t.ρ t.D 0 0
  have habsL0 := DrvPreShlAux.CAbs_phase0 _ _ habs0 t.S t.K t.ρ t.D 0
  have hlenL : ∀ k, k ≤ drvQ1 t → (qLs t ((mapC (shlC (drvDelta t)) (encLayer hA hS t.P z)).mapIdx
      (phaseRec t.S t.K t.ρ t.D 0 0)) k).length = t.M :=
    fun k hk => DrvPreShlAux.length_preLs t _ k (le_trans hk hq1D) hρ hlenL0
  have hshL : ∀ k, k ≤ drvQ1 t → ∀ cs ∈ qLs t ((mapC (shlC (drvDelta t))
      (encLayer hA hS t.P z)).mapIdx (phaseRec t.S t.K t.ρ t.D 0 0)) k, cs.length = t.r :=
    fun k hk => DrvPreShlAux.shape_preLs t _ k t.r (le_trans hk hq1D) hρ hlenL0 hshL0
  have hchain := pre_chain (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) hclPar hclShl hclSc hclCk hclPad hclDsc hpar hshl hsc hck hpad hdsc t
    (encLayer hA hS t.P z) _ rfl rest hrest S hρ hD1 hS1 hw1 hq1 hkeep hrestT
    (cArrFits_encLayer' hA hS hz hw)
    (cArrFits_of_CAbs habs0 (by clear * -; unfold drvWg; omega))
    (fun k hk => cArrFits_of_CAbs (DrvPreShlAux.CAbs_preLs _ t _ k habsL0)
      (by have hkΔ : k ≤ drvDelta t := le_trans hk hqΔ; clear * - hkΔ; unfold drvWg; omega))
    (fun k hk => DrvPPAux.chunksOf_flatten _ _ _ (by
      rw [hlenL k (Nat.le_of_lt hk), ← DrvPreShlAux.drvWj_NB t k (Nat.lt_of_lt_of_le hk hq1D) hρ]))
    (fun k hk => DrvPreShlAux.cgateOK_chunks t _ k t.r (Nat.lt_of_lt_of_le hk hq1D) hρ
      (hlenL k (Nat.le_of_lt hk)) (hshL k (Nat.le_of_lt hk)))
    (fun k hk => DrvPreShlAux.drvWj_succ t k (Nat.lt_of_lt_of_le hk hq1D))
    (fun k => DrvPreShlAux.one_le_drvWj t k hS1) (DrvPreShlAux.drvWj_zero t)
    (fun k => by
      unfold drvWj drvW0
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _)))
    (DrvPPAux.chunksOf_length_mem _ _ _ (by rw [hlenL _ le_rfl, hkM]))
    (DrvPPAux.chunksOf_flatten _ _ _ (by rw [hlenL _ le_rfl, hkM]))
    hlen0 hsh0 hlenL hshL
    (by rw [qOut_eq]; exact DrvPreMidT1.pad_shape t _ (hshL _ le_rfl)) h0 h1
  have hmid : carrSyms (drvWg t) (qOut t ((mapC (shlC (drvDelta t))
      (encLayer hA hS t.P z)).mapIdx (phaseRec t.S t.K t.ρ t.D 0 0))) = drvMidSyms t hA hS z :=
    by rw [qOut_eq_ph1]; exact DrvPreMidT1.mid_eq t hA hS z hρ hD1 hqΔ hz hPh1 hPadB
  have hNout : (qOut t ((mapC (shlC (drvDelta t)) (encLayer hA hS t.P z)).mapIdx
      (phaseRec t.S t.K t.ρ t.D 0 0))).length ≤ 2 * t.M := by
    rw [qOut_eq]; exact DrvPreMidT1.pad_len t hK1 _ (hlenL _ le_rfl)
  rw [hmid] at hchain
  exact Calculus.RunsIn.iff_runs.1 (Calculus.RunsIn.mono hchain (fun _ _ => trivial)
    (hC t _ hb1 hNout))

end SubNLogN.Machine.Layer
