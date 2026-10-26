/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.FFT
import SubNLogN.Math.Walsh.Proofs.PhaseTable
import SubNLogN.Math.Walsh.Proofs.DirectFFT
import SubNLogN.Math.Walsh.Proofs.DirectFFTLocal
import SubNLogN.Math.Walsh.Proofs.LayoutPerm
import SubNLogN.Math.Walsh.Proofs.DirectFFTExact

/-!
# K4 value facts for the middle reduction (`Machine/FFT/MiddleMath.lean`)

**Scope (honest summary).** Value-level lemmas (no machine; namespace
`SubNLogN.Machine.FFT.MiddleAux`) used by
`walshMiddleMachine_of_parts` (`Machine/FFT/Middle.lean`) to discharge the hypotheses of each part
and to identify the composite output with `walshMiddle`. All proved here from the math-layer
theorems (`phase_table`, `last_axis_level_error`, `DirectFFTProof.lastAxis_error`,
`positional_perm`, `norm_hT_apply_le`, `norm_layerH_apply_le`, `walsh_layout_perm` (Lemma 6.3:
`L`, `U` are permutations) and `tensor_encoding` (`ofTensor ∘ toTensor = id`)).

* `tabOK_phaseTable`: the concrete table of Lemma 6.1 is a disk-grid table (`phase_table`).
* `ofTensor_diskGrid`, `lastAxisFFT_diskGrid`, `rounds_ideal_diskGrid`: disk-grid arrays stay
  disk-grid through the input encoding, stage (i) and stage (iii) (Theorem 6.5, Section 6.4).
* `walshMiddle_ofTensor_eq` (from the two statements as hypotheses) and
  `walshMiddle_ofTensor_eq_parts` (unconditional): the composite of the four stages is
  `walshMiddle idealLayer` (Theorem 6.5, `thm:direct-fft`, with Theorem 5.8 for `L` and `U`).
* `addrBits_le_mul`: `m₀ ≤ D·ℓ` when every `a_i ≤ ℓ`.
-/

namespace SubNLogN.Machine.FFT.MiddleAux

open SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- The concrete phase table (Lemma 6.1) is a disk-grid table, for `8 ≤ q`, `ℓ ≤ q`. -/
theorem tabOK_phaseTable {q ℓ : ℕ} (hq : 8 ≤ q) (hℓ : ℓ ≤ q) : TabOK q ℓ (phaseTable q ℓ) :=
  fun j hj => ⟨((phase_table q ℓ hq hℓ).1 j hj).1, ((phase_table q ℓ hq hℓ).1 j hj).2.1⟩

/-- The tensor encoding of a disk-grid tensor is a disk-grid record array. -/
theorem ofTensor_diskGrid {D : ℕ} {a : Fin D → ℕ} {ℓ q : ℕ} {U : Idx (fftShape a ℓ) → ℂ}
    (hU : ∀ j, OnDiskGrid q (U j)) : ArrOnDiskGrid q (ofTensor a ℓ U) :=
  fun _ _ => hU _

/-- Stage (i) keeps disk-grid arrays disk-grid (Theorem 6.5, Section 6.4; `lastAxis_error`). -/
theorem lastAxisFFT_diskGrid {q ℓ : ℕ} (hq : 8 ≤ q) (hℓq : ℓ ≤ q) (hℓ : 1 ≤ ℓ) {α : Type}
    [Fintype α] {z : RArr α (2 ^ ℓ)} (hz : ArrOnDiskGrid q z) :
    ArrOnDiskGrid q (lastAxisFFT q ℓ (phaseTable q ℓ) z) :=
  (DirectFFTProof.lastAxis_error last_axis_level_error (phase_table q ℓ hq hℓq).1 hℓ z hz).1

/-- One computed round with the ideal layer keeps disk-grid arrays disk-grid, for any disk-grid
table (Section 6.4: butterflies and `Q_q` do not increase modulus, disk phases do not increase
modulus). -/
theorem roundRun_ideal_diskGrid {q D ℓ K : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ}
    (htab : TabOK q ℓ θt) (v : ℕ) (w : RArr (Cube (addrBits a)) (2 ^ ℓ))
    (hw : ArrOnDiskGrid q w) :
    ArrOnDiskGrid q (DirectFFTProof.roundRun idealLayer q D ℓ K a θt v w) := by
  have hstep : ∀ x k, ‖(roundStep q D ℓ K a v).run idealLayer (2 ^ ℓ) w x k‖ ≤ 1 := by
    intro x k
    unfold roundStep
    split_ifs with h
    · simp only [WStep.run, sliceCall, idealLayer, truncArr]
      exact (norm_truncC_le _ _).trans
        (norm_layerH_apply_le _ _ (fun y k' => (hw _ k').2) _ _)
    · simp only [WStep.run, truncArr]
      exact (norm_truncC_le _ _).trans (norm_hT_apply_le _ _ (fun y k' => (hw y k').2) x k)
  intro x k
  have hθ : ‖θt (2 * twJ ℓ K a v x)‖ ≤ 1 :=
    (htab _ (by have := DirectFFTProof.twJ_lt ℓ K a v x; omega)).2
  show OnDiskGrid q (truncC q (θt (2 * twJ ℓ K a v x) *
    (roundStep q D ℓ K a v).run idealLayer (2 ^ ℓ) w x k))
  refine truncC_mem_diskGrid q _ ?_
  rw [norm_mul]
  calc ‖θt (2 * twJ ℓ K a v x)‖ * ‖(roundStep q D ℓ K a v).run idealLayer (2 ^ ℓ) w x k‖
      ≤ 1 * 1 := mul_le_mul hθ (hstep x k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Step (iii) with the ideal layer keeps disk-grid arrays disk-grid. -/
theorem rounds_ideal_diskGrid {q D ℓ K : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ}
    (htab : TabOK q ℓ θt) (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) (hz : ArrOnDiskGrid q z) :
    ArrOnDiskGrid q (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a θt) z) := by
  rw [DirectFFTProof.roundsProg_run]
  exact DirectFFTProof.foldl_adm (ArrOnDiskGrid q)
    (DirectFFTProof.roundRun idealLayer q D ℓ K a θt) _
    (fun v _ w hw => roundRun_ideal_diskGrid htab v w hw) z hz

/-- **The composite of the four stages is the Walsh middle** (Theorem 6.5, `thm:direct-fft`): with
`z₁ = lastAxisFFT …`, `z₃ = rounds (L z₁)`, both disk-grid, the encoded `walshMiddle idealLayer`
output is `U (rounds (L z₁))`. Uses Theorem 5.8 (`positional_perm`, for the permutations `L` and
`U`), Lemma 6.3 (`WalshLayoutPermStmt`, contract hypothesis) and the tensor encoding
(`TensorEncodingStmt`, contract hypothesis). -/
theorem walshMiddle_ofTensor_eq (hLay : WalshLayoutPermStmt) (hEnc : TensorEncodingStmt)
    {q D ℓ K : ℕ} {a : Fin D → ℕ} (hK1 : 1 ≤ K) (hK2 : K ≤ ℓ - 1) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (U : Idx (fftShape a ℓ) → ℂ)
    (hz1 : ArrOnDiskGrid q (lastAxisFFT q ℓ (phaseTable q ℓ) (ofTensor a ℓ U)))
    (hz3 : ArrOnDiskGrid q (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a (phaseTable q ℓ))
      (posPermArr (layoutL ℓ K a) (lastAxisFFT q ℓ (phaseTable q ℓ) (ofTensor a ℓ U))))) :
    ofTensor a ℓ (walshMiddle idealLayer q D ℓ K a U) =
      posPermArr (layoutU ℓ K a) (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a (phaseTable q ℓ))
        (posPermArr (layoutL ℓ K a) (lastAxisFFT q ℓ (phaseTable q ℓ) (ofTensor a ℓ U)))) := by
  obtain ⟨hLb, -, hUL, hLU⟩ := hLay ℓ K a hK1 hK2 hℓ ha
  have hUb := DirectFFTProof.layoutU_bijective hUL hLU
  have hspec : ∀ (j₀ D' nS : ℕ) (ρ : Fin K), j₀ + D' * K + nS = addrBits a → 1 ≤ D' →
      D' ≤ D + 1 → LayerSpec (q + 8 * (D + 1)) (2 ^ ℓ) (2 ^ j₀) K D' (2 ^ nS) ρ
        (idealLayer (q + 8 * (D + 1)) (2 ^ ℓ) (2 ^ j₀) K D' (2 ^ nS) ρ) :=
    fun _ _ _ _ _ _ _ => idealLayer_spec _ _ _ _ _ _ _
  have hPL : ∀ z : RArr (Cube (addrBits a)) (2 ^ ℓ), ArrOnDiskGrid q z →
      runProg idealLayer (2 ^ ℓ) (posPermProg q (D + 1) K (layoutL ℓ K a)) z =
        posPermArr (layoutL ℓ K a) z :=
    (positional_perm idealLayer q (D + 1) K hK1 (by omega) hspec (Equiv.ofBijective _ hLb)).1
  have hPU : ∀ z : RArr (Cube (addrBits a)) (2 ^ ℓ), ArrOnDiskGrid q z →
      runProg idealLayer (2 ^ ℓ) (posPermProg q (D + 1) K (layoutU ℓ K a)) z =
        posPermArr (layoutU ℓ K a) z :=
    (positional_perm idealLayer q (D + 1) K hK1 (by omega) hspec (Equiv.ofBijective _ hUb)).1
  show ofTensor a ℓ (toTensor a ℓ (directFFT idealLayer q D ℓ K a (phaseTable q ℓ)
    (ofTensor a ℓ U))) = _
  rw [(hEnc a ℓ).2]
  unfold directFFT recordAxesProg
  rw [DirectFFTProof.run_append, DirectFFTProof.run_append, hPL _ hz1, hPU _ hz3]

/-- **The composite of the four stages is the Walsh middle**, unconditionally (using
`walsh_layout_perm` and `tensor_encoding` discharge the two statements). -/
theorem walshMiddle_ofTensor_eq_parts {q D ℓ K : ℕ} {a : Fin D → ℕ} (hK1 : 1 ≤ K)
    (hK2 : K ≤ ℓ - 1) (hℓ : 2 ≤ ℓ) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (U : Idx (fftShape a ℓ) → ℂ)
    (hz1 : ArrOnDiskGrid q (lastAxisFFT q ℓ (phaseTable q ℓ) (ofTensor a ℓ U)))
    (hz3 : ArrOnDiskGrid q (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a (phaseTable q ℓ))
      (posPermArr (layoutL ℓ K a) (lastAxisFFT q ℓ (phaseTable q ℓ) (ofTensor a ℓ U))))) :
    ofTensor a ℓ (walshMiddle idealLayer q D ℓ K a U) =
      posPermArr (layoutU ℓ K a) (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a (phaseTable q ℓ))
        (posPermArr (layoutL ℓ K a) (lastAxisFFT q ℓ (phaseTable q ℓ) (ofTensor a ℓ U)))) :=
  walshMiddle_ofTensor_eq walsh_layout_perm tensor_encoding hK1 hK2 hℓ ha U hz1 hz3

/-- `m₀ = ∑ a_i ≤ D·ℓ` when every `a_i ≤ ℓ`. -/
theorem addrBits_le_mul {D ℓ : ℕ} {a : Fin D → ℕ} (ha : ∀ i, a i ≤ ℓ) : addrBits a ≤ D * ℓ := by
  unfold addrBits
  have h := List.sum_le_card_nsmul (List.ofFn a) ℓ (fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact ha i)
  simpa [List.length_ofFn, smul_eq_mul] using h

end SubNLogN.Machine.FFT.MiddleAux
