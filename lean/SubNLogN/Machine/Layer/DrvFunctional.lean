import SubNLogN.Machine.Layer.DriverSpec
import SubNLogN.Math.Networks.Proofs.LayerSpecProof
import SubNLogN.Math.Networks.Proofs.AppCLayerAlg

/-!
# Layer driver: the functional identity of the driver chain (`DrvFunctionalStmt`)

`drvFunctional_holds (p) : DrvFunctionalStmt p` (`Machine/Layer/DriverSpec.lean`): on every
disk-grid input, the driver chain of the value-level semantics returns exactly `Q_P(Hz)`:
rows case `drvStageOut (pieces (drvStageIn z)) = Q_P(Hz)`, no-rows case
`drvSmallOut (drvA1 z) = Q_P(Hz)`. The cutoff is `P₀ = 0`: the bands are not used (in particular
no `K ≥ 6`; the pieces are the ideal values `cCoreVal`, not the C-core procedure).

Proof (value-level lemmas in `Math/Networks/Proofs/LayerSpecProof.lean`, namespace
`SubNLogN.Math.Networks.LayerSpecAux`): with `selOp ρ T` = `C` on the selected bits in `T`,
phase 1 is `selOp` of the first `min q₀ D` chunks after `𝒮_D` (`LayerSpecAux.kernels_run`); the
ideal pieces of `piecesOf (D − q₀)` tile the remaining chunks (`DrvFunctionalAux.pieces_val`), so
the stage is `C^{⊗(D−q₀)}` on the reshaped layout, which is `selOp` of the chunks `q₀, …, D−1` of
the original array (`LayerSpecAux.transfer`); phase 3 is `𝒮_D`, `b^D`, `Q_P`
(`LayerSpecPadAux.phase3_decode`). Hence the output is `Q_P(b^D 𝒮_D C^{⊗D} 𝒮_D z)`, which is
`Q_P(Hz)` by `prop71Functional_holds` (`prop71` is the earlier-draft prefix for Proposition A.11). Helpers live in
`SubNLogN.Machine.Layer.DrvFunctionalAux`.
-/

namespace SubNLogN.Machine.Layer

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Machine

namespace DrvFunctionalAux

/-- `a` consecutive ideal pieces of width `m^j`. -/
theorem range_pieces_val {A' K D' S rr : ℕ} (ρ : Fin K)
    (step : ℕ × ℕ → RArr (LayerAddr A' K D' S) rr → RArr (LayerAddr A' K D' S) rr)
    (hstep : ∀ (k j0 : ℕ) (y : RArr (LayerAddr A' K D' S) rr), j0 + mH ^ k ≤ D' →
      step (k, j0) y = LayerSpecAux.selOp ρ (LayerSpecAux.iv j0 (j0 + mH ^ k)) y) (j o : ℕ) :
    ∀ (a : ℕ) (y : RArr (LayerAddr A' K D' S) rr), o + a * mH ^ j ≤ D' →
      ((List.range a).map (fun t => (j, o + t * mH ^ j))).foldl (fun y pc => step pc y) y =
        LayerSpecAux.selOp ρ (LayerSpecAux.iv o (o + a * mH ^ j)) y
  | 0, y, _ => by
    simp only [List.range_zero, List.map_nil, List.foldl_nil, zero_mul, add_zero,
      LayerSpecAux.iv_self, LayerSpecAux.selOp_empty]
  | a + 1, y, h => by
    have h' : o + a * mH ^ j + mH ^ j ≤ D' := by
      rw [show o + (a + 1) * mH ^ j = o + a * mH ^ j + mH ^ j by ring] at h; exact h
    rw [List.range_succ, List.map_append, List.foldl_append,
      range_pieces_val ρ step hstep j o a y (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [hstep j (o + a * mH ^ j) _ h',
      LayerSpecAux.selOp_selOp ρ (LayerSpecAux.iv_disjoint _ _ _),
      LayerSpecAux.iv_union (by omega) (by omega),
      show o + (a + 1) * mH ^ j = o + a * mH ^ j + mH ^ j by ring]

/-- The ideal base-`m` pieces `piecesAux ds j o`. -/
theorem pieces_val {A' K D' S rr : ℕ} (ρ : Fin K)
    (step : ℕ × ℕ → RArr (LayerAddr A' K D' S) rr → RArr (LayerAddr A' K D' S) rr)
    (hstep : ∀ (k j0 : ℕ) (y : RArr (LayerAddr A' K D' S) rr), j0 + mH ^ k ≤ D' →
      step (k, j0) y = LayerSpecAux.selOp ρ (LayerSpecAux.iv j0 (j0 + mH ^ k)) y) :
    ∀ (ds : List ℕ) (j o : ℕ) (y : RArr (LayerAddr A' K D' S) rr),
      o + mH ^ j * Nat.ofDigits mH ds ≤ D' →
      (piecesAux ds j o).foldl (fun y pc => step pc y) y =
        LayerSpecAux.selOp ρ (LayerSpecAux.iv o (o + mH ^ j * Nat.ofDigits mH ds)) y
  | [], j, o, y, _ => by
    simp only [piecesAux, List.foldl_nil, Nat.ofDigits_nil, mul_zero, add_zero,
      LayerSpecAux.iv_self, LayerSpecAux.selOp_empty]
  | a :: ds, j, o, y, h => by
    have hsplit : mH ^ j * Nat.ofDigits mH (a :: ds) =
        a * mH ^ j + mH ^ (j + 1) * Nat.ofDigits mH ds := by
      rw [Nat.ofDigits_cons, pow_succ]; ring
    rw [hsplit] at h ⊢
    simp only [piecesAux, List.foldl_append]
    rw [range_pieces_val ρ step hstep j o a y (by omega),
      pieces_val ρ step hstep ds (j + 1) (o + a * mH ^ j) _ (by omega),
      LayerSpecAux.selOp_selOp ρ (LayerSpecAux.iv_disjoint _ _ _),
      LayerSpecAux.iv_union (by omega) (by omega), Nat.add_assoc]

end DrvFunctionalAux

/-- **`DrvFunctionalStmt`** (`Machine/Layer/DriverSpec.lean:214`), unconditionally (cutoff
`P₀ = 0`; the bands are not used): the driver chain of the value-level semantics returns `Q_P(Hz)`. -/
theorem drvFunctional_holds (p : LayerParams) : DrvFunctionalStmt p := by
  refine ⟨0, fun t hρ z _ hz => ?_⟩
  have hDE := LayerSpecPadAux.decodeEncodeAddr_holds
  have hC : ∀ (w : RArr (LayerAddr t.A t.K t.D t.S) t.r) (x₀ : LayerAddr t.A t.K t.D t.S)
      (e₀ : Fin t.D → Bool) (k : Fin t.r),
      LayerSpecAux.selOp ⟨t.ρ, hρ⟩ Finset.univ w (setSelBits ⟨t.ρ, hρ⟩ x₀ e₀) k =
        CD t.D (fun e => w (setSelBits ⟨t.ρ, hρ⟩ x₀ e) k) e₀ := by
    intro w x₀ e₀ k
    rw [LayerSpecAux.selOp_univ]
    simp only [LayerSpecAux.setSelBits_setSelBits, LayerSpecAux.selBits_setSelBits]
  have hF := prop71Functional_holds t.P t.r t.A t.K t.D t.S ⟨t.ρ, hρ⟩
    (LayerSpecAux.selOp ⟨t.ρ, hρ⟩ Finset.univ) hC z hz
  have hA1 : ProcK.run 0 (layerPhase1 t.A t.K t.D t.S t.r t.ρ t.d) (topClass t.A t.K t.D t.S)
      (encodeArr z) = encodeArr (LayerSpecAux.selOp ⟨t.ρ, hρ⟩
        (LayerSpecAux.iv 0 (min (q0Of t.d) t.D)) (fun y k' =>
        Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ⟨t.ρ, hρ⟩ = true).card * z y k')) :=
    (LayerSpecPadAux.phase1_eq t.d ⟨t.ρ, hρ⟩ z).trans
      (LayerSpecAux.kernels_run hDE ⟨t.ρ, hρ⟩ _ (min_le_right _ _) _)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hm : tripleM 100 = mH := by norm_num [tripleM]
    have hstep : ∀ (k j0 : ℕ) (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r),
        j0 + mH ^ k ≤ drvD' t →
        pieceStep t hρ (k, j0) y =
          LayerSpecAux.selOp ⟨t.ρ, hρ⟩ (LayerSpecAux.iv j0 (j0 + mH ^ k)) y := by
      intro k j0 y hk
      unfold pieceStep
      rw [dif_pos (by rw [hm]; exact hk), LayerSpecAux.cCoreVal_eq_selOp, hm]
    have hpieces : drvPieces t = piecesOf (drvD' t) := by
      unfold drvPieces; rw [if_pos h]
    have hYs : ∀ y₀, drvYs t hρ y₀ (drvPieces t).length =
        LayerSpecAux.selOp ⟨t.ρ, hρ⟩ Finset.univ y₀ := by
      intro y₀
      unfold drvYs
      rw [List.take_length, hpieces]
      have h1 := DrvFunctionalAux.pieces_val ⟨t.ρ, hρ⟩ (fun pc y => pieceStep t hρ pc y) hstep
        (Nat.digits mH (drvD' t)) 0 0 y₀ (by simp [Nat.ofDigits_digits])
      simp only [pow_zero, one_mul, zero_add, Nat.ofDigits_digits, LayerSpecAux.iv_univ] at h1
      exact h1
    rw [hYs]
    unfold drvStageOut drvStageIn
    rw [LayerSpecPadAux.phase3_decode t.P ⟨t.ρ, hρ⟩, hA1,
      LayerSpecAux.transfer h.2 h.1.le (LayerSpecAux.padR_ge t.d t.K) ⟨t.ρ, hρ⟩,
      LayerSpecAux.decodeArr_encodeArr hDE, min_eq_left h.1.le,
      LayerSpecAux.selOp_selOp _ (LayerSpecAux.iv_disjoint 0 _ t.D),
      LayerSpecAux.iv_union (Nat.zero_le _) h.1.le, LayerSpecAux.iv_univ]
    exact hF
  · have hq : t.D ≤ q0Of t.d := by
      by_contra hlt
      exact h ⟨by omega, LayerSpecAux.padR_pos t.d t.K⟩
    unfold drvSmallOut drvA1
    rw [LayerSpecPadAux.encodeArr_decodeArr, LayerSpecPadAux.phase3_decode t.P ⟨t.ρ, hρ⟩, hA1,
      LayerSpecAux.decodeArr_encodeArr hDE, min_eq_right hq, LayerSpecAux.iv_univ]
    exact hF

end SubNLogN.Machine.Layer
