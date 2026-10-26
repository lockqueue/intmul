import WP.W9a.PipeSteps

/-!
# WP.W9a.PipePost — the POST step triple of the pipeline

`post_step`: the embedded POST program maps `PB (ℓ+1)` to `PB ℓ` at cost `C · postB … ℓ`. Its
inputs are the child outputs `levelEvalV child pSub (preLevel …)` (sizes from `chain_sizes` and
`computablePaperFastDFT_size`, widths from `chain_out_width`) and the RET segment pushed by PRE(ℓ).
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

/-- **POST step**: `PB (ℓ+1) → PB ℓ`. -/
theorem post_step {Mul : ℕ → ℕ} {mo mL : ℕ} (hmo : mo ≤ mL) {Ro RR : Type} (lens : Lens RR Ro)
    {Co : ℕ} {Po : Prog (BLoc mo) (fun _ => Sym) Ro} (hPo : PostLevelSpec Mul mo Ro Co Po)
    {C : ℕ} (hC : Co ≤ C) {wd : ℕ → ℕ} {cSpec : ComputablePaperFastDFTSpec} {p_in : ℕ}
    {xs : List (Array (ℤ × ℤ))} {σ : BLoc mL → List Sym} {restS restT : List Sym}
    (hChain : ChainOK wd cSpec p_in 0 xs) (hW0 : σ (.inl .W0) = []) {ℓ : ℕ}
    (hℓ : ℓ < depthOf cSpec) (τ : BLoc mL → List Sym)
    (hB : PB σ cSpec p_in xs restS restT (ℓ + 1) τ) :
    Triple [] (fun s => s.stk = τ) ((Po.mapStk (embL hmo)).liftRegs lens)
      (fun s => PB σ cSpec p_in xs restS restT ℓ s.stk) (C * postB Mul wd cSpec p_in 0 xs ℓ) := by
  obtain ⟨q, pSub, m1, t1, r, ft, preTw, postTw, c0T, c1T, child, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    nav_step ℓ cSpec p_in xs hℓ
  have hC0 := chain_at wd ℓ cSpec p_in 0 xs hℓ.le hChain
  rw [h1] at hC0
  obtain ⟨hDims, -, hTabP, hOK, hPN, hChild⟩ := hC0
  have hlen : (levelEvalV child pSub ((xsAt cSpec p_in xs ℓ).flatMap fun x =>
      (preNodeV (pinAt cSpec p_in ℓ) pSub m1 t1 r ft preTw postTw x).toList)).length =
      t1 * ((xsAt cSpec p_in xs ℓ).map (altNodeV (pinAt cSpec p_in ℓ) pSub t1 r)).length := by
    rw [levelEvalV_eq_map, List.length_map, List.length_map, length_flatMap_preNodeV,
      Nat.mul_comm]
  have hys : ∀ y ∈ levelEvalV child pSub ((xsAt cSpec p_in xs ℓ).flatMap fun x =>
      (preNodeV (pinAt cSpec p_in ℓ) pSub m1 t1 r ft preTw postTw x).toList), y.size = r := by
    intro y hy
    rw [levelEvalV_eq_map] at hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    rw [computablePaperFastDFT_size, ← chain_sizes wd child pSub (0 + ℓ + 1) _ hChild z hz]
    obtain ⟨x, -, hzx⟩ := List.mem_flatMap.1 hz
    exact preNodeV_rows _ _ _ _ _ _ _ _ x z hzx
  have hEW : ∀ a ∈ (xsAt cSpec p_in xs ℓ).map (altNodeV (pinAt cSpec p_in ℓ) pSub t1 r),
      EntryW (wd (0 + ℓ)) a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    exact (hOK x hx).2.2.2.2.2.2.2.1
  have hPN' : ∀ i < ((xsAt cSpec p_in xs ℓ).map (altNodeV (pinAt cSpec p_in ℓ) pSub t1 r)).length,
      PostNodeOK (wd (0 + ℓ)) ⟨q, pSub, t1, r, child.p⟩ c0T c1T
        (((xsAt cSpec p_in xs ℓ).map (altNodeV (pinAt cSpec p_in ℓ) pSub t1 r)).getD i (0, 0))
        (groupAt t1 (levelEvalV child pSub ((xsAt cSpec p_in xs ℓ).flatMap fun x =>
          (preNodeV (pinAt cSpec p_in ℓ) pSub m1 t1 r ft preTw postTw x).toList)) i).toArray := by
    intro i hi
    rw [List.length_map] at hi
    rw [getD_map_of_lt _ #[] (0, 0) _ i hi]
    exact hPN i hi
  have hrun := hPo ⟨q, pSub, t1, r, child.p⟩ (wd (0 + ℓ)) (wd (0 + ℓ + 1)) c0T c1T
    ((xsAt cSpec p_in xs ℓ).map (altNodeV (pinAt cSpec p_in ℓ) pSub t1 r))
    (levelEvalV child pSub ((xsAt cSpec p_in xs ℓ).flatMap fun x =>
      (preNodeV (pinAt cSpec p_in ℓ) pSub m1 t1 r ft preTw postTw x).toList))
    (τ ∘ embL hmo) restS (postTailAt cSpec ℓ ++ restT) (retAt cSpec p_in xs ℓ ++ σ (.inl .RET))
    (pinStk cSpec ℓ ++ σ (.inl .C1)) hDims hTabP hlen hys
    (chain_out_width wd child pSub (0 + ℓ + 1) _ hChild) hEW hPN'
    (hB.1.trans (by rw [h2, h3, h4])) (frame_W0 (τ := τ) hB hW0)
    (hB.2.1.trans (by rw [h7, List.append_assoc]))
    (hB.2.2.2.1.trans (by rw [h5, List.append_assoc]))
    (hB.2.2.2.2.1.trans (by rw [h6, List.append_assoc]))
  rw [← Function.update_comp_eq_of_injective τ (embL_injective hmo),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmo),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmo),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmo),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmo)] at hrun
  refine step_triple hmo lens τ
    (Function.update (Function.update (Function.update (Function.update (Function.update τ
      (.inl .S) (streamSyms (postLevel (postNodeV q pSub t1 r c0T c1T child.p) t1
        ((xsAt cSpec p_in xs ℓ).map (altNodeV (pinAt cSpec p_in ℓ) pSub t1 r))
        (levelEvalV child pSub ((xsAt cSpec p_in xs ℓ).flatMap fun x =>
          (preNodeV (pinAt cSpec p_in ℓ) pSub m1 t1 r ft preTw postTw x).toList))) ++ restS))
      (.inl .TR) (postTailAt cSpec ℓ ++ restT))
      (.inl .TL) ((postSeg q pSub t1 r c0T c1T child.p).reverse ++ τ (.inl .TL)))
      (.inl .RET) (retAt cSpec p_in xs ℓ ++ σ (.inl .RET)))
      (.inl .C1) (pinStk cSpec ℓ ++ σ (.inl .C1)))
    hrun (fun j _ => by simp) ?_ ?_
  · refine frame_step5 hB (postSeg q pSub t1 r c0T c1T child.p) ?_ ?_ rfl rfl rfl
    · rw [h7, List.append_assoc]
    · simp only [h1, levelEvalV]
  · rw [postB_at h1, List.length_map]
    exact Nat.mul_le_mul_right _ hC

#assert_std_axioms post_step

end WP.W9a
