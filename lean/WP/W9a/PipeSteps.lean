import WP.W9a.PipeFrame
import WP.W9a.PipeCost

/-!
# WP.W9a.PipeSteps — the PRE and LEAF step triples of the pipeline

`PreLevelSpec`, `LeafLevelSpec`, `PostLevelSpec` are verbatim copies of the bodies of
`W9_preLevelProg`, `W9_leafLevelProg`, `W9_postLevelProg` at fixed `m R C P`.
* `pre_step`: the embedded PRE program maps `PA ℓ` to `PA (ℓ+1)` at cost `C · preB … ℓ`;
* `leaf_step`: the embedded LEAF program maps `PA depth` to `PB depth` at cost `C · leafB …`.

The level's fields come from `nav_step` / `nav_base`, and its hypotheses from `ChainOK` via
`chain_at`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

/-- The body of `W9_preLevelProg Mul` at fixed `m R C P`. -/
def PreLevelSpec (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) :
    Prop :=
  ∀ (h : PreHdr) (w w' : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (xs : List (Array (ℤ × ℤ))) (σ : BLoc m → List Sym) (restS restT r1 : List Sym),
    PreDims h → PreTablesW w h.m1 h.t1 h.r ft preTw postTw →
    (∀ x ∈ xs, x.size = h.N ∧ PreNodeOK w h ft preTw postTw x) →
    StreamW w' (xs.flatMap fun x => (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList) →
    σ (.inl .S) = streamSyms xs ++ restS → σ (.inl .W0) = [] →
    σ (.inl .TR) = preSeg h.pSub h.m1 h.t1 h.r ft preTw postTw ++ restT →
    σ (.inl .C1) = hdrSyms [h.p_in] ++ r1 →
    Runs P σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ
        (.inl .S) (streamSyms (xs.flatMap fun x =>
          (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList) ++ restS))
        (.inl .TR) restT)
        (.inl .TL) ((preSeg h.pSub h.m1 h.t1 h.r ft preTw postTw).reverse ++ σ (.inl .TL)))
        (.inl .RET) (retSeg (xs.map (altNodeV h.p_in h.pSub h.t1 h.r)) ++ σ (.inl .RET)))
        (.inl .C1) (hdrSyms [h.pSub] ++ σ (.inl .C1)))
      (fun _ => True)
      (C * (preLevelBound Mul w w' h xs.length + (preSeg h.pSub h.m1 h.t1 h.r ft preTw postTw).length))

/-- The body of `W9_leafLevelProg Mul` at fixed `m R C P`. -/
def LeafLevelSpec (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) :
    Prop :=
  ∀ (p_in p K w : ℕ) (tw : Array (Array (ℤ × ℤ))) (xs : List (Array (ℤ × ℤ)))
    (σ : BLoc m → List Sym) (restS restT r1 : List Sym),
    LeafTwW w K tw → (∀ x ∈ xs, x.size = 2 ^ K ∧ LeafOK w p_in p K tw x) →
    σ (.inl .S) = streamSyms xs ++ restS → σ (.inl .W0) = [] →
    σ (.inl .TR) = leafSeg p K tw ++ restT → σ (.inl .C1) = hdrSyms [p_in] ++ r1 →
    Runs P σ
      (Function.update (Function.update (Function.update σ
        (.inl .S) (streamSyms (xs.map fun x =>
          (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1) ++ restS))
        (.inl .TR) restT)
        (.inl .TL) ((leafSeg p K tw).reverse ++ σ (.inl .TL)))
      (fun _ => True)
      (C * (leafLevelBound Mul w p_in p K xs.length + (leafSeg p K tw).length))

/-- The body of `W9_postLevelProg Mul` at fixed `m R C P`. -/
def PostLevelSpec (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) :
    Prop :=
  ∀ (h : PostHdr) (w w' : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alts : List (ℤ × ℤ))
    (ys : List (Array (ℤ × ℤ))) (σ : BLoc m → List Sym) (restS restT ret r1 : List Sym),
    PostDims h → PostTablesW h.H h.r c0T c1T → ys.length = h.t1 * alts.length →
    (∀ y ∈ ys, y.size = h.r) → StreamW w' ys → (∀ a ∈ alts, EntryW w a) →
    (∀ i < alts.length,
      PostNodeOK w h c0T c1T (alts.getD i (0, 0)) (groupAt h.t1 ys i).toArray) →
    σ (.inl .S) = streamSyms ys ++ restS → σ (.inl .W0) = [] →
    σ (.inl .TR) = postSeg h.p h.pSub h.t1 h.r c0T c1T h.pChild ++ restT →
    σ (.inl .RET) = retSeg alts ++ ret → σ (.inl .C1) = hdrSyms [h.pSub] ++ r1 →
    Runs P σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ
        (.inl .S) (streamSyms (postLevel (postNodeV h.p h.pSub h.t1 h.r c0T c1T h.pChild) h.t1
          alts ys) ++ restS))
        (.inl .TR) restT)
        (.inl .TL) ((postSeg h.p h.pSub h.t1 h.r c0T c1T h.pChild).reverse ++ σ (.inl .TL)))
        (.inl .RET) ret)
        (.inl .C1) r1)
      (fun _ => True)
      (C * (postLevelBound Mul w w' h alts.length +
        (postSeg h.p h.pSub h.t1 h.r c0T c1T h.pChild).length))

/-- **PRE step**: `PA ℓ → PA (ℓ+1)`. -/
theorem pre_step {Mul : ℕ → ℕ} {mp mL : ℕ} (hmp : mp ≤ mL) {Rp RR : Type} (lens : Lens RR Rp)
    {Cp : ℕ} {Pp : Prog (BLoc mp) (fun _ => Sym) Rp} (hPp : PreLevelSpec Mul mp Rp Cp Pp)
    {C : ℕ} (hC : Cp ≤ C) {wd : ℕ → ℕ} {cSpec : ComputablePaperFastDFTSpec} {p_in : ℕ}
    {xs : List (Array (ℤ × ℤ))} {σ : BLoc mL → List Sym} {restS restT r1 : List Sym}
    (hChain : ChainOK wd cSpec p_in 0 xs) (hW0 : σ (.inl .W0) = [])
    (hC1 : σ (.inl .C1) = hdrSyms [p_in] ++ r1) {ℓ : ℕ} (hℓ : ℓ < depthOf cSpec)
    (τ : BLoc mL → List Sym) (hA : PA σ cSpec p_in xs restS restT ℓ τ) :
    Triple [] (fun s => s.stk = τ) ((Pp.mapStk (embL hmp)).liftRegs lens)
      (fun s => PA σ cSpec p_in xs restS restT (ℓ + 1) s.stk)
      (C * preB Mul wd cSpec p_in 0 xs ℓ) := by
  obtain ⟨q, pSub, m1, t1, r, ft, preTw, postTw, c0T, c1T, child, h1, h2, -, h4, h5, h6, -, -⟩ :=
    nav_step ℓ cSpec p_in xs hℓ
  have hC0 := chain_at wd ℓ cSpec p_in 0 xs hℓ.le hChain
  rw [h1] at hC0
  obtain ⟨hDims, hTab, -, hOK, -, hChild⟩ := hC0
  obtain ⟨r1', hr1'⟩ := pinStk_head p_in r1 ℓ cSpec hℓ.le
  have hrun := hPp ⟨pinAt cSpec p_in ℓ, pSub, m1, t1, r⟩ (wd (0 + ℓ)) (wd (0 + ℓ + 1)) ft preTw
    postTw (xsAt cSpec p_in xs ℓ) (τ ∘ embL hmp) restS (preSegs child ++ tailT cSpec restT) r1'
    hDims hTab hOK (chain_in_width wd child pSub (0 + ℓ + 1) _ hChild) hA.1 (frame_W0 (τ := τ) hA hW0)
    (hA.2.1.trans (by rw [h1]; simp only [preSegs, List.append_assoc]))
    (hA.2.2.2.2.1.trans (by rw [hC1]; exact hr1'))
  rw [← Function.update_comp_eq_of_injective τ (embL_injective hmp),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmp),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmp),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmp),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmp)] at hrun
  refine step_triple hmp lens τ
    (Function.update (Function.update (Function.update (Function.update (Function.update τ
      (.inl .S) (streamSyms ((xsAt cSpec p_in xs ℓ).flatMap fun x =>
        (preNodeV (pinAt cSpec p_in ℓ) pSub m1 t1 r ft preTw postTw x).toList) ++ restS))
      (.inl .TR) (preSegs child ++ tailT cSpec restT))
      (.inl .TL) ((preSeg pSub m1 t1 r ft preTw postTw).reverse ++ τ (.inl .TL)))
      (.inl .RET) (retSeg ((xsAt cSpec p_in xs ℓ).map (altNodeV (pinAt cSpec p_in ℓ) pSub t1 r)) ++
        τ (.inl .RET)))
      (.inl .C1) (hdrSyms [pSub] ++ τ (.inl .C1)))
    hrun (fun j _ => by simp) ?_ ?_
  · refine frame_step5 hA (preSeg pSub m1 t1 r ft preTw postTw) ?_ ?_ ?_ ?_ ?_
    · rw [h1, h2]
      simp only [preSegs, List.append_assoc]
    · rw [h4]
    · rw [h2]
    · rw [hA.2.2.2.1, h5, List.append_assoc]
    · rw [hA.2.2.2.2.1, h6, List.append_assoc]
  · rw [preB_at h1]
    exact Nat.mul_le_mul_right _ hC

/-- **LEAF step**: `PA depth → PB depth`. -/
theorem leaf_step {Mul : ℕ → ℕ} {ml mL : ℕ} (hml : ml ≤ mL) {Rl RR : Type} (lens : Lens RR Rl)
    {Cl : ℕ} {Pl : Prog (BLoc ml) (fun _ => Sym) Rl} (hPl : LeafLevelSpec Mul ml Rl Cl Pl)
    {C : ℕ} (hC : Cl ≤ C) {wd : ℕ → ℕ} {cSpec : ComputablePaperFastDFTSpec} {p_in : ℕ}
    {xs : List (Array (ℤ × ℤ))} {σ : BLoc mL → List Sym} {restS restT r1 : List Sym}
    (hChain : ChainOK wd cSpec p_in 0 xs) (hW0 : σ (.inl .W0) = [])
    (hC1 : σ (.inl .C1) = hdrSyms [p_in] ++ r1)
    (τ : BLoc mL → List Sym) (hA : PA σ cSpec p_in xs restS restT (depthOf cSpec) τ) :
    Triple [] (fun s => s.stk = τ) ((Pl.mapStk (embL hml)).liftRegs lens)
      (fun s => PB σ cSpec p_in xs restS restT (depthOf cSpec) s.stk)
      (C * leafB Mul wd cSpec p_in 0 xs) := by
  obtain ⟨q, K, tw, h1, h2, h3, h4⟩ := nav_base cSpec
  have hC0 := chain_at wd (depthOf cSpec) cSpec p_in 0 xs le_rfl hChain
  rw [h1] at hC0
  obtain ⟨hTw, hOK⟩ := hC0
  obtain ⟨r1', hr1'⟩ := pinStk_head p_in r1 (depthOf cSpec) cSpec le_rfl
  have hrun := hPl (pinAt cSpec p_in (depthOf cSpec)) q K (wd (0 + depthOf cSpec)) tw
    (xsAt cSpec p_in xs (depthOf cSpec)) (τ ∘ embL hml) restS
    (postTailAt cSpec (depthOf cSpec) ++ restT) r1' hTw hOK hA.1 (frame_W0 (τ := τ) hA hW0)
    (hA.2.1.trans (by rw [h4, tailT, h2, h3, List.nil_append, List.append_assoc]))
    (hA.2.2.2.2.1.trans (by rw [hC1]; exact hr1'))
  rw [← Function.update_comp_eq_of_injective τ (embL_injective hml),
    ← Function.update_comp_eq_of_injective _ (embL_injective hml),
    ← Function.update_comp_eq_of_injective _ (embL_injective hml)] at hrun
  refine step_triple hml lens τ
    (Function.update (Function.update (Function.update τ
      (.inl .S) (streamSyms ((xsAt cSpec p_in xs (depthOf cSpec)).map fun x =>
        (computableBaseRadix2FFTWithProgramCost (pinAt cSpec p_in (depthOf cSpec)) q K tw x).1) ++
          restS))
      (.inl .TR) (postTailAt cSpec (depthOf cSpec) ++ restT))
      (.inl .TL) ((leafSeg q K tw).reverse ++ τ (.inl .TL)))
    hrun (fun j _ => by simp) ?_ ?_
  · refine frame_step3 hA (leafSeg q K tw) ?_ ?_ rfl
    · rw [h4, tailT, h2, h3, List.nil_append, List.append_assoc]
    · simp only [h1, levelEvalV]
  · rw [leafB_at h1]
    exact Nat.mul_le_mul_right _ hC

#assert_std_axioms pre_step leaf_step

end WP.W9a
