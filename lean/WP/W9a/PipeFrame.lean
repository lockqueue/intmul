import WP.W9a.Chain

/-!
# WP.W9a.PipeFrame — the level-boundary states of the pipeline

`Frame σ tapeR Sv TRv RETv C1v τ` says that `τ` has `S = Sv`, `TR = TRv`, `RET = RETv` and
`C1 = C1v`, that the consumed tape prefix lies reversed on `TL` above `symGuard :: σ TL` (prefix
`++ TRv = tapeR`), and that every other stack is as in `σ`. `PA … ℓ` (before PRE(ℓ), or LEAF when
`ℓ = depth`) and `PB … ℓ` (after POST(ℓ), or LEAF) are the pipeline's `A`/`B` predicates for
`W9_level`. `step_triple` turns a level contract's `Runs` into a `W9_level` step triple.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

/-- A level-boundary state of the pipeline. -/
def Frame {m : ℕ} (σ : BLoc m → List Sym) (tapeR Sv TRv RETv C1v : List Sym)
    (τ : BLoc m → List Sym) : Prop :=
  τ (.inl .S) = Sv ∧ τ (.inl .TR) = TRv ∧
    (∃ pre : List Sym, τ (.inl .TL) = pre.reverse ++ symGuard :: σ (.inl .TL) ∧
      pre ++ TRv = tapeR) ∧
    τ (.inl .RET) = RETv ∧ τ (.inl .C1) = C1v ∧
    ∀ k, k ≠ .inl .S → k ≠ .inl .TR → k ≠ .inl .TL → k ≠ .inl .RET → k ≠ .inl .C1 → τ k = σ k

section FrameLemmas

variable {m : ℕ} {σ τ : BLoc m → List Sym} {tapeR Sv TRv RETv C1v : List Sym}

theorem frame_W0 (hF : Frame σ tapeR Sv TRv RETv C1v τ) (hW0 : σ (.inl .W0) = []) :
    τ (.inl .W0) = [] :=
  (hF.2.2.2.2.2 _ (by simp) (by simp) (by simp) (by simp) (by simp)).trans hW0

/-- PRE/POST: a level consumes `seg` from `TR` (pushed reversed on `TL`) and sets `S`, `RET`, `C1`. -/
theorem frame_step5 (hF : Frame σ tapeR Sv TRv RETv C1v τ) (seg : List Sym)
    {Sv' TRv' RETv' C1v' a b c d : List Sym} (hTR : TRv = seg ++ TRv') (ha : a = Sv')
    (hb : b = TRv') (hc : c = RETv') (hd : d = C1v') :
    Frame σ tapeR Sv' TRv' RETv' C1v'
      (Function.update (Function.update (Function.update (Function.update (Function.update τ
        (.inl .S) a) (.inl .TR) b) (.inl .TL) (seg.reverse ++ τ (.inl .TL))) (.inl .RET) c)
        (.inl .C1) d) := by
  obtain ⟨_, _, ⟨pre, hTL, hpre⟩, _, _, ho⟩ := hF
  subst ha hb hc hd
  refine ⟨by simp, by simp, ⟨pre ++ seg, by simp [hTL], ?_⟩, by simp, by simp, ?_⟩
  · rw [List.append_assoc, ← hTR, hpre]
  · intro k h1 h2 h3 h4 h5
    rw [Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3,
      Function.update_of_ne h2, Function.update_of_ne h1]
    exact ho k h1 h2 h3 h4 h5

/-- LEAF: consumes `seg` from `TR` and sets `S`; `RET` and `C1` are unchanged. -/
theorem frame_step3 (hF : Frame σ tapeR Sv TRv RETv C1v τ) (seg : List Sym)
    {Sv' TRv' a b : List Sym} (hTR : TRv = seg ++ TRv') (ha : a = Sv') (hb : b = TRv') :
    Frame σ tapeR Sv' TRv' RETv C1v
      (Function.update (Function.update (Function.update τ (.inl .S) a) (.inl .TR) b) (.inl .TL)
        (seg.reverse ++ τ (.inl .TL))) := by
  obtain ⟨_, _, ⟨pre, hTL, hpre⟩, hRET, hC1, ho⟩ := hF
  subst ha hb
  refine ⟨by simp, by simp, ⟨pre ++ seg, by simp [hTL], ?_⟩, by simp [hRET], by simp [hC1], ?_⟩
  · rw [List.append_assoc, ← hTR, hpre]
  · intro k h1 h2 h3 h4 h5
    rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
    exact ho k h1 h2 h3 h4 h5

end FrameLemmas

/-- The tape below the PRE segments. -/
def tailT (cSpec : ComputablePaperFastDFTSpec) (restT : List Sym) : List Sym :=
  leafSegOf cSpec ++ postSegsUp cSpec ++ restT

/-- Before PRE(ℓ) (before LEAF when `ℓ = depthOf cSpec`). -/
def PA {m : ℕ} (σ : BLoc m → List Sym) (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))) (restS restT : List Sym) (ℓ : ℕ) (τ : BLoc m → List Sym) : Prop :=
  Frame σ (tapeSyms cSpec ++ restT) (streamSyms (xsAt cSpec p_in xs ℓ) ++ restS)
    (preSegs (specAt cSpec ℓ) ++ tailT cSpec restT) (retAt cSpec p_in xs ℓ ++ σ (.inl .RET))
    (pinStk cSpec ℓ ++ σ (.inl .C1)) τ

/-- After POST(ℓ) (after LEAF when `ℓ = depthOf cSpec`). -/
def PB {m : ℕ} (σ : BLoc m → List Sym) (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))) (restS restT : List Sym) (ℓ : ℕ) (τ : BLoc m → List Sym) : Prop :=
  Frame σ (tapeSyms cSpec ++ restT)
    (streamSyms (levelEvalV (specAt cSpec ℓ) (pinAt cSpec p_in ℓ) (xsAt cSpec p_in xs ℓ)) ++ restS)
    (postTailAt cSpec ℓ ++ restT) (retAt cSpec p_in xs ℓ ++ σ (.inl .RET))
    (pinStk cSpec ℓ ++ σ (.inl .C1)) τ

section Tags

variable {m : ℕ} {σ τ : BLoc m → List Sym} {cSpec : ComputablePaperFastDFTSpec} {p_in : ℕ}
  {xs : List (Array (ℤ × ℤ))} {restS restT : List Sym}

theorem tag_pre {ℓ : ℕ} (hℓ : ℓ < depthOf cSpec) (hA : PA σ cSpec p_in xs restS restT ℓ τ) :
    (τ (.inl .TR)).head? = some symPre := by
  obtain ⟨q, pSub, m1, t1, r, ft, preTw, postTw, c0T, c1T, child, h1, -⟩ :=
    nav_step ℓ cSpec p_in xs hℓ
  rw [hA.2.1, h1]
  simp [preSegs, preSeg]

theorem tag_leaf (hA : PA σ cSpec p_in xs restS restT (depthOf cSpec) τ) :
    (τ (.inl .TR)).head? = some symLeaf := by
  obtain ⟨q, K, tw, -, h2, -, h4⟩ := nav_base cSpec
  rw [hA.2.1, h4, tailT, h2]
  simp [leafSeg]

theorem tag_post {ℓ : ℕ} (hℓ : ℓ < depthOf cSpec) (hB : PB σ cSpec p_in xs restS restT (ℓ + 1) τ) :
    (τ (.inl .TR)).head? = some symPost := by
  obtain ⟨q, pSub, m1, t1, r, ft, preTw, postTw, c0T, c1T, child, -, -, -, -, -, -, h7, -⟩ :=
    nav_step ℓ cSpec p_in xs hℓ
  rw [hB.2.1, h7]
  simp [postSeg]

theorem tag_end (hrestT : restT.head? ≠ some symPost) (hB : PB σ cSpec p_in xs restS restT 0 τ) :
    (τ (.inl .TR)).head? ≠ some symPost := by
  rw [hB.2.1, postTailAt_zero, List.nil_append]
  exact hrestT

/-- The state after pushing the guard on `TL` is `PA … 0`. -/
theorem pa_zero (hS : σ (.inl .S) = streamSyms xs ++ restS)
    (hTR : σ (.inl .TR) = tapeSyms cSpec ++ restT) :
    PA σ cSpec p_in xs restS restT 0 (Function.update σ (.inl .TL) (symGuard :: σ (.inl .TL))) := by
  unfold PA Frame
  refine ⟨?_, ?_, ⟨[], ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by simp), hS, xsAt_zero]
  · rw [Function.update_of_ne (by simp), hTR, specAt_zero, tapeSyms, tailT]
    simp only [List.append_assoc]
  · rw [Function.update_self]
    rfl
  · rw [specAt_zero, tapeSyms, tailT, List.nil_append]
    simp only [List.append_assoc]
  · rw [Function.update_of_ne (by simp), retAt_zero, List.nil_append]
  · rw [Function.update_of_ne (by simp), pinStk_zero, List.nil_append]
  · intro k _ _ h3 _ _
    exact Function.update_of_ne h3 _ _

/-- From `PB … 0`: the tape prefix on `TL` is the whole tape, and rewinding it gives the
pipeline's final state. -/
theorem pb_zero_final (hTR : σ (.inl .TR) = tapeSyms cSpec ++ restT)
    (hB : PB σ cSpec p_in xs restS restT 0 τ) :
    τ (.inl .TL) = (tapeSyms cSpec).reverse ++ symGuard :: σ (.inl .TL) ∧
    Function.update (Function.update τ (.inl .TL) (σ (.inl .TL))) (.inl .TR)
        ((tapeSyms cSpec).reverse.reverse ++ τ (.inl .TR)) =
      Function.update σ (.inl .S) (streamSyms (levelEvalV cSpec p_in xs) ++ restS) := by
  obtain ⟨hS, hTR', ⟨pre, hTL, hpre⟩, hRET, hC1, ho⟩ := hB
  simp only [specAt_zero, pinAt_zero, xsAt_zero, postTailAt_zero, retAt_zero, pinStk_zero,
    List.nil_append] at hS hTR' hpre hRET hC1
  have hpre' : pre = tapeSyms cSpec := (List.append_left_inj restT).1 hpre
  subst hpre'
  refine ⟨hTL, ?_⟩
  funext k
  by_cases hkTR : k = .inl .TR
  · subst hkTR
    simp [hTR', hTR]
  by_cases hkTL : k = .inl .TL
  · subst hkTL
    simp
  by_cases hkS : k = .inl .S
  · subst hkS
    simp [hS]
  rw [Function.update_of_ne hkTR, Function.update_of_ne hkTL, Function.update_of_ne hkS]
  by_cases hkR : k = .inl .RET
  · subst hkR
    exact hRET
  by_cases hkC : k = .inl .C1
  · subst hkC
    exact hC1
  exact ho k hkS hkTR hkTL hkR hkC

end Tags

/-- A level contract's `Runs` (on the embedded view) as a `W9_level` step triple. -/
theorem step_triple {mc mL : ℕ} (h : mc ≤ mL) {R RR : Type} (lens : Lens RR R)
    {P : Prog (BLoc mc) (fun _ => Sym) R} {T T' : ℕ} (τ τ' : BLoc mL → List Sym)
    (hP : Runs P (τ ∘ embL h) (τ' ∘ embL h) (fun _ => True) T)
    (hout : ∀ j : Fin mL, mc ≤ j.val → τ' (.inr j) = τ (.inr j))
    {Q : (BLoc mL → List Sym) → Prop} (hQ : Q τ') (hT : T ≤ T') :
    Triple [] (fun s => s.stk = τ) ((P.mapStk (embL h)).liftRegs lens) (fun s => Q s.stk) T' := by
  rintro ⟨v, S⟩ hs
  simp only at hs
  have hs' : τ = S := hs.symm
  subst hs'
  obtain ⟨v', t, e, ht⟩ := runs_embed h τ τ' hP hout (lens.get v)
  exact ⟨⟨lens.set v v', τ'⟩, t, Eval.liftRegs lens e v rfl, hQ, ht.trans hT⟩

/-- The input widths of a level from `ChainOK`. -/
theorem chain_in_width (wd : ℕ → ℕ) : ∀ (s : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
    (zs : List (Array (ℤ × ℤ))), ChainOK wd s p ℓ0 zs → StreamW (wd ℓ0) zs
  | .basePow2 _ _ _, _, _, _, h => fun z hz => (h.2 z hz).2.1
  | .step _ _ _ _ _ _ _ _ _ _ _, _, _, _, h => fun z hz => (h.2.2.2.1 z hz).2.1

#assert_std_axioms frame_W0 frame_step5 frame_step3 tag_pre tag_leaf tag_post tag_end pa_zero
  pb_zero_final step_triple chain_in_width

end WP.W9a
