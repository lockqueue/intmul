import WP.W9a.LevelPre

/-!
# WP.W9a.LevelPreMain — `W9_preLevelProg_holds`

The PRE level program `preProg` (WP.W9a.LevelPre) with the embedded `W9_retMark` and `W9_preNode`
programs and the `W9_sweep` combinator, all taken as explicit hypotheses. The sweep's
outer-stack invariant tracks the RET pushes: after `i` nodes RET holds
`retPre alt xs ret i = (blkE alts_{<i}).reverse ++ # :: ret`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

theorem W9_preLevelProg_holds (Mul : ℕ → ℕ) (hSw : W9_sweep) (hRm : W9_retMark)
    (hK : W9_preNode Mul) : W9_preLevelProg Mul := by
  obtain ⟨Cs, hSw⟩ := hSw
  obtain ⟨Crm, hRm⟩ := hRm
  obtain ⟨mrm, Rrm, Prm, hmrm, hRrmF, ⟨rrm0⟩, hPrmC, hPrm⟩ := hRm ()
  obtain ⟨Ck, hK⟩ := hK
  obtain ⟨mk, Rk, Pk, hmk, hRkF, ⟨rk0⟩, hPkC, hPk⟩ := hK ()
  obtain ⟨mL, hmL⟩ : ∃ mL, mL = max (max mk mrm) 4 := ⟨_, rfl⟩
  have hm4 : 4 ≤ mL := hmL ▸ le_max_right _ _
  have hmk' : mk ≤ mL := hmL ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hmrm' : mrm ≤ mL := hmL ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hmL64 : mL ≤ w9Scratch := hmL ▸ max_le (max_le hmk hmrm) (by unfold w9Scratch; omega)
  obtain ⟨Qs, sweepF, hQF, ⟨qs0⟩, hswC, hsw⟩ := hSw mL Rk hm4
  haveI := hRkF
  haveI := hQF
  haveI := hRrmF
  refine ⟨Ck + 2 * Cs + Crm + 64, fun _ => ⟨mL, (Rk × Qs) × (Rrm × Option Sym),
    preProg hm4 (Prm.mapStk (embL hmrm')) (sweepF (Pk.mapStk (embL hmk'))), hmL64,
    inferInstance, ⟨((rk0, qs0), (rrm0, none))⟩,
    closed_preProg hm4 (closed_embL hmrm' hPrmC) (hswC _ (closed_embL hmk' hPkC)), ?_⟩⟩
  intro h w w' ft preTw postTw xs σ restS restT r1 hDims hTab hxs hW' hS hW0 hTR hC1
  rintro ⟨⟨rs, ⟨rx, q⟩⟩, S⟩ hs
  simp only at hs
  have hs' : σ = S := hs.symm
  subst hs'
  -- (1) header, `g = 1`
  have hTR' : σ (.inl .TR) = symPre :: (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++
      (preBody h.t1 h.r ft preTw postTw ++ restT)) := by
    rw [hTR, preSeg, List.cons_append, List.append_assoc]
  have e1 := hdrOne_eval hm4 symPre (preTapeFields h.pSub h.m1 h.t1 h.r)
    (preBody h.t1 h.r ft preTw postTw ++ restT) σ q hTR'
  generalize hσ1 : Function.update (Function.update (Function.update (Function.update σ (.inl .TR)
      (preBody h.t1 h.r ft preTw postTw ++ restT)) (.inl .TL)
      ((hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).reverse ++ symPre :: σ (.inl .TL)))
      (.inl .C0) (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ symGuard :: σ (.inl .C0)))
      (.inl .C2) (natSyms 1 ++ Sym.mark :: σ (.inl .C2)) = σ1 at e1
  have h1S : σ1 (.inl .S) = σ (.inl .S) := by rw [← hσ1]; simp
  have h1W : σ1 (.inl .W0) = [] := by rw [← hσ1]; simpa using hW0
  have h1TR : σ1 (.inl .TR) = preBody h.t1 h.r ft preTw postTw ++ restT := by rw [← hσ1]; simp
  have h1C0 : σ1 (.inl .C0) = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ symGuard ::
      σ (.inl .C0) := by rw [← hσ1]; simp
  have h1C1 : σ1 (.inl .C1) = σ (.inl .C1) := by rw [← hσ1]; simp
  have h1C2 : σ1 (.inl .C2) = natSyms 1 ++ Sym.mark :: σ (.inl .C2) := by rw [← hσ1]; simp
  have h1RET : σ1 (.inl .RET) = σ (.inl .RET) := by rw [← hσ1]; simp
  -- (2) `#` on RET
  have hrm := hPrm (σ1 ∘ embL hmrm')
  rw [← Function.update_comp_eq_of_injective σ1 (embL_injective hmrm')] at hrm
  obtain ⟨vrm, trm, erm, htrm⟩ := runs_embed hmrm' σ1 _ hrm (fun j _ => by simp [embL]) rx
  generalize hσ2 : Function.update σ1 (embL hmrm' (.inl .RET))
      (symRet :: (σ1 ∘ embL hmrm') (.inl .RET)) = σ2 at erm
  have h2RET : σ2 (.inl .RET) = symRet :: σ (.inl .RET) := by
    rw [← hσ2]; simp [embL, h1RET]
  have h2o : ∀ k, k ≠ .inl .RET → σ2 k = σ1 k := fun k hk => by
    rw [← hσ2, Function.update_of_ne (by simpa [embL] using hk)]
  -- (3) the sweep
  let alt := altNodeV h.p_in h.pSub h.t1 h.r
  let out : ℕ → List Sym := fun i =>
    (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw (xs.getD i #[])).toList.flatMap nodeSyms
  let J : ℕ → (LB → List Sym) → Prop := fun i τ =>
    τ = Function.update (outer σ2) .RET (retPre alt xs (σ (.inl .RET)) i)
  have hκ : ∀ i < xs.length, ∀ σ' : BLoc mL → List Sym, J i (outer σ') →
      σ' (.inl .W0) = groupSyms (groupAt 1 xs i) →
      Triple [] (fun s => s.stk = σ') (Pk.mapStk (embL hmk'))
        (fun s => s.stk (.inl .W0) = out i ∧ s.stk (.inl .S) = σ' (.inl .S) ∧
          (∀ j, s.stk (.inr j) = σ' (.inr j)) ∧ J (i + 1) (outer s.stk))
        ((fun _ => Ck * preNodeBound Mul w h) i) := by
    intro i hi σ' hJ hW
    obtain ⟨x, hxd, hxg, hxm⟩ := drop_cons_of_lt (#[] : Array (ℤ × ℤ)) xs i hi
    have hJ' : outer σ' = Function.update (outer σ2) .RET (retPre alt xs (σ (.inl .RET)) i) := hJ
    have hσ'C0 : σ' (.inl .C0) = σ2 (.inl .C0) := by
      have := congrFun hJ' .C0
      simpa [outer, Function.update_apply] using this
    have hσ'C1 : σ' (.inl .C1) = σ2 (.inl .C1) := by
      have := congrFun hJ' .C1
      simpa [outer, Function.update_apply] using this
    have hσ'TR : σ' (.inl .TR) = σ2 (.inl .TR) := by
      have := congrFun hJ' .TR
      simpa [outer, Function.update_apply] using this
    have hσ'RET : σ' (.inl .RET) = retPre alt xs (σ (.inl .RET)) i := by
      have := congrFun hJ' .RET
      simpa [outer, Function.update_apply] using this
    have hrun := hPk h w ft preTw postTw x (σ' ∘ embL hmk') restT hDims
      ⟨⟨_, show σ' (.inl .C0) = _ by rw [hσ'C0, h2o _ (by simp), h1C0]⟩,
        ⟨_, show σ' (.inl .C1) = _ by rw [hσ'C1, h2o _ (by simp), h1C1, hC1]⟩⟩ hTab
      (hxs x hxm).1 (hxs x hxm).2
      (show σ' (.inl .W0) = _ by rw [hW, groupAt_one_of_drop xs i x hxd, groupSyms_singleton])
      (show σ' (.inl .TR) = _ by rw [hσ'TR, h2o _ (by simp), h1TR])
    rw [← Function.update_comp_eq_of_injective σ' (embL_injective hmk'),
      ← Function.update_comp_eq_of_injective _ (embL_injective hmk')] at hrun
    rintro ⟨r', S'⟩ hS'
    simp only at hS'
    subst hS'
    obtain ⟨v', t, e, ht⟩ := runs_embed hmk' S' _ hrun (fun j _ => by simp [embL]) r'
    refine ⟨_, t, e, ⟨?_, ?_, ?_, ?_⟩, ht⟩
    · simp only [embL]
      rw [Function.update_of_ne (by simp), Function.update_self]
      simp only [out, hxg]
    · simp only [embL]
      rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
    · intro j
      simp only [embL]
      rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
    · simp only [embL, J, Function.comp_apply]
      rw [outer_update_inl _ .RET (by simp) (by simp), outer_update_W0, hJ', Function.update_idem,
        hσ'RET, retPre_succ alt xs _ i x hxd]
  have hJ0 : J 0 (outer σ2) := by
    show outer σ2 = Function.update (outer σ2) .RET (retPre alt xs (σ (.inl .RET)) 0)
    have h0 : retPre alt xs (σ (.inl .RET)) 0 = outer σ2 .RET := by
      simp [retPre, outer, h2RET, blkE_nil]
    rw [h0, Function.update_eq_self]
  have hsweep := hsw (Pk.mapStk (embL hmk')) 1 xs.length xs out J
    (fun _ => Ck * preNodeBound Mul w h) Nat.one_pos (by rw [Nat.one_mul])
    (fun i _ => symLevel_not_mem_flatMap_nodeSyms _) hκ σ2 restS (Sym.mark :: σ (.inl .C2))
    (by rw [h2o _ (by simp), h1S, hS]) (by rw [h2o _ (by simp), h1W])
    (by rw [h2o _ (by simp), h1C2]) (TermOK.cons rfl _) hJ0
  obtain ⟨⟨r3, S3⟩, t3, e3, ⟨hS3, hW3, hsc3, hJ3⟩, ht3⟩ := hsweep ⟨rs, σ2⟩ rfl
  simp only at hS3 hW3 hsc3 hJ3
  have hS3eq : S3 = Function.update (Function.update σ2 (.inl .S)
      ((List.range xs.length).flatMap out ++ symLevel :: restS)) (.inl .RET)
      (retPre alt xs (σ (.inl .RET)) xs.length) := by
    refine stk_of_parts ?_ ?_ ?_ ?_
    · rw [hS3, Function.update_of_ne (by simp), Function.update_self]
    · rw [hW3, Function.update_of_ne (by simp), Function.update_of_ne (by simp), h2o _ (by simp),
        h1W]
    · intro j
      rw [hsc3 j, Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
    · rw [hJ3, outer_update_inl _ .RET (by simp) (by simp), outer_update_S]
  subst hS3eq
  -- (4) skip the body, push `pSub`, drop `C2` and the header
  obtain ⟨v4, t4, e4, ht4⟩ := skipPre_eval hm4 (Function.update (Function.update σ2 (.inl .S)
    ((List.range xs.length).flatMap out ++ symLevel :: restS)) (.inl .RET)
    (retPre alt xs (σ (.inl .RET)) xs.length)) h ft preTw postTw restT
    (symGuard :: σ (.inl .C0)) (some symLevel)
    (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), h2o _ (by simp),
      h1TR])
    (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), h2o _ (by simp),
      h1C0])
  generalize hσ4 : Function.update (Function.update (Function.update (Function.update σ2 (.inl .S)
    ((List.range xs.length).flatMap out ++ symLevel :: restS)) (.inl .RET)
    (retPre alt xs (σ (.inl .RET)) xs.length)) (.inl .TR) restT) (.inl .TL)
    ((preBody h.t1 h.r ft preTw postTw).reverse ++ Function.update (Function.update σ2 (.inl .S)
      ((List.range xs.length).flatMap out ++ symLevel :: restS)) (.inl .RET)
      (retPre alt xs (σ (.inl .RET)) xs.length) (.inl .TL)) = σ4 at e4
  have h4C0 : σ4 (.inl .C0) = natSyms h.pSub ++ Sym.mark ::
      (hdrSyms [h.m1, h.t1, h.r, natLog2Fuel h.t1 h.t1, natLog2Fuel h.r h.r,
        effectiveFilterWidth h.m1 h.r, kroneckerSpreadNumBlocks h.m1 h.r, strideOf h.pSub] ++
        symGuard :: σ (.inl .C0)) := by
    rw [← hσ4]
    simp only [Function.update_apply]
    simp [h2o, h1C0, preTapeFields, hdrSyms_cons]
  have e5 := pushPSub_eval hm4 σ4 v4 h.pSub _ h4C0
  have e6 := cleanup_eval (Function.update σ4 (.inl .C1) (natSyms h.pSub ++ Sym.mark ::
    σ4 (.inl .C1))) (some .mark) 1 (preTapeFields h.pSub h.m1 h.t1 h.r) (σ (.inl .C2))
    (σ (.inl .C0))
    (by rw [Function.update_of_ne (by simp), ← hσ4]; simp only [Function.update_apply];
        simp [h2o, h1C2])
    (by rw [Function.update_of_ne (by simp), ← hσ4]; simp only [Function.update_apply];
        simp [h2o, h1C0])
  refine ⟨_, _, Eval.seq (liftG3_eval e1 rs rx) (Eval.seq (liftX3_eval erm rs (some symLevel))
    (Eval.seq (liftS3_eval e3 (vrm, some symLevel))
      (liftG3_eval (Eval.seq e4 (Eval.seq e5 e6)) r3 vrm))), ⟨?_, trivial⟩, ?_⟩
  · -- the final stacks
    have hout : (List.range xs.length).flatMap out ++ symLevel :: restS =
        streamSyms (xs.flatMap fun x =>
          (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList) ++ restS :=
      pre_out_eq h ft preTw postTw xs restS
    have hret : retPre alt xs (σ (.inl .RET)) xs.length =
        retSeg (xs.map (altNodeV h.p_in h.pSub h.t1 h.r)) ++ σ (.inl .RET) :=
      retPre_length alt xs _
    subst hσ4
    subst hσ2
    subst hσ1
    funext k
    by_cases hkS : k = .inl .S
    · subst hkS
      simp [embL, hout]
    by_cases hkTR : k = .inl .TR
    · subst hkTR
      simp [embL]
    by_cases hkTL : k = .inl .TL
    · subst hkTL
      simp [embL, preSeg, List.reverse_append]
    by_cases hkRET : k = .inl .RET
    · subst hkRET
      simp [embL, hret]
    by_cases hkC1 : k = .inl .C1
    · subst hkC1
      simp [embL, hdrSyms_cons, hdrSyms_nil]
    by_cases hkC0 : k = .inl .C0
    · subst hkC0
      simp [embL]
    by_cases hkC2 : k = .inl .C2
    · subst hkC2
      simp [embL]
    have hkRET' : k ≠ embL hmrm' (.inl .RET) := by simpa [embL] using hkRET
    simp [Function.update_apply, hkS, hkTR, hkTL, hkRET, hkRET', hkC1, hkC0, hkC2]
  · -- the cost
    have hLst : (streamSyms xs).length ≤ xs.length * (h.N * eb w) + xs.length + 1 := by
      have := groupSyms_length_le w h.N xs (fun x hx => ⟨(hxs x hx).1, (hxs x hx).2.1⟩)
      rw [length_streamSyms]
      omega
    have hys := length_flatMap_preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw xs
    have hLout : sumTo xs.length (fun i => (out i).length) ≤
        xs.length * h.t1 * (h.r * eb w') + xs.length * h.t1 := by
      rw [sumTo_length_flatMap, flatMap_range_getD (#[] : Array (ℤ × ℤ))
        (fun x => (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList.flatMap
          nodeSyms), ← List.flatMap_assoc, length_flatMap_nodeSyms, hys]
      have := groupSyms_length_le w' h.r
        (xs.flatMap fun x => (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList)
        (by
          intro y hy
          refine ⟨?_, hW' y hy⟩
          obtain ⟨x, -, hyx⟩ := List.mem_flatMap.1 hy
          exact preNodeV_rows h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x y hyx)
      rw [hys] at this
      omega
    have hEW : 4 ≤ eb w := by unfold eb; omega
    have htsw : t3 ≤ Ck * (xs.length * preNodeBound Mul w h) +
        Cs * (2 * (xs.length * (h.N * eb w + 1) + xs.length * h.t1 * (h.r * eb w' + 1) +
          xs.length * eb w + 1)) := by
      refine ht3.trans ?_
      rw [sumTo_const, bitLen_one]
      have e1' : xs.length * (Ck * preNodeBound Mul w h) = Ck * (xs.length * preNodeBound Mul w h) :=
        by ring
      have e2' : xs.length * (h.N * eb w + 1) = xs.length * (h.N * eb w) + xs.length := by ring
      have e3' : xs.length * h.t1 * (h.r * eb w' + 1) =
          xs.length * h.t1 * (h.r * eb w') + xs.length * h.t1 := by ring
      have e4' : 4 * xs.length ≤ xs.length * eb w := by
        calc 4 * xs.length = xs.length * 4 := Nat.mul_comm _ _
          _ ≤ xs.length * eb w := Nat.mul_le_mul_left _ hEW
      rw [e1']
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    have hhp : (hdrSyms [h.pSub, h.m1]).length ≤
        (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length := by
      rw [show preTapeFields h.pSub h.m1 h.t1 h.r = [h.pSub, h.m1] ++ [h.t1, h.r,
        natLog2Fuel h.t1 h.t1, natLog2Fuel h.r h.r, effectiveFilterWidth h.m1 h.r,
        kroneckerSpreadNumBlocks h.m1 h.r, strideOf h.pSub] from rfl, hdrSyms_append,
        List.length_append]
      omega
    have hbt1 : bitLen h.t1 ≤ (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length :=
      bitLen_le_length_hdrSyms _ _ (by simp [preTapeFields])
    have hbps : bitLen h.pSub ≤ (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length :=
      bitLen_le_length_hdrSyms _ _ (by simp [preTapeFields])
    have hinc : incSeqCost 6 10 h.t1 ≤ 16 * (preBody h.t1 h.r ft preTw postTw).length := by
      have h1 := incSeqCost_le 6 10 h.t1
      have h2 := length_chunks_le symSub (preChunks h.t1 ft)
      rw [length_preChunks] at h2
      have h3 : ((preChunks h.t1 ft).flatMap (· ++ [symSub])).length ≤
          (preBody h.t1 h.r ft preTw postTw).length := by
        rw [preBody_eq, List.length_append]
        omega
      omega
    have hseg : (preSeg h.pSub h.m1 h.t1 h.r ft preTw postTw).length =
        (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length +
          (preBody h.t1 h.r ft preTw postTw).length + 1 := by
      rw [preSeg, List.length_cons, List.length_append]
    rw [hseg, bitLen_one]
    unfold preLevelBound
    exact pre_cost Ck Cs Crm (xs.length * preNodeBound Mul w h) (xs.length * (h.N * eb w + 1))
      (xs.length * h.t1 * (h.r * eb w' + 1)) (xs.length * eb w)
      (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length
      (preBody h.t1 h.r ft preTw postTw).length (hdrSyms [h.pSub, h.m1]).length (bitLen h.t1)
      (incSeqCost 6 10 h.t1) (bitLen h.pSub) trm t3 t4 htrm htsw ht4 hhp hbt1 hbps hinc

#assert_std_axioms W9_preLevelProg_holds

end WP.W9a
