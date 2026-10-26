import WP.W9a.LevelPost
import WP.W9a.Ret

/-!
# WP.W9a.LevelPostMain — `W9_postLevelProg_holds`

The POST level program `postProg` (WP.W9a.LevelPost) with the embedded `W9_retFlip` and
`W9_postNode` programs and the `W9_sweep` combinator (`g = t1`), taken as explicit hypotheses.
The sweep's outer-stack invariant tracks the RQ pops: before node `i`, RQ holds
`blkE (alts.drop i) ++ rq`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

theorem W9_postLevelProg_holds (Mul : ℕ → ℕ) (hSw : W9_sweep) (hFl : W9_retFlip)
    (hK : W9_postNode Mul) : W9_postLevelProg Mul := by
  obtain ⟨Cs, hSw⟩ := hSw
  obtain ⟨Cf, hFl⟩ := hFl
  obtain ⟨mf, Rf, Pf, hmf, hRfF, ⟨rf0⟩, hPfC, hPf⟩ := hFl ()
  obtain ⟨Ck, hK⟩ := hK
  obtain ⟨mk, Rk, Pk, hmk, hRkF, ⟨rk0⟩, hPkC, hPk⟩ := hK ()
  obtain ⟨mL, hmL⟩ : ∃ mL, mL = max (max mk mf) 4 := ⟨_, rfl⟩
  have hm4 : 4 ≤ mL := hmL ▸ le_max_right _ _
  have hmk' : mk ≤ mL := hmL ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hmf' : mf ≤ mL := hmL ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hmL64 : mL ≤ w9Scratch := hmL ▸ max_le (max_le hmk hmf) (by unfold w9Scratch; omega)
  obtain ⟨Qs, sweepF, hQF, ⟨qs0⟩, hswC, hsw⟩ := hSw mL Rk hm4
  haveI := hRkF
  haveI := hQF
  haveI := hRfF
  refine ⟨Ck + 2 * Cs + 2 * Cf + 64, fun _ => ⟨mL, (Rk × Qs) × (Rf × Option Sym),
    postProg hm4 (Pf.mapStk (embL hmf')) (sweepF (Pk.mapStk (embL hmk'))), hmL64,
    inferInstance, ⟨((rk0, qs0), (rf0, none))⟩,
    closed_postProg hm4 (closed_embL hmf' hPfC) (hswC _ (closed_embL hmk' hPkC)), ?_⟩⟩
  intro h w w' c0T c1T alts ys σ restS restT ret r1 hDims hTab hlen hys hW' hEW hOK hS hW0 hTR
    hRET hC1
  rintro ⟨⟨rs, ⟨rx, q⟩⟩, S⟩ hs
  simp only at hs
  have hs' : σ = S := hs.symm
  subst hs'
  have ht1pos : 0 < h.t1 := by
    rw [hDims.1]
    exact Nat.two_pow_pos _
  -- (1) header, `g = t1`
  have hTR' : σ (.inl .TR) = symPost :: (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++
      (postBody h.pSub h.r c0T c1T ++ restT)) := by
    rw [hTR, postSeg, List.cons_append, List.append_assoc]
  have e1 := hdrT1_eval hm4 h c0T c1T (postBody h.pSub h.r c0T c1T ++ restT) σ q hTR'
  generalize hσ1 : Function.update (Function.update (Function.update (Function.update σ (.inl .TR)
      (postBody h.pSub h.r c0T c1T ++ restT)) (.inl .TL)
      ((hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).reverse ++ symPost :: σ (.inl .TL)))
      (.inl .C0) (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ symGuard :: σ (.inl .C0)))
      (.inl .C2) (natSyms h.t1 ++ Sym.mark :: σ (.inl .C2)) = σ1 at e1
  have h1S : σ1 (.inl .S) = σ (.inl .S) := by rw [← hσ1]; simp
  have h1W : σ1 (.inl .W0) = [] := by rw [← hσ1]; simpa using hW0
  have h1TR : σ1 (.inl .TR) = postBody h.pSub h.r c0T c1T ++ restT := by rw [← hσ1]; simp
  have h1C0 : σ1 (.inl .C0) = hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ symGuard ::
      σ (.inl .C0) := by rw [← hσ1]; simp
  have h1C1 : σ1 (.inl .C1) = σ (.inl .C1) := by rw [← hσ1]; simp
  have h1C2 : σ1 (.inl .C2) = natSyms h.t1 ++ Sym.mark :: σ (.inl .C2) := by rw [← hσ1]; simp
  have h1RET : σ1 (.inl .RET) = σ (.inl .RET) := by rw [← hσ1]; simp
  have h1RQ : σ1 (.inl .RQ) = σ (.inl .RQ) := by rw [← hσ1]; simp
  -- (2) RET → RQ
  have hfl := hPf alts ret (σ1 ∘ embL hmf') (by show σ1 (.inl .RET) = _; rw [h1RET, hRET])
  rw [← Function.update_comp_eq_of_injective σ1 (embL_injective hmf'),
    ← Function.update_comp_eq_of_injective _ (embL_injective hmf')] at hfl
  obtain ⟨vf, tfl, efl, htfl⟩ := runs_embed hmf' σ1 _ hfl (fun j _ => by simp [embL]) rx
  generalize hσ2 : Function.update (Function.update σ1 (embL hmf' (.inl .RET)) ret)
      (embL hmf' (.inl .RQ)) (blkE alts ++ (σ1 ∘ embL hmf') (.inl .RQ)) = σ2 at efl
  have h2RQ : σ2 (.inl .RQ) = blkE alts ++ σ (.inl .RQ) := by
    rw [← hσ2]; simp [embL, h1RQ]
  have h2RET : σ2 (.inl .RET) = ret := by rw [← hσ2]; simp [embL]
  have h2o : ∀ k, k ≠ .inl .RET → k ≠ .inl .RQ → σ2 k = σ1 k := fun k hk1 hk2 => by
    rw [← hσ2, Function.update_of_ne (by simpa [embL] using hk2),
      Function.update_of_ne (by simpa [embL] using hk1)]
  -- (3) the sweep
  let f := postNodeV h.p h.pSub h.t1 h.r c0T c1T h.pChild
  let out : ℕ → List Sym := fun i => nodeSyms (f (alts.getD i (0, 0)) (groupAt h.t1 ys i).toArray)
  let J : ℕ → (LB → List Sym) → Prop := fun i τ =>
    τ = Function.update (outer σ2) .RQ (blkE (alts.drop i) ++ σ (.inl .RQ))
  have hκ : ∀ i < alts.length, ∀ σ' : BLoc mL → List Sym, J i (outer σ') →
      σ' (.inl .W0) = groupSyms (groupAt h.t1 ys i) →
      Triple [] (fun s => s.stk = σ') (Pk.mapStk (embL hmk'))
        (fun s => s.stk (.inl .W0) = out i ∧ s.stk (.inl .S) = σ' (.inl .S) ∧
          (∀ j, s.stk (.inr j) = σ' (.inr j)) ∧ J (i + 1) (outer s.stk))
        ((fun _ => Ck * postNodeBound Mul w h) i) := by
    intro i hi σ' hJ hW
    obtain ⟨a, had, hag, -⟩ := drop_cons_of_lt ((0, 0) : ℤ × ℤ) alts i hi
    have hJ' : outer σ' = Function.update (outer σ2) .RQ (blkE (alts.drop i) ++ σ (.inl .RQ)) :=
      hJ
    have hσ'C0 : σ' (.inl .C0) = σ2 (.inl .C0) := by
      have := congrFun hJ' .C0
      simpa [outer, Function.update_apply] using this
    have hσ'TR : σ' (.inl .TR) = σ2 (.inl .TR) := by
      have := congrFun hJ' .TR
      simpa [outer, Function.update_apply] using this
    have hσ'RQ : σ' (.inl .RQ) = blkE (alts.drop i) ++ σ (.inl .RQ) := by
      have := congrFun hJ' .RQ
      simpa [outer, Function.update_apply] using this
    have hglen := length_groupAt h.t1 alts.length i ys hlen hi
    have hrun := hPk h w c0T c1T a (groupAt h.t1 ys i).toArray (σ' ∘ embL hmk') restT
      (rq := blkE (alts.drop (i + 1)) ++ σ (.inl .RQ)) hDims
      ⟨_, show σ' (.inl .C0) = _ by rw [hσ'C0, h2o _ (by simp) (by simp), h1C0]⟩ hTab
      (by rw [List.size_toArray, hglen])
      (by
        intro row hrow
        rw [List.toList_toArray] at hrow
        exact hys row (List.mem_of_mem_drop (List.mem_of_mem_take hrow)))
      (by rw [← hag]; exact hOK i hi)
      (show σ' (.inl .W0) = _ by rw [hW, groupSyms_eq_matSyms])
      (show σ' (.inl .TR) = _ by rw [hσ'TR, h2o _ (by simp) (by simp), h1TR])
      (show σ' (.inl .RQ) = _ by rw [hσ'RQ, had, blkE_cons, List.append_assoc])
    rw [← Function.update_comp_eq_of_injective σ' (embL_injective hmk'),
      ← Function.update_comp_eq_of_injective _ (embL_injective hmk')] at hrun
    rintro ⟨r', S'⟩ hS'
    simp only at hS'
    subst hS'
    obtain ⟨v', t, e, ht⟩ := runs_embed hmk' S' _ hrun (fun j _ => by simp [embL]) r'
    refine ⟨_, t, e, ⟨?_, ?_, ?_, ?_⟩, ht⟩
    · simp only [embL]
      rw [Function.update_of_ne (by simp), Function.update_self]
      simp only [out, f, hag]
    · simp only [embL]
      rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
    · intro j
      simp only [embL]
      rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
    · simp only [embL, J]
      rw [outer_update_inl _ .RQ (by simp) (by simp), outer_update_W0, hJ', Function.update_idem]
  have hJ0 : J 0 (outer σ2) := by
    show outer σ2 = Function.update (outer σ2) .RQ (blkE (alts.drop 0) ++ σ (.inl .RQ))
    have h0 : blkE (alts.drop 0) ++ σ (.inl .RQ) = outer σ2 .RQ := by
      simp [outer, h2RQ]
    rw [h0, Function.update_eq_self]
  have hsweep := hsw (Pk.mapStk (embL hmk')) h.t1 alts.length ys out J
    (fun _ => Ck * postNodeBound Mul w h) ht1pos hlen
    (fun i _ => symLevel_not_mem_nodeSyms _) hκ σ2 restS (Sym.mark :: σ (.inl .C2))
    (by rw [h2o _ (by simp) (by simp), h1S, hS]) (by rw [h2o _ (by simp) (by simp), h1W])
    (by rw [h2o _ (by simp) (by simp), h1C2]) (TermOK.cons rfl _) hJ0
  obtain ⟨⟨r3, S3⟩, t3, e3, ⟨hS3, hW3, hsc3, hJ3⟩, ht3⟩ := hsweep ⟨rs, σ2⟩ rfl
  simp only at hS3 hW3 hsc3 hJ3
  have hS3eq : S3 = Function.update (Function.update σ2 (.inl .S)
      ((List.range alts.length).flatMap out ++ symLevel :: restS)) (.inl .RQ) (σ (.inl .RQ)) := by
    refine stk_of_parts ?_ ?_ ?_ ?_
    · rw [hS3, Function.update_of_ne (by simp), Function.update_self]
    · rw [hW3, Function.update_of_ne (by simp), Function.update_of_ne (by simp),
        h2o _ (by simp) (by simp), h1W]
    · intro j
      rw [hsc3 j, Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
    · rw [hJ3, outer_update_inl _ .RQ (by simp) (by simp), outer_update_S, List.drop_length,
        blkE_nil, List.nil_append]
  subst hS3eq
  -- (4) skip the body, pop `pSub`, drop `C2` and the header
  have e4 := postTail_eval (Function.update (Function.update σ2 (.inl .S)
    ((List.range alts.length).flatMap out ++ symLevel :: restS)) (.inl .RQ) (σ (.inl .RQ)))
    (some symLevel) h c0T c1T restT r1 (σ (.inl .C2)) (σ (.inl .C0))
    (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      h2o _ (by simp) (by simp), h1TR])
    (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      h2o _ (by simp) (by simp), h1C1, hC1])
    (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      h2o _ (by simp) (by simp), h1C2])
    (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      h2o _ (by simp) (by simp), h1C0])
  refine ⟨_, _, Eval.seq (liftG3_eval e1 rs rx) (Eval.seq (liftX3_eval efl rs (some (.tag 1)))
    (Eval.seq (liftS3_eval e3 (vf, some (.tag 1))) (liftG3_eval e4 r3 vf))), ⟨?_, trivial⟩, ?_⟩
  · -- the final stacks
    have hout : (List.range alts.length).flatMap out ++ symLevel :: restS =
        streamSyms (postLevel (postNodeV h.p h.pSub h.t1 h.r c0T c1T h.pChild) h.t1 alts ys) ++
          restS := post_out_eq _ h.t1 alts ys restS
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
      simp [embL, postSeg, List.reverse_append]
    by_cases hkRET : k = .inl .RET
    · subst hkRET
      simp [embL]
    by_cases hkRQ : k = .inl .RQ
    · subst hkRQ
      simp [embL]
    by_cases hkC1 : k = .inl .C1
    · subst hkC1
      simp [embL]
    by_cases hkC0 : k = .inl .C0
    · subst hkC0
      simp [embL]
    by_cases hkC2 : k = .inl .C2
    · subst hkC2
      simp [embL]
    have hkRET' : k ≠ embL hmf' (.inl .RET) := by simpa [embL] using hkRET
    have hkRQ' : k ≠ embL hmf' (.inl .RQ) := by simpa [embL] using hkRQ
    simp [hkS, hkTR, hkTL, hkRET, hkRET', hkRQ, hkRQ', hkC1, hkC0, hkC2]
  · -- the cost
    have hNE : 4 ≤ eb w := by unfold eb; omega
    have hLst : (streamSyms ys).length ≤ alts.length * h.t1 * (h.r * eb w') +
        alts.length * h.t1 + 1 := by
      have := groupSyms_length_le w' h.r ys (fun y hy => ⟨hys y hy, hW' y hy⟩)
      have e : ys.length * (h.r * eb w') = alts.length * h.t1 * (h.r * eb w') := by
        rw [hlen]; ring
      have e' : ys.length = alts.length * h.t1 := by rw [hlen, Nat.mul_comm]
      rw [length_streamSyms]
      omega
    have hLout : sumTo alts.length (fun i => (out i).length) ≤
        alts.length * (h.N * eb w) + alts.length := by
      rw [sumTo_length_flatMap]
      have hout' : (List.range alts.length).flatMap out = (postLevel f h.t1 alts ys).flatMap
          nodeSyms := by
        rw [postLevel_eq_map, flatMap_map']
      rw [hout', length_flatMap_nodeSyms]
      have hplen : (postLevel f h.t1 alts ys).length = alts.length := by
        rw [postLevel_eq_map, List.length_map, List.length_range]
      have := groupSyms_length_le w h.N (postLevel f h.t1 alts ys) (by
        intro y hy
        rw [postLevel_eq_map] at hy
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
        exact ⟨postNodeV_size _ _ _ _ _ _ _ _ _, (hOK i (List.mem_range.1 hi)).2.2.2.2.2.2⟩)
      rw [hplen] at this
      omega
    have hbt1 : bitLen h.t1 = natLog2Fuel h.t1 h.t1 + 1 := by
      rw [hDims.1, bitLen_two_pow]
      congr 1
      exact hDims.1.symm ▸ rfl
    have hD1 : alts.length * (bitLen h.t1 + 1) ≤
        alts.length * (eb w + 1) * (natLog2Fuel h.t1 h.t1 + 1) := by
      rw [hbt1, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by nlinarith)
    have htsw : t3 ≤ Ck * (alts.length * postNodeBound Mul w h) +
        Cs * (2 * (alts.length * h.t1 * (h.r * eb w' + 1) + alts.length * (h.N * eb w + 1) +
          alts.length * (eb w + 1) * (natLog2Fuel h.t1 h.t1 + 1) + 1)) := by
      refine ht3.trans ?_
      rw [sumTo_const]
      have e1' : alts.length * (Ck * postNodeBound Mul w h) =
          Ck * (alts.length * postNodeBound Mul w h) := by ring
      have e2' : alts.length * (h.N * eb w + 1) = alts.length * (h.N * eb w) + alts.length := by
        ring
      have e3' : alts.length * h.t1 * (h.r * eb w' + 1) =
          alts.length * h.t1 * (h.r * eb w') + alts.length * h.t1 := by ring
      rw [e1']
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    have hEW' : (blkE alts).length ≤ alts.length * eb w := length_blkE_le w alts hEW
    have htfl' : tfl ≤ Cf * (2 * (alts.length * (eb w + 1) * (natLog2Fuel h.t1 h.t1 + 1) + 1)) := by
      refine htfl.trans (Nat.mul_le_mul_left _ ?_)
      rw [length_retSeg]
      have : alts.length * eb w ≤ alts.length * (eb w + 1) * (natLog2Fuel h.t1 h.t1 + 1) := by
        calc alts.length * eb w ≤ alts.length * (eb w + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ alts.length * (eb w + 1) * (natLog2Fuel h.t1 h.t1 + 1) := Nat.le_mul_of_pos_right _
            (by omega)
      omega
    have hhp : (hdrSyms [h.p, h.pSub]).length ≤
        (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length := by
      rw [show postFields h.p h.pSub h.t1 h.r h.pChild = [h.p, h.pSub] ++ [h.t1, h.r,
        natLog2Fuel h.t1 h.t1, natLog2Fuel h.r h.r, h.pChild, barrettH h.pSub] from rfl,
        hdrSyms_append, List.length_append]
      omega
    have hbt1' : bitLen h.t1 ≤ (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length :=
      bitLen_le_length_hdrSyms _ _ (by simp [postFields])
    have hbps : bitLen h.pSub ≤ (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length :=
      bitLen_le_length_hdrSyms _ _ (by simp [postFields])
    have hseg : (postSeg h.p h.pSub h.t1 h.r c0T c1T h.pChild).length =
        (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length +
          (postBody h.pSub h.r c0T c1T).length + 1 := by
      rw [postSeg, List.length_cons, List.length_append]
    rw [hseg]
    unfold postLevelBound
    have := post_cost Ck Cs Cf (alts.length * postNodeBound Mul w h)
      (alts.length * (h.N * eb w + 1)) (alts.length * h.t1 * (h.r * eb w' + 1))
      (alts.length * (eb w + 1) * (h.mt1 + 1))
      (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length
      (postBody h.pSub h.r c0T c1T).length (hdrSyms [h.p, h.pSub]).length (bitLen h.t1)
      (bitLen h.pSub) tfl t3 htfl' htsw hhp hbt1' hbps
    exact this

#assert_std_axioms W9_postLevelProg_holds

end WP.W9a
