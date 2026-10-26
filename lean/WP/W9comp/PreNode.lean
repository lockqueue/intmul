import WP.W9comp.PreProg
import Contracts.W9.Pipeline

/-!
# WP.W9comp.PreNode — `W9_preNode_of_phases`

* `preNodeProg_spec`: if every phase program meets its contract body (`SpecP1` … `SpecP8`), the
  composite `preNodeProg` meets `W9_preNode`'s body (`SpecPreNode`) with constant
  `C1 + C2 + C3 + C4 + C5 + C7 + C8 + 6`.
* `W9_preNode_of_phases_holds`: the contract-level statement. The phase contracts are hypotheses
  (discharged at stage assembly); the scratch count is the maximum of the phases' and the register type
  is `PreRegs`.

Proof. The step lemmas `pre_st1` … `pre_st8` lift one phase's `Runs` through `callB` (`runs_callB`;
`upd_comp_emb` moves the phase's updates across the embedding). The chain is one right-nested
`runs_seq` term, so the intermediate states are found by unification. Its side conditions (`W0`,
`TR`, the context) are `simp` facts about `Function.update`. The rewind consumes exactly the reversed
PRE body down to the guard (`guard_not_mem_preBody`). The cost is `preCost_le`. The final state is
checked stack by stack.
-/

namespace WP.W9comp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## One step per phase -/

section Steps

variable {m mi : ℕ} {Ri τ : Type} {Ci : ℕ} {Pi : Prog (BLoc mi) (fun _ => Sym) Ri}

theorem pre_st1 (s : SpecP1 mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri) (h : PreHdr) (w : ℕ)
    (x : Array (ℤ × ℤ)) (S : BLoc m → List Sym) (hD : PreDims h) (hC : PreCtx h S)
    (hx : x.size = h.N) (hwx : ArrW w x) (hwXR : MatW w (w9XRows h.t1 h.r x))
    (hW0 : S (.inl .W0) = blkE x.toList) :
    Runs (callB hm l Pi) S (Function.update S (.inl .W0) (matSyms (w9XRows h.t1 h.r x)))
      (fun _ => True) (Ci * preTransposeBound w h) := by
  have := s h w x (S ∘ emb hm) hD hC hx hwx hwXR hW0
  rw [upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

theorem pre_st2 (s : SpecP2 mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri) (h : PreHdr) (w : ℕ)
    (xR : Array (Array (ℤ × ℤ))) (S : BLoc m → List Sym) (hD : PreDims h) (hC : PreCtx h S)
    (hs : xR.size = h.t1) (hr : ∀ row ∈ xR.toList, row.size = h.r) (hw : MatW w xR)
    (ha : EntryW w (computableNyquistAltSumContiguous h.p_in h.pSub h.r (xR.getD (h.t1 / 2) #[])))
    (hW0 : S (.inl .W0) = matSyms xR) :
    Runs (callB hm l Pi) S (Function.update S (.inl .RET)
        ((entrySyms (computableNyquistAltSumContiguous h.p_in h.pSub h.r
          (xR.getD (h.t1 / 2) #[]))).reverse ++ S (.inl .RET)))
      (fun _ => True) (Ci * altSumBound w h) := by
  have := s h w xR (S ∘ emb hm) hD hC hs hr hw ha hW0
  rw [upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

theorem pre_st3 {Mul : ℕ → ℕ} (s : SpecP3 Mul mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri)
    (h : PreHdr) (w : ℕ) (ft : Array (List ℤ)) (xR : Array (Array (ℤ × ℤ))) (restT : List Sym)
    (S : BLoc m → List Sym) (hD : PreDims h) (hC : PreCtx h S) (hs : xR.size = h.t1)
    (hr : ∀ row ∈ xR.toList, row.size = h.r) (hw : MatW w xR)
    (hT : ∀ j < h.t1, TapsW w (ft.getD j []) ∧ (ft.getD j []).length ≤ h.W)
    (hstr : SpreadStrideOK h.s h.p_in h.pSub h.m1 h.t1 h.r ft xR)
    (hwU : MatW w (w9U h.p_in h.pSub h.m1 h.t1 h.r ft xR))
    (hW0 : S (.inl .W0) = matSyms xR) (hTR : S (.inl .TR) = filterRowsSyms h.t1 ft ++ restT) :
    Runs (callB hm l Pi) S (Function.update (Function.update (Function.update S (.inl .W0)
          (matSyms (w9U h.p_in h.pSub h.m1 h.t1 h.r ft xR)))
        (.inl .TR) restT) (.inl .TL) ((filterRowsSyms h.t1 ft).reverse ++ S (.inl .TL)))
      (fun _ => True) (Ci * spreadBound Mul w h) := by
  have eU := w9UStatic_eq h.s h.p_in h.pSub h.m1 h.t1 h.r ft xR hstr
  have := s h w ft xR (S ∘ emb hm) restT hD hC hs hr hw hT (by rw [eU]; exact hwU) hW0 hTR
  rw [upd_comp_emb, upd_comp_emb, upd_comp_emb, eU] at this
  exact runs_callB hm l this fun j => by simp

theorem pre_st4 {Mul : ℕ → ℕ} (s : SpecP4 Mul mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri)
    (h : PreHdr) (w : ℕ) (preTw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) (restT : List Sym)
    (S : BLoc m → List Sym) (hD : PreDims h) (hC : PreCtx h S) (hs : U.size = h.t1)
    (hr : ∀ row ∈ U.toList, row.size = h.r) (hw : MatW w U) (htw : TwW w h.r preTw)
    (hwP : MatW w (w9P h.pSub h.t1 h.r preTw U))
    (hW0 : S (.inl .W0) = matSyms U) (hTR : S (.inl .TR) = twSyms h.r preTw ++ restT) :
    Runs (callB hm l Pi) S (Function.update (Function.update (Function.update S (.inl .W0)
          (matSyms (w9P h.pSub h.t1 h.r preTw U)))
        (.inl .TR) restT) (.inl .TL) ((twSyms h.r preTw).reverse ++ S (.inl .TL)))
      (fun _ => True) (Ci * twistBound Mul w h) := by
  have := s h w preTw U (S ∘ emb hm) restT hD hC hs hr hw htw hwP hW0 hTR
  rw [upd_comp_emb, upd_comp_emb, upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

theorem pre_st5 (s : SpecP5 mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri) (h : PreHdr) (w : ℕ)
    (Pm : Array (Array (ℤ × ℤ))) (S : BLoc m → List Sym) (hD : PreDims h) (hC : PreCtx h S)
    (hs : Pm.size = h.t1) (hr : ∀ row ∈ Pm.toList, row.size = h.r) (hw : MatW w Pm)
    (hwQ : MatW w (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r Pm))) (hW0 : S (.inl .W0) = matSyms Pm) :
    Runs (callB hm l Pi) S
      (Function.update S (.inl .W0) (matSyms (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r Pm))))
      (fun _ => True) (Ci * synBound w h) := by
  have := s h w Pm (S ∘ emb hm) hD hC hs hr hw hwQ hW0
  rw [upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

theorem pre_st7 {Mul : ℕ → ℕ} (s : SpecP7 Mul mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri)
    (h : PreHdr) (w : ℕ) (postTw : Array (ℤ × ℤ)) (Q : Array (Array (ℤ × ℤ))) (restT : List Sym)
    (S : BLoc m → List Sym) (hD : PreDims h) (hC : PreCtx h S) (hs : Q.size = h.t1)
    (hr : ∀ row ∈ Q.toList, row.size = h.r) (hw : MatW w Q) (htw : TwW w h.r postTw)
    (hwQP : MatW w (w9QPost h.pSub h.t1 h.r postTw Q))
    (hW0 : S (.inl .W0) = matSyms Q) (hTR : S (.inl .TR) = twSyms h.r postTw ++ restT) :
    Runs (callB hm l Pi) S (Function.update (Function.update (Function.update S (.inl .W0)
          (matSyms (w9QPost h.pSub h.t1 h.r postTw Q)))
        (.inl .TR) restT) (.inl .TL) ((twSyms h.r postTw).reverse ++ S (.inl .TL)))
      (fun _ => True) (Ci * twistBound Mul w h) := by
  have := s h w postTw Q (S ∘ emb hm) restT hD hC hs hr hw htw hwQP hW0 hTR
  rw [upd_comp_emb, upd_comp_emb, upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

theorem pre_st8 (s : SpecP8 mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri) (h : PreHdr) (w : ℕ)
    (M : Array (Array (ℤ × ℤ))) (S : BLoc m → List Sym) (hC : PreCtx h S) (hs : M.size = h.t1)
    (hr : ∀ row ∈ M.toList, row.size = h.r) (hw : MatW w M) (hW0 : S (.inl .W0) = matSyms M) :
    Runs (callB hm l Pi) S (Function.update S (.inl .W0) (M.toList.flatMap nodeSyms))
      (fun _ => True) (Ci * emitBound w h) := by
  have := s h w M (S ∘ emb hm) hC hs hr hw hW0
  rw [upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

end Steps

/-! ## The composite -/

/-- **The PRE composite meets `W9_preNode`'s body.** -/
theorem preNodeProg_spec {Mul : ℕ → ℕ} {m m1 m2 m3 m4 m5 m7 m8 : ℕ}
    {R1 R2 R3 R4 R5 R7 R8 : Type} {C1 C2 C3 C4 C5 C7 C8 : ℕ}
    (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m) (h7 : m7 ≤ m)
    (h8 : m8 ≤ m) {P1 : Prog (BLoc m1) (fun _ => Sym) R1} {P2 : Prog (BLoc m2) (fun _ => Sym) R2}
    {P3 : Prog (BLoc m3) (fun _ => Sym) R3} {P4 : Prog (BLoc m4) (fun _ => Sym) R4}
    {P5 : Prog (BLoc m5) (fun _ => Sym) R5} {P7 : Prog (BLoc m7) (fun _ => Sym) R7}
    {P8 : Prog (BLoc m8) (fun _ => Sym) R8}
    (s1 : SpecP1 m1 R1 C1 P1) (s2 : SpecP2 m2 R2 C2 P2) (s3 : SpecP3 Mul m3 R3 C3 P3)
    (s4 : SpecP4 Mul m4 R4 C4 P4) (s5 : SpecP5 m5 R5 C5 P5) (s7 : SpecP7 Mul m7 R7 C7 P7)
    (s8 : SpecP8 m8 R8 C8 P8) :
    SpecPreNode Mul m (PreRegs R1 R2 R3 R4 R5 R7 R8) (C1 + C2 + C3 + C4 + C5 + C7 + C8 + 6)
      (preNodeProg h1 h2 h3 h4 h5 h7 h8 P1 P2 P3 P4 P5 P7 P8) := by
  intro h w ft preTw postTw x σ restT hD hC hT hx hN hW0 hTR
  obtain ⟨hwx, hwXR, hwU, hwP, hwQ, hwQP, hwalt, hstr⟩ := hN
  obtain ⟨hTrows, hTpre, hTpost⟩ := hT
  rw [preNodeV_eq_phases, altNodeV_eq_phase]
  rw [preNodeV_eq_phases] at hwQP
  rw [altNodeV_eq_phase] at hwalt
  have hL : (preBody h.t1 h.r ft preTw postTw).reverse.length ≤ preBodyBound w h := by
    rw [List.length_reverse]
    exact length_preBody_le w h ft preTw postTw ⟨hTrows, hTpre, hTpost⟩
  have chain :=
    runs_seq (pre_st1 s1 h1 (pl1 R1 R2 R3 R4 R5 R7 R8) h w x σ hD hC hx hwx hwXR hW0) <|
    runs_seq (pre_st2 s2 h2 (pl2 R1 R2 R3 R4 R5 R7 R8) h w (w9XRows h.t1 h.r x) _ hD
      (preCtx_of_eq hC (by simp) (by simp))
      (w9XRows_size _ _ _) (w9XRows_rows _ _ _) hwXR hwalt (by simp)) <|
    runs_seq (runs_pushConst (σ := PreRegs R1 R2 R3 R4 R5 R7 R8) (Sum.inl LB.TL : BLoc m)
      symGuard _) <|
    runs_seq (pre_st3 s3 h3 (pl3 R1 R2 R3 R4 R5 R7 R8) h w ft (w9XRows h.t1 h.r x)
      (twSyms h.r preTw ++ twSyms h.r postTw ++ restT) _ hD
      (preCtx_of_eq hC (by simp) (by simp))
      (w9XRows_size _ _ _) (w9XRows_rows _ _ _) hwXR hTrows hstr hwU
      (by simp)
      (by simp [hTR, preBody, List.append_assoc])) <|
    runs_seq (pre_st4 s4 h4 (pl4 R1 R2 R3 R4 R5 R7 R8) h w preTw
      (w9U h.p_in h.pSub h.m1 h.t1 h.r ft (w9XRows h.t1 h.r x)) (twSyms h.r postTw ++ restT) _ hD
      (preCtx_of_eq hC (by simp) (by simp))
      (w9U_size _ _ _ _ _ _ _) (w9U_rows _ _ _ _ _ _ _) hwU hTpre hwP
      (by simp) (by simp [List.append_assoc])) <|
    runs_seq (pre_st5 s5 h5 (pl5 R1 R2 R3 R4 R5 R7 R8) h w
      (w9P h.pSub h.t1 h.r preTw (w9U h.p_in h.pSub h.m1 h.t1 h.r ft (w9XRows h.t1 h.r x))) _ hD
      (preCtx_of_eq hC (by simp) (by simp))
      (w9P_size _ _ _ _ _) (w9P_rows _ _ _ _ _) hwP hwQ (by simp)) <|
    runs_seq (pre_st7 s7 h7 (pl7 R1 R2 R3 R4 R5 R7 R8) h w postTw
      (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r (w9P h.pSub h.t1 h.r preTw
        (w9U h.p_in h.pSub h.m1 h.t1 h.r ft (w9XRows h.t1 h.r x))))) restT _ hD
      (preCtx_of_eq hC (by simp) (by simp))
      (w9Q_size _ _ _ _) (w9Q_rows _ _ _ _) hwQ hTpost hwQP
      (by simp) (by simp)) <|
    runs_seq (pre_st8 s8 h8 (pl8 R1 R2 R3 R4 R5 R7 R8) h w
      (w9QPost h.pSub h.t1 h.r postTw (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r (w9P h.pSub h.t1 h.r
        preTw (w9U h.p_in h.pSub h.m1 h.t1 h.r ft (w9XRows h.t1 h.r x)))))) _
      (preCtx_of_eq hC (by simp) (by simp))
      (w9QPost_size _ _ _ _ _) (w9QPost_rows _ _ _ _ _) hwQP (by simp)) <|
    runs_rewind (plg R1 R2 R3 R4 R5 R7 R8) (src := (Sum.inl LB.TL : BLoc m)) (dst := Sum.inl LB.TR)
      (by simp) symGuard (preBody h.t1 h.r ft preTw postTw).reverse (σ (.inl .TL)) _
      (fun hm => guard_not_mem_preBody h.t1 h.r ft preTw postTw (List.mem_reverse.mp hm))
      (by simp [preBody, List.reverse_append, List.append_assoc])
  refine runs_mono (runs_congr chain ?_) (fun _ _ => trivial)
    (preCost_le Mul w h C1 C2 C3 C4 C5 C7 C8 _ hL)
  funext k
  rcases k with k | j
  · cases k <;> simp [hTR]
  · simp

/-! ## The contract-level statement -/

/-- **`W9_preNode_of_phases`**: the PRE node kernel from its phase contracts. -/
theorem W9_preNode_of_phases_holds (Mul : ℕ → ℕ) : W9_preNode_of_phases Mul := by
  intro c1 c2 c3 c4 c5 c7 c8
  obtain ⟨C1, k1⟩ := c1
  obtain ⟨C2, k2⟩ := c2
  obtain ⟨C3, k3⟩ := c3
  obtain ⟨C4, k4⟩ := c4
  obtain ⟨C5, k5⟩ := c5
  obtain ⟨C7, k7⟩ := c7
  obtain ⟨C8, k8⟩ := c8
  obtain ⟨m1, R1, P1, hm1, hf1, hn1, hc1, s1⟩ := k1 ()
  obtain ⟨m2, R2, P2, hm2, hf2, hn2, hc2, s2⟩ := k2 ()
  obtain ⟨m3, R3, P3, hm3, hf3, hn3, hc3, s3⟩ := k3 ()
  obtain ⟨m4, R4, P4, hm4, hf4, hn4, hc4, s4⟩ := k4 ()
  obtain ⟨m5, R5, P5, hm5, hf5, hn5, hc5, s5⟩ := k5 ()
  obtain ⟨m7, R7, P7, hm7, hf7, hn7, hc7, s7⟩ := k7 ()
  obtain ⟨m8, R8, P8, hm8, hf8, hn8, hc8, s8⟩ := k8 ()
  haveI := hf1; haveI := hf2; haveI := hf3; haveI := hf4; haveI := hf5; haveI := hf7
  haveI := hf8; haveI := hn1; haveI := hn2; haveI := hn3; haveI := hn4; haveI := hn5
  haveI := hn7; haveI := hn8
  have e1 : m1 ≤ max m1 (max m2 (max m3 (max m4 (max m5 (max m7 m8))))) := by omega
  have e2 : m2 ≤ max m1 (max m2 (max m3 (max m4 (max m5 (max m7 m8))))) := by omega
  have e3 : m3 ≤ max m1 (max m2 (max m3 (max m4 (max m5 (max m7 m8))))) := by omega
  have e4 : m4 ≤ max m1 (max m2 (max m3 (max m4 (max m5 (max m7 m8))))) := by omega
  have e5 : m5 ≤ max m1 (max m2 (max m3 (max m4 (max m5 (max m7 m8))))) := by omega
  have e7 : m7 ≤ max m1 (max m2 (max m3 (max m4 (max m5 (max m7 m8))))) := by omega
  have e8 : m8 ≤ max m1 (max m2 (max m3 (max m4 (max m5 (max m7 m8))))) := by omega
  exact ⟨C1 + C2 + C3 + C4 + C5 + C7 + C8 + 6, fun _ =>
    ⟨_, PreRegs R1 R2 R3 R4 R5 R7 R8, preNodeProg e1 e2 e3 e4 e5 e7 e8 P1 P2 P3 P4 P5 P7 P8,
      by omega, inferInstance, inferInstance,
      preNodeProg_closed e1 e2 e3 e4 e5 e7 e8 hc1 hc2 hc3 hc4 hc5 hc7 hc8,
      preNodeProg_spec e1 e2 e3 e4 e5 e7 e8 s1 s2 s3 s4 s5 s7 s8⟩⟩

#assert_std_axioms pre_st1 pre_st2 pre_st3 pre_st4 pre_st5 pre_st7 pre_st8 preNodeProg_spec
  W9_preNode_of_phases_holds

end WP.W9comp
