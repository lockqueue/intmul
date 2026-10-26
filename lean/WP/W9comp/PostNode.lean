import WP.W9comp.PostProg
import Contracts.W9.Pipeline

/-!
# WP.W9comp.PostNode — `W9_postNode_of_phases`

* `postNodeProg_spec`: if every phase program meets its contract body (`SpecQ2`, `SpecQ3`,
  `SpecQ5`, `SpecQ6`), the composite `postNodeProg` meets `W9_postNode`'s body (`SpecPostNode`)
  with constant `C2 + C3 + 2·C5 + C6 + 6`.
* `W9_postNode_of_phases_holds`: the contract-level statement. The phase contracts are hypotheses
  (discharged when assembling `W9_kernels_of_machine`).

Proof, as for PRE (`WP.W9comp.PreNode`). The step lemmas lift each phase through `callB`. The chain
is one right-nested `runs_seq` term. The value bridges are:
* `w9QHatT_size` (from `PostDims`: `r = 2^m_r`) gives the size premise of `W9_columnRoutes`;
* `w9ZBarrett_eq_exact` (from the `ColumnOK` premises in `PostNodeOK`) turns the machine's Barrett
  columns into the snapshot's exact solvers, inside `post_st5`;
* `postNodeV_eq_phases` (`rfl`) gives the node value.

The width premises come from `PostNodeOK` (`MatW (min w H)` gives both `MatW H` for Q5 and `MatW w`
for Q6). The cost is `postCost_le`, with `N ≥ 1` from `PostDims`.
-/

namespace WP.W9comp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## One step per phase -/

section Steps

variable {m mi : ℕ} {Ri τ : Type} {Ci : ℕ} {Pi : Prog (BLoc mi) (fun _ => Sym) Ri}

theorem post_st2 (s : SpecQ2 mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri) (h : PostHdr) (w : ℕ)
    (qHat : Array (Array (ℤ × ℤ))) (S : BLoc m → List Sym) (hD : PostDims h) (hC : PostCtx h S)
    (hs : qHat.size = h.t1) (hr : ∀ row ∈ qHat.toList, row.size = h.r) (hwq : MatW w qHat)
    (hwT : ArrW w (w9QHatT h.t1 h.r qHat)) (hW0 : S (.inl .W0) = matSyms qHat) :
    Runs (callB hm l Pi) S (Function.update S (.inl .W0) (blkE (w9QHatT h.t1 h.r qHat).toList))
      (fun _ => True) (Ci * postTransposeBound w h) := by
  have := s h w qHat (S ∘ emb hm) hD hC hs hr hwq hwT hW0
  rw [upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

theorem post_st3 (s : SpecQ3 mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri) (h : PostHdr) (w : ℕ)
    (qHatT : Array (ℤ × ℤ)) (S : BLoc m → List Sym) (hD : PostDims h) (hC : PostCtx h S)
    (hs : qHatT.size = h.N) (hwT : ArrW w qHatT)
    (hwY : MatW w (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT)))
    (hW0 : S (.inl .W0) = blkE qHatT.toList) :
    Runs (callB hm l Pi) S (Function.update S (.inl .W0)
        (matSyms (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT))))
      (fun _ => True) (Ci * routesBound w h) := by
  have := s h w qHatT (S ∘ emb hm) hD hC hs hwT hwY hW0
  rw [upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

/-- Q5, with the Barrett columns already turned into the snapshot's exact solvers. -/
theorem post_st5 {Mul : ℕ → ℕ} (s : SpecQ5 Mul mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri)
    (h : PostHdr) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ) (Y : Array (Array (ℤ × ℤ)))
    (restT rq : List Sym) (S : BLoc m → List Sym) (hD : PostDims h) (hC : PostCtx h S)
    (hT : PostTablesW h.H h.r c0T c1T) (hs : Y.size = h.r)
    (hcols : ∀ col ∈ Y.toList, col.size = h.t1)
    (hcol : ∀ u2 < h.r, ColumnOK h.pSub h.t1 h.r u2 (read1D c0T u2) (read1D c1T u2)
      (Y.getD u2 #[]) alt)
    (hwZ : MatW h.H (w9ZExact h.pSub h.t1 h.r c0T c1T alt Y))
    (hW0 : S (.inl .W0) = matSyms Y) (hTR : S (.inl .TR) = postBody h.pSub h.r c0T c1T ++ restT)
    (hRQ : S (.inl .RQ) = entrySyms alt ++ rq) :
    Runs (callB hm l Pi) S (Function.update (Function.update (Function.update
          (Function.update S (.inl .W0) (matSyms (w9ZExact h.pSub h.t1 h.r c0T c1T alt Y)))
        (.inl .TR) restT) (.inl .TL) ((postBody h.pSub h.r c0T c1T).reverse ++ S (.inl .TL)))
        (.inl .RQ) rq)
      (fun _ => True) (Ci * (h.r * columnBound Mul h + h.N * eb h.H + eb h.H + 1)) := by
  have eZ := w9ZBarrett_eq_exact h.pSub h.t1 h.r c0T c1T alt Y hcol
  have := s h c0T c1T alt Y (S ∘ emb hm) restT rq hD hC hT hs hcols hcol
    (by rw [eZ]; exact hwZ) hW0 hTR hRQ
  rw [upd_comp_emb, upd_comp_emb, upd_comp_emb, upd_comp_emb, eZ] at this
  exact runs_callB hm l this fun j => by simp

theorem post_st6 (s : SpecQ6 mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri) (h : PostHdr) (w : ℕ)
    (Zc : Array (Array (ℤ × ℤ))) (S : BLoc m → List Sym) (hD : PostDims h) (hC : PostCtx h S)
    (hs : Zc.size = h.r) (hcols : ∀ col ∈ Zc.toList, col.size = h.t1) (hwZ : MatW w Zc)
    (hwO : ArrW w (w9Out h.p h.pSub h.t1 h.r Zc)) (hW0 : S (.inl .W0) = matSyms Zc) :
    Runs (callB hm l Pi) S (Function.update S (.inl .W0) (nodeSyms (w9Out h.p h.pSub h.t1 h.r Zc)))
      (fun _ => True) (Ci * outBound w h) := by
  have := s h w Zc (S ∘ emb hm) hD hC hs hcols hwZ hwO hW0
  rw [upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

end Steps

/-! ## The composite -/

theorem postDims_N_pos {h : PostHdr} (hD : PostDims h) : 1 ≤ h.N := by
  obtain ⟨e1, e2, -, -⟩ := hD
  have h1 : 0 < h.t1 := by rw [e1]; exact Nat.two_pow_pos _
  have h2 : 0 < h.r := by rw [e2]; exact Nat.two_pow_pos _
  exact Nat.mul_pos h1 h2

/-- **The POST composite meets `W9_postNode`'s body.** -/
theorem postNodeProg_spec {Mul : ℕ → ℕ} {m m2 m3 m5 m6 : ℕ} {R2 R3 R5 R6 : Type}
    {C2 C3 C5 C6 : ℕ} (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h5 : m5 ≤ m) (h6 : m6 ≤ m)
    {Q2 : Prog (BLoc m2) (fun _ => Sym) R2} {Q3 : Prog (BLoc m3) (fun _ => Sym) R3}
    {Q5 : Prog (BLoc m5) (fun _ => Sym) R5} {Q6 : Prog (BLoc m6) (fun _ => Sym) R6}
    (s2 : SpecQ2 m2 R2 C2 Q2) (s3 : SpecQ3 m3 R3 C3 Q3) (s5 : SpecQ5 Mul m5 R5 C5 Q5)
    (s6 : SpecQ6 m6 R6 C6 Q6) :
    SpecPostNode Mul m (PostRegs R2 R3 R5 R6) (C2 + C3 + 2 * C5 + C6 + 6)
      (postNodeProg h2 h3 h5 h6 Q2 Q3 Q5 Q6) := by
  intro h w c0T c1T alt qHat σ restT rq hD hC hT hs hr hN hW0 hTR hRQ
  obtain ⟨hwq, hwT, hwY, hcol, hwZ, -, hwO⟩ := hN
  rw [postNodeV_eq_phases]
  rw [postNodeV_eq_phases] at hwO
  have hTs : (w9QHatT h.t1 h.r qHat).size = h.N := w9QHatT_size h.t1 h.r qHat hD.2.1
  have hL : (postBody h.pSub h.r c0T c1T).reverse.length ≤ postBodyBound h := by
    rw [List.length_reverse]
    exact length_postBody_le h c0T c1T hT
  have chain :=
    runs_seq (post_st2 s2 h2 (ql2 R2 R3 R5 R6) h w qHat σ hD hC hs hr hwq hwT hW0) <|
    runs_seq (post_st3 s3 h3 (ql3 R2 R3 R5 R6) h w (w9QHatT h.t1 h.r qHat) _ hD
      (postCtx_of_eq hC (by simp)) hTs hwT hwY (by simp)) <|
    runs_seq (runs_pushConst (σ := PostRegs R2 R3 R5 R6) (Sum.inl LB.TL : BLoc m) symGuard _) <|
    runs_seq (post_st5 s5 h5 (ql5 R2 R3 R5 R6) h c0T c1T alt
      (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r (w9QHatT h.t1 h.r qHat))) restT rq _ hD
      (postCtx_of_eq hC (by simp)) hT (w9Y_size _ _ _ _ _) (w9Y_rows _ _ _ _ _) hcol
      (MatW.mono (min_le_right _ _) hwZ) (by simp) (by simp [hTR]) (by simp [hRQ])) <|
    runs_seq (post_st6 s6 h6 (ql6 R2 R3 R5 R6) h w
      (w9ZExact h.pSub h.t1 h.r c0T c1T alt
        (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r (w9QHatT h.t1 h.r qHat)))) _ hD
      (postCtx_of_eq hC (by simp)) (w9ZExact_size _ _ _ _ _ _ _) (w9ZExact_cols _ _ _ _ _ _ _)
      (MatW.mono (min_le_left _ _) hwZ) hwO (by simp)) <|
    runs_rewind (qlg R2 R3 R5 R6) (src := (Sum.inl LB.TL : BLoc m)) (dst := Sum.inl LB.TR)
      (by simp) symGuard (postBody h.pSub h.r c0T c1T).reverse (σ (.inl .TL)) _
      (fun hm => guard_not_mem_postBody h.pSub h.r c0T c1T (List.mem_reverse.mp hm))
      (by simp)
  refine runs_mono (runs_congr chain ?_) (fun _ _ => trivial)
    (postCost_le Mul w h C2 C3 C5 C6 _ hL (postDims_N_pos hD))
  funext k
  rcases k with k | j
  · cases k <;> simp [hTR]
  · simp

/-! ## The contract-level statement -/

/-- **`W9_postNode_of_phases`**: the POST node kernel from its phase contracts. -/
theorem W9_postNode_of_phases_holds (Mul : ℕ → ℕ) : W9_postNode_of_phases Mul := by
  intro c2 c3 c5 c6
  obtain ⟨C2, k2⟩ := c2
  obtain ⟨C3, k3⟩ := c3
  obtain ⟨C5, k5⟩ := c5
  obtain ⟨C6, k6⟩ := c6
  obtain ⟨m2, R2, Q2, hm2, hf2, hn2, hc2, s2⟩ := k2 ()
  obtain ⟨m3, R3, Q3, hm3, hf3, hn3, hc3, s3⟩ := k3 ()
  obtain ⟨m5, R5, Q5, hm5, hf5, hn5, hc5, s5⟩ := k5 ()
  obtain ⟨m6, R6, Q6, hm6, hf6, hn6, hc6, s6⟩ := k6 ()
  haveI := hf2; haveI := hf3; haveI := hf5; haveI := hf6
  haveI := hn2; haveI := hn3; haveI := hn5; haveI := hn6
  have e2 : m2 ≤ max m2 (max m3 (max m5 m6)) := by omega
  have e3 : m3 ≤ max m2 (max m3 (max m5 m6)) := by omega
  have e5 : m5 ≤ max m2 (max m3 (max m5 m6)) := by omega
  have e6 : m6 ≤ max m2 (max m3 (max m5 m6)) := by omega
  exact ⟨C2 + C3 + 2 * C5 + C6 + 6, fun _ =>
    ⟨_, PostRegs R2 R3 R5 R6, postNodeProg e2 e3 e5 e6 Q2 Q3 Q5 Q6,
      by omega, inferInstance, inferInstance,
      postNodeProg_closed e2 e3 e5 e6 hc2 hc3 hc5 hc6,
      postNodeProg_spec e2 e3 e5 e6 s2 s3 s5 s6⟩⟩

#assert_std_axioms post_st2 post_st3 post_st5 post_st6 postDims_N_pos postNodeProg_spec
  W9_postNode_of_phases_holds

end WP.W9comp
