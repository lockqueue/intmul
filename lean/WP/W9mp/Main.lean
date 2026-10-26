import WP.W9mp.Prog

/-!
# WP.W9mp.Main — `W9_multiply_of_parts`

* `multProg_spec`: if the stage programs meet their contract bodies (`SpecPipe`, `SpecSplit`,
  `SpecSquare`, `SpecExtract`, `SpecRecon`), the composite `multProg` meets `W9_multiply`'s body
  (`SpecMult`) with constant `Cs + 2·Cp + Cq + Ce + Cr + 200`.
* `W9_multiply_of_parts_holds`: the contract-level statement, with **no extra hypotheses**. The
  `C1` header glue (push `b`, push `p0 = rootPrecision b K0`, pop) is built and proved here, from the
  framework's exact-evaluation programs (`WP.W9mp.Glue`, `WP.W9mp.GlueP0`).

Proof, as for the W9comp node composites. The step lemmas lift each stage through `callB`; the glue
steps are lifted through the register lens `mlg`. The chain is one right-nested `runs_seq` term. The
value bridges are `levelEvalV_eq_map` (inside `st_pipe`: the pipeline on one root node is the
snapshot transform) and `multiply_eq_root_phases` (the snapshot multiplier is
`reconstruct ∘ extract ∘ inverse ∘ square ∘ forward ∘ pack`). The premises of each stage come from
`RootOK` (chains, sizes, widths; reconstruct runs at digit width `wD := wR`). The cost is
`multCost_le`.
-/

namespace WP.W9mp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync WP.W9comp

attribute [local instance 10000] instZeroIntElementary

/-! ## One step per stage -/

section Steps

variable {m mi : ℕ} {Ri τ : Type} {Ci : ℕ} {Pi : Prog (BLoc mi) (fun _ => Sym) Ri}

theorem st_split (s : SpecSplit mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri) (b K0 k1 k2 A B : ℕ)
    (S : BLoc m → List Sym) (rA rB r0 : List Sym) (hA : A < 2 ^ (b * k1))
    (hB : B < 2 ^ (b * k2)) (hk : k1 + k2 ≤ 2 ^ K0) (hrA : TermOK rA) (hrB : TermOK rB)
    (hOA : S (.inl .OA) = natSyms A ++ rA) (hOB : S (.inl .OB) = natSyms B ++ rB)
    (hC0 : S (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0) :
    Runs (callB hm l Pi) S
      (Function.update (Function.update (Function.update S (.inl .OA) rA) (.inl .OB) rB)
        (.inl .S) (streamSyms [rootPackV b K0 k1 k2 A B] ++ S (.inl .S))) (fun _ => True)
      (Ci * (b * (k1 + k2) + 2 ^ K0 * (b + 1) + rootHdrLen b K0 k1 k2 + 1)) := by
  have := s b K0 k1 k2 A B (S ∘ emb hm) rA rB r0 hA hB hk hrA hrB hOA hOB hC0
  rw [upd_comp_emb, upd_comp_emb, upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

/-- The pipeline on one root node `x`: the output is the snapshot transform of `x`. -/
theorem st_pipe {Mul : ℕ → ℕ} (s : SpecPipe Mul mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri)
    (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ) (wd : ℕ → ℕ) (x : Array (ℤ × ℤ))
    (S : BLoc m → List Sym) (restS restT r1 : List Sym) (hc : ChainOK wd cSpec p_in 0 [x])
    (hS : S (.inl .S) = streamSyms [x] ++ restS) (hW0 : S (.inl .W0) = [])
    (hTR : S (.inl .TR) = tapeSyms cSpec ++ restT) (hrT : restT.head? ≠ some symPost)
    (hC1 : S (.inl .C1) = hdrSyms [p_in] ++ r1) :
    Runs (callB hm l Pi) S
      (Function.update S (.inl .S) (streamSyms [computablePaperFastDFT p_in cSpec x] ++ restS))
      (fun _ => True) (Ci * (pipeBound Mul wd cSpec p_in 0 1 + (tapeSyms cSpec).length + 1)) := by
  have := s cSpec p_in wd [x] (S ∘ emb hm) restS restT r1 hc hS hW0 hTR hrT hC1
  rw [upd_comp_emb, levelEvalV_eq_map] at this
  exact runs_callB hm l this fun j => by simp

theorem st_square {Mul : ℕ → ℕ} (s : SpecSquare Mul mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri)
    (b K0 k1 k2 wR : ℕ) (z : Array (ℤ × ℤ)) (S : BLoc m → List Sym) (restS r0 : List Sym)
    (hz : z.size = 2 ^ K0) (hw : ArrW wR z) (hw' : ArrW wR (rootSquareV (rootPrecision b K0) K0 z))
    (hC0 : S (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0)
    (hS : S (.inl .S) = streamSyms [z] ++ restS) :
    Runs (callB hm l Pi) S (Function.update S (.inl .S)
        (streamSyms [rootSquareV (rootPrecision b K0) K0 z] ++ restS)) (fun _ => True)
      (Ci * (2 ^ K0 * (4 * Mul wR + eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1)) := by
  have := s b K0 k1 k2 wR z (S ∘ emb hm) restS r0 hz hw hw' hC0 hS
  rw [upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

theorem st_extract (s : SpecExtract mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri)
    (b K0 k1 k2 wR : ℕ) (v : Array (ℤ × ℤ)) (S : BLoc m → List Sym) (restS r0 : List Sym)
    (hv : v.size = 2 ^ K0) (hk : k1 + k2 ≤ 2 ^ K0) (hw : ArrW wR v)
    (hC0 : S (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0)
    (hS : S (.inl .S) = streamSyms [v] ++ restS) :
    Runs (callB hm l Pi) S (Function.update (Function.update S (.inl .S) restS) (.inl .OA)
        (hdrSyms (rootDigits b K0 k1 k2 v) ++ S (.inl .OA))) (fun _ => True)
      (Ci * (2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1)) := by
  have := s b K0 k1 k2 wR v (S ∘ emb hm) restS r0 hv hk hw hC0 hS
  rw [upd_comp_emb, upd_comp_emb] at this
  exact runs_callB hm l this fun j => by simp

theorem st_recon (s : SpecRecon mi Ri Ci Pi) (hm : mi ≤ m) (l : Lens τ Ri)
    (b K0 k1 k2 wD : ℕ) (cs : List ℕ) (S : BLoc m → List Sym) (rA r0 : List Sym)
    (hlen : cs.length = k1 + k2) (hk : k1 + k2 ≤ 2 ^ K0) (hw : ∀ c ∈ cs, bitLen c ≤ wD)
    (hrA : TermOK rA) (hC0 : S (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0)
    (hOA : S (.inl .OA) = hdrSyms cs ++ rA) :
    Runs (callB hm l Pi) S
      (Function.update S (.inl .OA) (natSyms (reconstructChunksTree b cs) ++ rA))
      (fun _ => True) (Ci * ((k1 + k2) * (b + wD + K0 + 1) + rootHdrLen b K0 k1 k2 + 1)) := by
  have := s b K0 k1 k2 wD cs (S ∘ emb hm) rA r0 hlen hk hw hrA hC0 hOA
  rw [upd_comp_emb, hlen] at this
  exact runs_callB hm l this fun j => by simp

end Steps

/-! ## The composite -/

/-- **The root composite meets `W9_multiply`'s body.** -/
theorem multProg_spec {Mul : ℕ → ℕ} {m m1 m2 m3 m4 m5 : ℕ} {R1 R2 R3 R4 R5 : Type}
    {Cp Cs Cq Ce Cr : ℕ} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m)
    (hx : 3 ≤ m)
    {Pp : Prog (BLoc m1) (fun _ => Sym) R1} {Ps : Prog (BLoc m2) (fun _ => Sym) R2}
    {Pq : Prog (BLoc m3) (fun _ => Sym) R3} {Pe : Prog (BLoc m4) (fun _ => Sym) R4}
    {Pr : Prog (BLoc m5) (fun _ => Sym) R5}
    (sP : SpecPipe Mul m1 R1 Cp Pp) (sS : SpecSplit m2 R2 Cs Ps) (sQ : SpecSquare Mul m3 R3 Cq Pq)
    (sE : SpecExtract m4 R4 Ce Pe) (sR : SpecRecon m5 R5 Cr Pr) :
    SpecMult Mul m (MRegs R1 R2 R3 R4 R5) (Cs + 2 * Cp + Cq + Ce + Cr + 200)
      (multProg h1 h2 h3 h4 h5 hx Pp Ps Pq Pe Pr) := by
  intro cSpec b K0 k1 k2 A B wdF wdI wR σ rA rB r0 restT hA hB hk hrA hrB hRoot hOA hOB hC0 hW0
    hTR hrT
  obtain ⟨hcF, hcI, hfs, -, hwF, hwQ, his, hwI, hwD⟩ := hRoot
  rw [multiply_eq_root_phases]
  have chain :=
    runs_seq (st_split sS h2 (mlS R1 R2 R3 R4 R5) b K0 k1 k2 A B σ rA rB r0 hA hB hk hrA hrB
      hOA hOB hC0) <|
    runs_seq (runs_liftRegs (mlg R1 R2 R3 R4 R5) (runs_pushB_m hx b
      (.mark :: (hdrSyms [K0, k1, k2] ++ r0)) _ (termOK_mark _) (by simp [hC0, hdrSyms_cons]))) <|
    runs_seq (st_pipe sP h1 (mlP R1 R2 R3 R4 R5) cSpec b wdF _ _ (σ (.inl .S)) restT
      (σ (.inl .C1)) hcF (by simp) (by simp [hW0]) (by simp [hTR]) hrT (by simp)) <|
    runs_seq (runs_liftRegs (mlg R1 R2 R3 R4 R5) (runs_popHdr (K := BLoc m) (.inl .C1) b
      (σ (.inl .C1)) _ (by simp))) <|
    runs_seq (st_square sQ h3 (mlQ R1 R2 R3 R4 R5) b K0 k1 k2 wR _ _ (σ (.inl .S)) r0 hfs hwF hwQ
      (by simp [hC0]) (by simp)) <|
    runs_seq (runs_liftRegs (mlg R1 R2 R3 R4 R5) (runs_pushP0_m hx b K0 (hdrSyms [k1, k2] ++ r0)
      _ (by simp [hC0, hdrSyms_cons]))) <|
    runs_seq (st_pipe sP h1 (mlP R1 R2 R3 R4 R5) cSpec (rootPrecision b K0) wdI _ _
      (σ (.inl .S)) restT (σ (.inl .C1)) hcI (by simp) (by simp [hW0]) (by simp [hTR]) hrT
      (by simp)) <|
    runs_seq (runs_liftRegs (mlg R1 R2 R3 R4 R5) (runs_popHdr (K := BLoc m) (.inl .C1)
      (rootPrecision b K0) (σ (.inl .C1)) _ (by simp))) <|
    runs_seq (st_extract sE h4 (mlE R1 R2 R3 R4 R5) b K0 k1 k2 wR _ _ (σ (.inl .S)) r0 his hk hwI
      (by simp [hC0]) (by simp)) <|
    st_recon sR h5 (mlR R1 R2 R3 R4 R5) b K0 k1 k2 wR _ _ rA r0 (by simp [rootDigits]) hk hwD hrA
      (by simp [hC0]) (by simp)
  refine runs_mono (runs_congr chain ?_) (fun _ _ => trivial)
    (multCost_le Mul wR b K0 k1 k2 _ _ _ Cs Cp Cq Ce Cr hk)
  funext k
  rcases k with k | j
  · cases k <;> simp
  · simp

/-! ## The contract-level statement -/

/-- **`W9_multiply_of_parts`**, with no extra hypotheses: the multiplier from the pipeline and the
four root stages. -/
theorem W9_multiply_of_parts_holds (Mul : ℕ → ℕ) : W9_multiply_of_parts Mul := by
  intro cP cS cQ cE cR
  obtain ⟨Cp, kP⟩ := cP
  obtain ⟨Cs, kS⟩ := cS
  obtain ⟨Cq, kQ⟩ := cQ
  obtain ⟨Ce, kE⟩ := cE
  obtain ⟨Cr, kR⟩ := cR
  obtain ⟨m1, R1, Pp, hm1, hf1, hn1, hc1, sP⟩ := kP ()
  obtain ⟨m2, R2, Ps, hm2, hf2, hn2, hc2, sS⟩ := kS ()
  obtain ⟨m3, R3, Pq, hm3, hf3, hn3, hc3, sQ⟩ := kQ ()
  obtain ⟨m4, R4, Pe, hm4, hf4, hn4, hc4, sE⟩ := kE ()
  obtain ⟨m5, R5, Pr, hm5, hf5, hn5, hc5, sR⟩ := kR ()
  haveI := hf1; haveI := hf2; haveI := hf3; haveI := hf4; haveI := hf5
  haveI := hn1; haveI := hn2; haveI := hn3; haveI := hn4; haveI := hn5
  have h64 : w9Scratch = 64 := rfl
  have e1 : m1 ≤ max (max m1 (max m2 (max m3 (max m4 m5)))) 3 := by omega
  have e2 : m2 ≤ max (max m1 (max m2 (max m3 (max m4 m5)))) 3 := by omega
  have e3 : m3 ≤ max (max m1 (max m2 (max m3 (max m4 m5)))) 3 := by omega
  have e4 : m4 ≤ max (max m1 (max m2 (max m3 (max m4 m5)))) 3 := by omega
  have e5 : m5 ≤ max (max m1 (max m2 (max m3 (max m4 m5)))) 3 := by omega
  have ex : 3 ≤ max (max m1 (max m2 (max m3 (max m4 m5)))) 3 := by omega
  exact ⟨Cs + 2 * Cp + Cq + Ce + Cr + 200, fun _ =>
    ⟨_, MRegs R1 R2 R3 R4 R5, multProg e1 e2 e3 e4 e5 ex Pp Ps Pq Pe Pr,
      by omega, inferInstance, inferInstance,
      multProg_closed e1 e2 e3 e4 e5 ex hc1 hc2 hc3 hc4 hc5,
      multProg_spec e1 e2 e3 e4 e5 ex sP sS sQ sE sR⟩⟩

#assert_std_axioms st_split st_pipe st_square st_extract st_recon multProg_spec
  W9_multiply_of_parts_holds

end WP.W9mp
