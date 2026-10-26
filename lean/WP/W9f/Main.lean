import WP.W9f.Cleanup

/-!
# WP.W9f.Main — the column-solve host program and its exact-stacks triple

`colProg`: guards on the private stacks, header phase, record pass, regime dispatch, cleanup.
`HT.colProg`: from the contract's initial stacks (`henc σ0 (σ0 ∘ F.loc)`) to the stacks with
`W0 := blkE (columnSolveBarrett …)`, the record moved `TR → TL`, everything else restored.
-/

namespace WP.W9f

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

variable {Mul : ℕ → ℕ} (K : Kit Mul)

/-- The column-solve host program. -/
def colProg : KP K :=
  (pushAll K privs).seq ((hdrPhase K).seq ((recPass (lS K)).seq ((dispatch K).seq (cleanup K))))

/-- Exact cost of `colProg` (before the final bound). -/
def colCost (h : PostHdr) (u2 : ℕ) (a c : ℤ) (μ : ℕ) : ℕ :=
  11 + (8 * mvCost (postFields h.p h.pSub h.t1 h.r h.pChild) +
    7 * (bitLen h.pSub + bitLen h.r + bitLen h.mt1 + bitLen h.H) + 37) +
  (10 * (bitLen a.natAbs + bitLen c.natAbs + bitLen μ) + 47) +
  (2 * (K.CC * (bitLen u2 + bitLen (h.r / 2) + 1)) + kreg K * cbase Mul h.t1 h.H h.mt1 + 2) +
  (2 * (bitLen h.pSub + bitLen h.H + bitLen h.mt1 + bitLen μ + bitLen (h.r / 2) +
    bitLen a.natAbs + bitLen c.natAbs) + 40)

theorem HT.colProg (σ0 : HL → List Sym) (h : PostHdr) (u2 : ℕ) (c0 c1 alt : ℤ × ℤ)
    (Y : Array (ℤ × ℤ)) (r0 restT rq r3 : List Sym)
    (hd : PostDims h) (hY : Y.size = h.t1) (hok : ColumnOK h.pSub h.t1 h.r u2 c0 c1 Y alt)
    (hO : ArrW h.H (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1
      Y alt))
    (hr3 : TermOK r3) (hC3v : σ0 hC3 = natSyms u2 ++ r3) (hRQv : σ0 hRQ = entrySyms alt ++ rq)
    (hC0 : σ0 F.C0.loc = hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ r0)
    (hW0 : σ0 F.W0.loc = blkE Y.toList)
    (hTR : σ0 F.TR.loc = postRecSyms c0.1 c1.1 (postMu h.H h.r u2 c0.1 c1.1) ++ restT) :
    HT [] (henc σ0 (fun f => σ0 f.loc)) (colProg K)
      (henc σ0 (Function.update (Function.update (Function.update (fun f => σ0 f.loc) .W0
        (blkE (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1 Y
          alt).toList)) .TR restT) .TL
        ((postRecSyms c0.1 c1.1 (postMu h.H h.r u2 c0.1 c1.1)).reverse ++ σ0 F.TL.loc)))
      (colCost K h u2 c0.1 c1.1 (postMu h.H h.r u2 c0.1 c1.1)) := by
  set s0 : F → List Sym := fun f => σ0 f.loc with hs0
  set μ := postMu h.H h.r u2 c0.1 c1.1 with hμ
  set fs := postFields h.p h.pSub h.t1 h.r h.pChild with hfs
  obtain ⟨hr2, hr2p⟩ := half_of_pow hd.2.1 (by have := hd.2.2.1; have := hd.2.2.2; omega)
  -- guards
  have h1 := HT.pushAll K σ0 privs s0 (by decide)
  set s1 := withMarks privs s0 with hs1
  -- header
  have h2 := HT.hdrPhase K σ0 s1 fs r0 (h.r / 2) (by simp [hfs, postFields])
    (by simp [hs1, withMarks, privs, hs0, hC0]) (by simp [hs1, withMarks, privs]; exact TermOK.cons rfl _)
    (by simpa [hfs, postFields] using hr2) hr2p
  set s2 := Function.update (Function.update (Function.update (Function.update s1
    .PQ (natSyms (fs.getD 1 0) ++ s1 .PQ)) .RH (natSyms (h.r / 2) ++ s1 .RH))
    .PK (natSyms (fs.getD 4 0) ++ s1 .PK)) .PH (natSyms (fs.getD 7 0) ++ s1 .PH) with hs2
  -- record
  have h3 := HT.recPass (lS K) σ0 s2 c0.1 c1.1 μ restT
    (by simp [hs2, hs1, withMarks, privs, hs0, hTR])
  set s3 := Function.update (Function.update (Function.update (Function.update
    (Function.update s2 .PA (intSyms c0.1 ++ s2 .PA)) .PC (intSyms c1.1 ++ s2 .PC)) .PMU
    (natSyms μ ++ s2 .PMU)) .TL ((postRecSyms c0.1 c1.1 μ).reverse ++ s2 .TL)) .TR restT with hs3
  -- dispatch
  have h4 := HT.dispatch K σ0 s3 h u2 c0 c1 alt Y (σ0 F.X.loc) (σ0 F.X'.loc) (σ0 F.TT.loc)
    (σ0 F.PQ.loc) (σ0 F.PH.loc) (σ0 F.PK.loc) (σ0 F.PMU.loc) (σ0 F.PA.loc) (σ0 F.PC.loc)
    (σ0 F.RH.loc) r3 rq hd hY hok hO hr3 hC3v hRQv
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0, hW0])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0, hfs, postFields])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0, hfs, postFields, PostHdr.H])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0, hfs, postFields, PostHdr.mt1])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0, hμ])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs3, hs2, hs1, withMarks, privs, hs0])
  set s4 := Function.update s3 .W0 (blkE (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H
    h.t1 h.mt1 h.r u2 c0.1 c1.1 Y alt).toList) with hs4
  -- cleanup
  have h5 := HT.cleanup K σ0 s4 s0 h.pSub h.H h.mt1 μ (h.r / 2) c0.1 c1.1
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0, hfs, postFields])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0, hfs, postFields, PostHdr.H])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0, hfs, postFields, PostHdr.mt1])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0, hμ])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0])
    (by simp [hs4, hs3, hs2, hs1, withMarks, privs, hs0])
  refine (HT.seq h1 (HT.seq h2 (HT.seq h3 (HT.seq h4 h5)))).of_eq ?_ ?_
  · congr 1
    funext f
    cases f <;> simp [restored, privs, hs4, hs3, hs2, hs1, withMarks, hs0]
  · simp only [colCost, privs, List.length_cons, List.length_nil, hfs, postFields, List.getD_cons_succ,
      List.getD_cons_zero, PostHdr.mt1, PostHdr.H]
    omega

end WP.W9f
