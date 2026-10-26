import WP.W9f.Dispatch

/-!
# WP.W9f.Cleanup — dropping the parameter copies and the guards; header cost facts
-/

namespace WP.W9f

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

variable {Mul : ℕ → ℕ} (K : Kit Mul)

/-- Drop every parameter copy and pop every guard. -/
def cleanup : KP K :=
  (dnm K .PQ).seq ((dnm K .PH).seq ((dnm K .PK).seq ((dnm K .PMU).seq ((dnm K .RH).seq
    ((dim K .PA).seq ((dim K .PC).seq ((popS F.X.loc).seq ((popS F.X'.loc).seq
      (popS F.TT.loc)))))))))

/-- The state after the cleanup: the private stacks hold their bases `b`. -/
def restored (s b : F → List Sym) (f : F) : List Sym := if f ∈ privs then b f else s f

theorem HT.cleanup (σ0 : HL → List Sym) (s b : F → List Sym) (q H k μ m : ℕ) (a c : ℤ)
    (hPQ : s .PQ = natSyms q ++ Sym.mark :: b .PQ) (hPH : s .PH = natSyms H ++ Sym.mark :: b .PH)
    (hPK : s .PK = natSyms k ++ Sym.mark :: b .PK)
    (hPMU : s .PMU = natSyms μ ++ Sym.mark :: b .PMU)
    (hRH : s .RH = natSyms m ++ Sym.mark :: b .RH)
    (hPA : s .PA = intSyms a ++ Sym.mark :: b .PA) (hPC : s .PC = intSyms c ++ Sym.mark :: b .PC)
    (hX : s .X = Sym.mark :: b .X) (hX' : s .X' = Sym.mark :: b .X')
    (hTT : s .TT = Sym.mark :: b .TT) :
    HT [] (henc σ0 s) (cleanup K) (henc σ0 (restored s b))
      (2 * (bitLen q + bitLen H + bitLen k + bitLen μ + bitLen m + bitLen a.natAbs +
        bitLen c.natAbs) + 40) := by
  have h1 := HT.dnm K σ0 s .PQ q (b .PQ) hPQ
  set s1 := Function.update s .PQ (b .PQ) with hs1
  have h2 := HT.dnm K σ0 s1 .PH H (b .PH) (by simp [hs1, hPH])
  set s2 := Function.update s1 .PH (b .PH) with hs2
  have h3 := HT.dnm K σ0 s2 .PK k (b .PK) (by simp [hs2, hs1, hPK])
  set s3 := Function.update s2 .PK (b .PK) with hs3
  have h4 := HT.dnm K σ0 s3 .PMU μ (b .PMU) (by simp [hs3, hs2, hs1, hPMU])
  set s4 := Function.update s3 .PMU (b .PMU) with hs4
  have h5 := HT.dnm K σ0 s4 .RH m (b .RH) (by simp [hs4, hs3, hs2, hs1, hRH])
  set s5 := Function.update s4 .RH (b .RH) with hs5
  have h6 := HT.dim K σ0 s5 .PA a (b .PA) (by simp [hs5, hs4, hs3, hs2, hs1, hPA])
  set s6 := Function.update s5 .PA (b .PA) with hs6
  have h7 := HT.dim K σ0 s6 .PC c (b .PC) (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hPC])
  set s7 := Function.update s6 .PC (b .PC) with hs7
  have h8 := HT.popF (σ := KReg K) σ0 s7 .X Sym.mark (b .X)
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hX])
  set s8 := Function.update s7 .X (b .X) with hs8
  have h9 := HT.popF (σ := KReg K) σ0 s8 .X' Sym.mark (b .X')
    (by simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hX'])
  set s9 := Function.update s8 .X' (b .X') with hs9
  have h10 := HT.popF (σ := KReg K) σ0 s9 .TT Sym.mark (b .TT)
    (by simp [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hTT])
  refine (HT.seq h1 (HT.seq h2 (HT.seq h3 (HT.seq h4 (HT.seq h5 (HT.seq h6 (HT.seq h7
    (HT.seq h8 (HT.seq h9 h10))))))))).of_eq ?_ (by omega)
  congr 1
  funext f
  cases f <;> simp [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, restored, privs]

/-! ## Header cost facts -/

theorem length_hdrSyms (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map (fun n => bitLen n + 1)).sum := by
  induction fs with
  | nil => rfl
  | cons n fs ih =>
    rw [hdrSyms_cons, List.length_append, List.length_cons, ih, length_natSyms]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Bit lengths of the POST header fields. -/
def hbits (h : PostHdr) : ℕ :=
  bitLen h.p + bitLen h.pSub + bitLen h.t1 + bitLen h.r + bitLen h.mt1 + bitLen h.mr +
    bitLen h.pChild + bitLen h.H

theorem hdrLen_eq (h : PostHdr) : h.hdrLen = hbits h + 9 := by
  unfold PostHdr.hdrLen hbits
  rw [length_hdrSyms]
  simp only [postFields, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, PostHdr.mt1,
    PostHdr.mr, PostHdr.H]
  omega

theorem mvCost_postFields (h : PostHdr) :
    mvCost (postFields h.p h.pSub h.t1 h.r h.pChild) ≤ 6 * h.hdrLen := by
  rw [hdrLen_eq]
  unfold hbits mvCost
  simp only [postFields, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, PostHdr.mt1,
    PostHdr.mr, PostHdr.H]
  omega

theorem cbase_le (Mul : ℕ → ℕ) (h : PostHdr) : cbase Mul h.t1 h.H h.mt1 ≤ columnBound Mul h := by
  unfold cbase columnBound solW
  have := Nat.mul_le_mul_left h.t1 (show Mul (8 * (h.H + 1)) + eb h.H + h.mt1 + 1 ≤
    8 * Mul (8 * (h.H + 1)) + 4 * eb h.H + h.mt1 + 1 by omega)
  omega

#assert_std_axioms HT.cleanup length_hdrSyms hdrLen_eq mvCost_postFields cbase_le

end WP.W9f
