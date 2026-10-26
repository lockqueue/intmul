import WP.W9b.AltScale

/-!
# WP.W9b.AltKer1 — P2 kernel, part 1: the rescale composed; setup and skip (`altPre`)
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability
open IntMul (divRoundPow2 gRescale)

section Ker1

variable (k : W3Kit)

theorem rs_rescale {C : ℕ} (hok : W3Ok k C) (h : PreHdr) (X : AStk → List Sym)
    (r0 r1 AIb ARb : List Sym) (zi zr : ℤ) (wz : ℕ) (hAIb : TermOK AIb) (hARb : TermOK ARb)
    (hzi : bitLen zi.natAbs ≤ wz) (hzr : bitLen zr.natAbs ≤ wz)
    (hC0 : X .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0)
    (hC1 : X .C1 = hdrSyms [h.p_in] ++ r1)
    (hAI : X .AI = intSyms zi ++ AIb) (hAR : X .AR = intSyms zr ++ ARb) :
    Runs (rescale k) X
      (Function.update (Function.update X .AI
        (intSyms (gRescale (h.mr + h.p_in) h.pSub (zi, zr)).1 ++ AIb)) .AR
        (intSyms (gRescale (h.mr + h.p_in) h.pSub (zi, zr)).2 ++ ARb))
      (fun _ => True)
      (C * (2 * wz + 12 * (h.mr + h.p_in + h.pSub) + 8) + 50 * wz +
        130 * (h.mr + h.p_in + h.pSub) +
        26 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 300) := by
  have eH := rs_scaleHead k hok h X r0 r1 hC0 hC1
  have hSS : scaleMid X h .SS = natSyms (h.mr + h.p_in) ++ Sym.mark :: X .SS := by simp [scaleMid]
  have hP : scaleMid X h .P = natSyms h.pSub ++ Sym.mark :: X .P := by simp [scaleMid]
  have hD : scaleMid X h .D = Sym.mark :: X .D := by simp [scaleMid]
  have hAI' : scaleMid X h .AI = intSyms zi ++ AIb := by simp [scaleMid, hAI]
  have hAR' : scaleMid X h .AR = intSyms zr ++ ARb := by simp [scaleMid, hAR]
  have b1 := bitLen_le_self h.mr
  have b2 := bitLen_le_self h.p_in
  have b3 := bitLen_le_self h.pSub
  have b4 := bitLen_le_self (h.mr + h.p_in)
  rw [IntMulTM.Contracts.W8.gRescale_shift]
  by_cases hle : h.mr + h.p_in ≤ h.pSub
  · rw [if_pos hle]
    have eB := rs_scaleLE k hok (scaleMid X h) (h.mr + h.p_in) h.pSub zi zr _ _ _ AIb ARb
      (TermOK.cons rfl _) (TermOK.cons rfl _) (TermOK.cons rfl _) hAIb hARb hle hSS hP hD hAI'
      hAR'
    refine runs_post (runs_seq eH (runs_seq eB (rs_scaleTail k _ (h.pSub - (h.mr + h.p_in))
      (h.mr + h.p_in) h.p_in h.mr h.pSub (X .D) (X .SS) (X .PI) (X .Q) (X .P)
      (by simp [scaleMid]) (by simp [scaleMid]) (by simp [scaleMid]) (by simp [scaleMid])
      (by simp [scaleMid])))) ?_ ?_
    · clear eH eB
      funext x
      cases x <;> simp [scaleMid]
    · have b5 := bitLen_le_self (h.pSub - (h.mr + h.p_in))
      have hC : C * (bitLen h.mr + bitLen h.p_in + 1) +
          C * (bitLen h.pSub + bitLen (h.mr + h.p_in) + 1) +
          2 * (C * (h.pSub - (h.mr + h.p_in) + bitLen (h.pSub - (h.mr + h.p_in)) + 1)) ≤
          C * (2 * wz + 12 * (h.mr + h.p_in + h.pSub) + 8) := by
        have e : C * (bitLen h.mr + bitLen h.p_in + 1) +
            C * (bitLen h.pSub + bitLen (h.mr + h.p_in) + 1) +
            2 * (C * (h.pSub - (h.mr + h.p_in) + bitLen (h.pSub - (h.mr + h.p_in)) + 1)) =
            C * ((bitLen h.mr + bitLen h.p_in + 1) + (bitLen h.pSub + bitLen (h.mr + h.p_in) + 1) +
              2 * (h.pSub - (h.mr + h.p_in) + bitLen (h.pSub - (h.mr + h.p_in)) + 1)) := by ring
        rw [e]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
  · rw [if_neg hle]
    have hgt : h.pSub < h.mr + h.p_in := by omega
    have eB := rs_scaleGT k hok (scaleMid X h) (h.mr + h.p_in) h.pSub zi zr _ _ _ AIb ARb
      (TermOK.cons rfl _) (TermOK.cons rfl _) (TermOK.cons rfl _) hAIb hARb hgt hSS hP hD hAI'
      hAR'
    refine runs_post (runs_seq eH (runs_seq eB (rs_scaleTail k _ (h.mr + h.p_in - h.pSub)
      (h.mr + h.p_in) h.p_in h.mr h.pSub (X .D) (X .SS) (X .PI) (X .Q) (X .P)
      (by simp [scaleMid]) (by simp [scaleMid]) (by simp [scaleMid]) (by simp [scaleMid])
      (by simp [scaleMid])))) ?_ ?_
    · clear eH eB
      funext x
      cases x <;> simp [scaleMid]
    · have b5 := bitLen_le_self (h.mr + h.p_in - h.pSub)
      have hC : C * (bitLen h.mr + bitLen h.p_in + 1) +
          C * (bitLen (h.mr + h.p_in) + bitLen h.pSub + 1) +
          C * (bitLen zi.natAbs + 5 * (h.mr + h.p_in - h.pSub) + 3) +
          C * (bitLen zr.natAbs + 5 * (h.mr + h.p_in - h.pSub) + 3) ≤
          C * (2 * wz + 12 * (h.mr + h.p_in + h.pSub) + 8) := by
        have e : C * (bitLen h.mr + bitLen h.p_in + 1) +
            C * (bitLen (h.mr + h.p_in) + bitLen h.pSub + 1) +
            C * (bitLen zi.natAbs + 5 * (h.mr + h.p_in - h.pSub) + 3) +
            C * (bitLen zr.natAbs + 5 * (h.mr + h.p_in - h.pSub) + 3) =
            C * ((bitLen h.mr + bitLen h.p_in + 1) + (bitLen (h.mr + h.p_in) + bitLen h.pSub + 1) +
              (bitLen zi.natAbs + 5 * (h.mr + h.p_in - h.pSub) + 3) +
              (bitLen zr.natAbs + 5 * (h.mr + h.p_in - h.pSub) + 3)) := by ring
        rw [e]
        exact Nat.mul_le_mul_left _ (by omega)
      omega

end Ker1

theorem closed_cmpK (k : W3Kit) (x y : AStk) : (cmpK k x y).Closed :=
  closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, cmpNum, cmpBody, freeBelow_liftRegs,
    pushC, pushR, popR, restoreR, moveBits, moveBitsBody, Lib.skip])

theorem closed_scaleHead (k : W3Kit) (hN : k.PN.Closed) : (scaleHead k).Closed := by
  have hN' : k.PN.FreeBelow 0 := hN
  have h0 : (copyField 0 AStk.C0 AStk.P AStk.H).FreeBelow 0 := closed_copyField _ _ _ _
  have h5 : (copyField 5 AStk.C0 AStk.Q AStk.H).FreeBelow 0 := closed_copyField _ _ _ _
  simp [Prog.Closed, Prog.FreeBelow, scaleHead, kSym, addN, freeBelow_liftRegs, freeBelow_mapStk,
    hN', h0, h5, pushC, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody,
    restoreR, pushR, popR, Lib.skip]

theorem closed_scaleBranch (k : W3Kit) (hA : k.PA.Closed) (hM : k.PM.Closed) (hL : k.PL.Closed)
    (hR : k.PR.Closed) : (scaleBranch k).Closed := by
  have hM' : k.PM.FreeBelow 0 := hM
  have hL' : k.PL.FreeBelow 0 := hL
  have d1 : (divRoundS k .AI).FreeBelow 0 := closed_divRoundS k .AI hA hL hR
  have d2 : (divRoundS k .AR).FreeBelow 0 := closed_divRoundS k .AR hA hL hR
  simp [Prog.Closed, Prog.FreeBelow, scaleBranch, subN, shlS, shlV, kSym, freeBelow_liftRegs,
    freeBelow_mapStk, hM', hL', d1, d2, mvSym, popR, pushR]

theorem closed_scaleTail (k : W3Kit) : (scaleTail k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, scaleTail, kSym, freeBelow_liftRegs, dropBits, dropBody,
    popR, peekR]

theorem closed_rescale (k : W3Kit) (hA : k.PA.Closed) (hN : k.PN.Closed) (hM : k.PM.Closed)
    (hL : k.PL.Closed) (hR : k.PR.Closed) : (rescale k).Closed :=
  ⟨closed_scaleHead k hN, ⟨closed_cmpK k _ _, closed_scaleBranch k hA hM hL hR⟩,
    closed_scaleTail k⟩

#assert_std_axioms rs_rescale closed_cmpK closed_scaleHead closed_scaleBranch closed_scaleTail
  closed_rescale

end WP.W9b
