import WP.W9b.AltKer2

/-!
# WP.W9b.AltKer3 — P2 kernel, part 3: rescale, emit onto `RET`, cleanup (`altPost`)
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability
open IntMul (gRescale)

section Ker3

variable (k : W3Kit)

/-- Rescale, push the entry reversed onto `RET`, drop the guards and `R`. -/
def altPost : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (rescale k) (.seq (kSym k (mvIntOnly .AI .RET)) (.seq (kSym k (pushC .RET .sep2))
  (.seq (kSym k (mvIntOnly .AR .RET)) (.seq (kSym k (pushC .RET .sep))
  (.seq (kSym k (popR .AR)) (.seq (kSym k (popR .AI)) (.seq (kSym k (popR .AR'))
  (.seq (kSym k (popR .AI')) (.seq (kSym k (popR .K)) (.seq (kSym k (popR .J))
  (.seq (kSym k (dropBits .R)) (kSym k (popR .R)))))))))))))

theorem rs_altPost {C : ℕ} (hok : W3Ok k C) (h : PreHdr) (Z : AStk → List Sym)
    (r0 r1 : List Sym) (zi zr : ℤ) (wz : ℕ) (XAI XAR XAR' XAI' XK XJ XR : List Sym)
    (hzi : bitLen zi.natAbs ≤ wz) (hzr : bitLen zr.natAbs ≤ wz)
    (hC0 : Z .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0)
    (hC1 : Z .C1 = hdrSyms [h.p_in] ++ r1)
    (hAI : Z .AI = intSyms zi ++ Sym.mark :: XAI) (hAR : Z .AR = intSyms zr ++ Sym.mark :: XAR)
    (hAR' : Z .AR' = Sym.mark :: XAR') (hAI' : Z .AI' = Sym.mark :: XAI')
    (hK : Z .K = Sym.mark :: XK) (hJ : Z .J = Sym.mark :: XJ)
    (hR : Z .R = natSyms h.r ++ Sym.mark :: XR) :
    Runs (altPost k) Z
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update Z .RET
          ((entrySyms (gRescale (h.mr + h.p_in) h.pSub (zi, zr))).reverse ++ Z .RET)) .AI XAI)
          .AR XAR) .AR' XAR') .AI' XAI') .K XK) .J XJ) .R XR)
      (fun _ => True)
      (C * (2 * wz + 12 * (h.mr + h.p_in + h.pSub) + 8) + 50 * wz +
        130 * (h.mr + h.p_in + h.pSub) +
        26 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 300 +
        (3 * bitLen (gRescale (h.mr + h.p_in) h.pSub (zi, zr)).1.natAbs +
          3 * bitLen (gRescale (h.mr + h.p_in) h.pSub (zi, zr)).2.natAbs + 3 * bitLen h.r + 23)) := by
  have e1 := rs_rescale k hok h Z r0 r1 (Sym.mark :: XAI) (Sym.mark :: XAR) zi zr wz
    (TermOK.cons rfl _) (TermOK.cons rfl _) hzi hzr hC0 hC1 hAI hAR
  set g := gRescale (h.mr + h.p_in) h.pSub (zi, zr) with hg
  set S1 := Function.update (Function.update Z .AI (intSyms g.1 ++ Sym.mark :: XAI)) .AR
    (intSyms g.2 ++ Sym.mark :: XAR) with hS1
  have e2 := runs_lift (kS k) (rs_mvIntOnly (src := AStk.AI) (dst := AStk.RET) (by decide) g.1
    (Sym.mark :: XAI) (TermOK.cons rfl _) S1 (by simp [hS1]))
  set S2 := Function.update (Function.update S1 .AI (Sym.mark :: XAI)) .RET
    ((intSyms g.1).reverse ++ S1 .RET) with hS2
  have e3 := runs_lift (kS k) (rs_push AStk.RET Sym.sep2 S2)
  set S3 := Function.update S2 .RET (Sym.sep2 :: S2 .RET) with hS3
  have e4 := runs_lift (kS k) (rs_mvIntOnly (src := AStk.AR) (dst := AStk.RET) (by decide) g.2
    (Sym.mark :: XAR) (TermOK.cons rfl _) S3 (by simp [hS3, hS2, hS1]))
  set S4 := Function.update (Function.update S3 .AR (Sym.mark :: XAR)) .RET
    ((intSyms g.2).reverse ++ S3 .RET) with hS4
  have e5 := runs_lift (kS k) (rs_push AStk.RET Sym.sep S4)
  set S5 := Function.update S4 .RET (Sym.sep :: S4 .RET) with hS5
  have e6 := runs_lift (kS k) (rs_pop AStk.AR Sym.mark XAR S5 (by simp [hS5, hS4]))
  set S6 := Function.update S5 .AR XAR with hS6
  have e7 := runs_lift (kS k) (rs_pop AStk.AI Sym.mark XAI S6 (by simp [hS6, hS5, hS4, hS3, hS2]))
  set S7 := Function.update S6 .AI XAI with hS7
  have e8 := runs_lift (kS k) (rs_pop AStk.AR' Sym.mark XAR' S7
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hAR']))
  set S8 := Function.update S7 .AR' XAR' with hS8
  have e9 := runs_lift (kS k) (rs_pop AStk.AI' Sym.mark XAI' S8
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hAI']))
  set S9 := Function.update S8 .AI' XAI' with hS9
  have e10 := runs_lift (kS k) (rs_pop AStk.K Sym.mark XK S9
    (by simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hK]))
  set S10 := Function.update S9 .K XK with hS10
  have e11 := runs_lift (kS k) (rs_pop AStk.J Sym.mark XJ S10
    (by simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hJ]))
  set S11 := Function.update S10 .J XJ with hS11
  have e12 := runs_lift (kS k) (rs_dropNat AStk.R h.r (Sym.mark :: XR) S11 (TermOK.cons rfl _)
    (by simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hR]))
  set S12 := Function.update S11 .R (Sym.mark :: XR) with hS12
  have e13 := runs_lift (kS k) (rs_pop AStk.R Sym.mark XR S12 (by simp [hS12]))
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5 (runs_seq e6
    (runs_seq e7 (runs_seq e8 (runs_seq e9 (runs_seq e10 (runs_seq e11 (runs_seq e12
      e13)))))))))))) ?_ (by omega)
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
  funext x
  cases x <;> simp [hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, entrySyms]

end Ker3

theorem closed_altPost (k : W3Kit) (hA : k.PA.Closed) (hN : k.PN.Closed) (hM : k.PM.Closed)
    (hL : k.PL.Closed) (hR : k.PR.Closed) : (altPost k).Closed := by
  have hr : (rescale k).FreeBelow 0 := closed_rescale k hA hN hM hL hR
  have hm : ∀ a b : AStk, (mvIntOnly a b).FreeBelow 0 := fun a b => closed_mvIntOnly a b
  simp [Prog.Closed, Prog.FreeBelow, altPost, kSym, freeBelow_liftRegs, hr, hm, pushC, popR,
    dropBits, dropBody, peekR]

#assert_std_axioms rs_altPost closed_altPost

end WP.W9b
