import WP.W9b.AltKer1

/-!
# WP.W9b.AltKer2 — P2 kernel, part 2: setup and skip (`altPre`), pair loop and restore (`altMid`)
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

section Ker2

variable (k : W3Kit)

/-- Setup and skip: guards, `J := t1/2`, `R := r`, then the first `t1/2` rows move `W0 → T`. -/
def altPre : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (pushC .T .mark)) (.seq (kSym k (pushC .J .mark)) (.seq (kSym k (pushC .K .mark))
  (.seq (kSym k (pushC .R .mark)) (.seq (kSym k (pushC .AR .mark))
  (.seq (kSym k (pushC .AR' .mark)) (.seq (kSym k (pushC .AI .mark))
  (.seq (kSym k (pushC .AI' .mark)) (.seq (kSym k (copyField 2 .C0 .J .H))
  (.seq (kSym k (popR .J)) (.seq (kSym k (copyField 3 .C0 .R .H)) (skipRows k)))))))))))

/-- Pair loop, then all entries `T → W0` (`T`'s guard is consumed). -/
def altMid : Prog AStk (fun _ => Sym) (KReg k) := .seq (pairLoop k) (kSym k (mvG .T .W0))

end Ker2

/-- The stacks after `altPre`. -/
def preOut (X : AStk → List Sym) (r : ℕ) (rows : List (Array (ℤ × ℤ)))
    (restE : List (ℤ × ℤ)) : AStk → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update X .W0 (blkE restE)) .T
    ((blkE (rows.flatMap Array.toList)).reverse ++ Sym.mark :: X .T)) .J (Sym.mark :: X .J))
    .K (Sym.mark :: X .K)) .R (natSyms r ++ Sym.mark :: X .R)) .AR (Sym.mark :: X .AR))
    .AR' (Sym.mark :: X .AR')) .AI (Sym.mark :: X .AI)) .AI' (Sym.mark :: X .AI')

section Ker2Proofs

variable (k : W3Kit)

theorem rs_altPre (h : PreHdr) (X : AStk → List Sym) (r0 : List Sym)
    (rows : List (Array (ℤ × ℤ))) (restE : List (ℤ × ℤ)) (ht1 : h.t1 ≠ 0)
    (hlen : rows.length = h.t1 / 2) (hrows : ∀ row ∈ rows, row.size = h.r)
    (hC0 : X .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0)
    (hW : X .W0 = blkE (rows.flatMap Array.toList ++ restE)) :
    Runs (altPre k) X (preOut X h.r rows restE) (fun _ => True)
      (26 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 31 +
        (3 * (blkE (rows.flatMap Array.toList)).length +
          rows.length * (7 * bitLen h.r + 9 + decSum h.r + 2 * h.r) + decSum rows.length +
          2 * rows.length + 2)) := by
  have e1 := runs_lift (kS k) (rs_push AStk.T Sym.mark X)
  set S1 := Function.update X .T (Sym.mark :: X .T) with hS1
  have e2 := runs_lift (kS k) (rs_push AStk.J Sym.mark S1)
  set S2 := Function.update S1 .J (Sym.mark :: S1 .J) with hS2
  have e3 := runs_lift (kS k) (rs_push AStk.K Sym.mark S2)
  set S3 := Function.update S2 .K (Sym.mark :: S2 .K) with hS3
  have e4 := runs_lift (kS k) (rs_push AStk.R Sym.mark S3)
  set S4 := Function.update S3 .R (Sym.mark :: S3 .R) with hS4
  have e5 := runs_lift (kS k) (rs_push AStk.AR Sym.mark S4)
  set S5 := Function.update S4 .AR (Sym.mark :: S4 .AR) with hS5
  have e6 := runs_lift (kS k) (rs_push AStk.AR' Sym.mark S5)
  set S6 := Function.update S5 .AR' (Sym.mark :: S5 .AR') with hS6
  have e7 := runs_lift (kS k) (rs_push AStk.AI Sym.mark S6)
  set S7 := Function.update S6 .AI (Sym.mark :: S6 .AI) with hS7
  have e8 := runs_lift (kS k) (rs_push AStk.AI' Sym.mark S7)
  set S8 := Function.update S7 .AI' (Sym.mark :: S7 .AI') with hS8
  have hC0' : S8 .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0 := by
    simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hC0]
  have e9 : Runs (kSym k (copyField 2 .C0 .J .H)) S8
      (Function.update S8 .J (natSyms h.t1 ++ S8 .J)) (fun _ => True)
      (13 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 11) :=
    runs_lift (kS k) (rs_copyField (by decide) (by decide) (by decide)
      (preTapeFields h.pSub h.m1 h.t1 h.r) 2 (by simp [preTapeFields]) r0 S8 hC0')
  set S9 := Function.update S8 .J (natSyms h.t1 ++ S8 .J) with hS9
  have e10 := runs_lift (kS k) (rs_halve AStk.J h.t1 ht1 (S8 .J) S9
    (by rw [hS9, Function.update_self]))
  set S10 := Function.update S9 .J (natSyms (h.t1 / 2) ++ S8 .J) with hS10
  have hC0'' : S10 .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0 := by
    simp [hS10, hS9, hC0']
  have e11 : Runs (kSym k (copyField 3 .C0 .R .H)) S10
      (Function.update S10 .R (natSyms h.r ++ S10 .R)) (fun _ => True)
      (13 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 11) :=
    runs_lift (kS k) (rs_copyField (by decide) (by decide) (by decide)
      (preTapeFields h.pSub h.m1 h.t1 h.r) 3 (by simp [preTapeFields]) r0 S10 hC0'')
  set S11 := Function.update S10 .R (natSyms h.r ++ S10 .R) with hS11
  have e12 := rs_skipRows k S11 h.r (Sym.mark :: X .R) (Sym.mark :: X .K) (Sym.mark :: X .J)
    (Sym.mark :: X .T) rows restE (TermOK.cons rfl _) (TermOK.cons rfl _) (TermOK.cons rfl _)
    hrows (by simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hlen])
    (by simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hW])
    (by simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5 (runs_seq e6
    (runs_seq e7 (runs_seq e8 (runs_seq e9 (runs_seq e10 (runs_seq e11 e12))))))))))) ?_
    (by omega)
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  funext x
  cases x <;> simp [preOut, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, natSyms_zero]

theorem rs_altMid {C : ℕ} (hok : W3Ok k C) (Y : AStk → List Sym) (r mr w : ℕ)
    (rb kb XT ARb AIb : List Sym) (skipped row restE : List (ℤ × ℤ)) (hrb : TermOK rb)
    (hkb : TermOK kb) (hARb : TermOK ARb) (hAIb : TermOK AIb) (hr : r = 2 ^ mr) (hmr : 1 ≤ mr)
    (hlen : row.length = r) (hroww : ∀ z ∈ row, EntryW w z)
    (hR : Y .R = natSyms r ++ rb) (hK : Y .K = kb) (hW : Y .W0 = blkE (row ++ restE))
    (hT : Y .T = (blkE skipped).reverse ++ Sym.mark :: XT) (hAR : Y .AR = ARb)
    (hAI : Y .AI = AIb) (hAR' : TermOK (Y .AR')) (hAI' : TermOK (Y .AI')) :
    Runs (altMid k) Y
      (Function.update (Function.update (Function.update (Function.update Y
        .W0 (blkE (skipped ++ row ++ restE))) .T XT) .AR (intSyms (accRe (pairUp row)) ++ ARb))
        .AI (intSyms (accIm (pairUp row)) ++ AIb))
      (fun _ => True)
      (7 * bitLen r + 10 + (r / 2 * pairCost C w mr + decSum (r / 2) + 2 * (r / 2) + 2) +
        (3 * ((blkE row).length + (blkE skipped).length) + 2)) := by
  have e1 := rs_pairLoop k hok Y r mr w rb kb ((blkE skipped).reverse ++ Sym.mark :: XT) ARb AIb
    row restE hrb hkb hARb hAIb hr hmr hlen hroww hR hK hW hT hAR hAI hAR' hAI'
  have hnm : ∀ x ∈ (blkE row).reverse ++ (blkE skipped).reverse, x ≠ Sym.mark := by
    intro x hx
    simp only [List.mem_append, List.mem_reverse] at hx
    rcases hx with hx | hx
    · exact mem_blkE_ne_mark _ x hx
    · exact mem_blkE_ne_mark _ x hx
  refine runs_post (runs_seq e1 (runs_lift (kS k) (rs_mvG (src := AStk.T) (dst := AStk.W0)
    (by decide) ((blkE row).reverse ++ (blkE skipped).reverse) XT _ hnm (by simp)))) ?_ ?_
  · clear e1
    funext x
    cases x <;> simp [blkE_append]
  · simp only [List.length_append, List.length_reverse]
    omega

end Ker2Proofs

theorem closed_altPre (k : W3Kit) : (altPre k).Closed := by
  have h2 : (copyField 2 AStk.C0 AStk.J AStk.H).FreeBelow 0 := closed_copyField _ _ _ _
  have h3 : (copyField 3 AStk.C0 AStk.R AStk.H).FreeBelow 0 := closed_copyField _ _ _ _
  have hs : (skipRows k).FreeBelow 0 := closed_skipRows k
  simp [Prog.Closed, Prog.FreeBelow, altPre, kSym, freeBelow_liftRegs, h2, h3, hs, pushC, popR]

theorem closed_altMid (k : W3Kit) (hA : k.PA.Closed) (hS : k.PS.Closed) : (altMid k).Closed :=
  ⟨closed_pairLoop k hA hS, closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, mvG, mvGBody,
    popR, pushR])⟩

#assert_std_axioms rs_altPre rs_altMid closed_altPre closed_altMid

end WP.W9b
