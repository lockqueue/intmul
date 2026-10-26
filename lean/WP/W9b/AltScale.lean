import WP.W9b.AltPair

/-!
# WP.W9b.AltScale — P2, the final rescale of the two accumulators

`gRescale (m_r + p_in) pSub` (`W8.gRescale_shift`). With `e = m_r + p_in` (on `SS`) and `pSub`
(on `P`): compare; if `e ≤ pSub`, shift both accumulators left by `pSub − e` (`shlS`); otherwise
round-shift them right by `e − pSub ≥ 1` (`divRoundS`). The parameters come from the header on `C0`
(`copyField 0`, `copyField 5`) and from `C1`.
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability
open IntMul (divRoundPow2 gRescale)

section Scale

variable (k : W3Kit)

/-- Comparator result `gt`. -/
def isGtR (v : KReg k) : Bool := decide (((kC k).get v).2.2 = Ordering.gt)

/-- The comparator through its lens (temporaries `E`, `F`). -/
def cmpK (x y : AStk) : Prog AStk (fun _ => Sym) (KReg k) := (cmpNum x y .E .F).liftRegs (kC k)

/-- Head: guards, `P := pSub`, `Q := m_r`, `PI := p_in`, `SS := m_r + p_in`. -/
def scaleHead : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (pushC .P .mark)) (.seq (kSym k (pushC .Q .mark)) (.seq (kSym k (pushC .PI .mark))
  (.seq (kSym k (pushC .SS .mark)) (.seq (kSym k (pushC .D .mark))
  (.seq (kSym k (copyField 0 .C0 .P .H)) (.seq (kSym k (copyField 5 .C0 .Q .H))
  (.seq (kSym k (copyBlock .C1 .PI .t)) (addN k .Q .PI .SS))))))))

/-- Branch on `SS > P`. -/
def scaleBranch : Prog AStk (fun _ => Sym) (KReg k) :=
  .ite (isGtR k)
    (.seq (subN k .SS .P .D) (.seq (divRoundS k .AI) (divRoundS k .AR)))
    (.seq (subN k .P .SS .D) (.seq (shlS k .AI) (shlS k .AR)))

/-- Tail: drop `D`, `SS`, `PI`, `Q`, `P` and their guards. -/
def scaleTail : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (dropBits .D)) (.seq (kSym k (popR .D))
  (.seq (kSym k (dropBits .SS)) (.seq (kSym k (popR .SS))
  (.seq (kSym k (dropBits .PI)) (.seq (kSym k (popR .PI))
  (.seq (kSym k (dropBits .Q)) (.seq (kSym k (popR .Q))
  (.seq (kSym k (dropBits .P)) (kSym k (popR .P))))))))))

/-- **P2 rescale.** -/
def rescale : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (scaleHead k) (.seq (.seq (cmpK k .SS .P) (scaleBranch k)) (scaleTail k))

end Scale

/-- The stacks after `scaleHead`. -/
def scaleMid (X : AStk → List Sym) (h : PreHdr) : AStk → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update X
    .P (natSyms h.pSub ++ Sym.mark :: X .P)) .Q (natSyms h.mr ++ Sym.mark :: X .Q))
    .PI (natSyms h.p_in ++ Sym.mark :: X .PI)) .SS
    (natSyms (h.mr + h.p_in) ++ Sym.mark :: X .SS)) .D (Sym.mark :: X .D)

section ScaleProofs

variable (k : W3Kit)

theorem rs_scaleHead {C : ℕ} (hok : W3Ok k C) (h : PreHdr) (X : AStk → List Sym)
    (r0 r1 : List Sym) (hC0 : X .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0)
    (hC1 : X .C1 = hdrSyms [h.p_in] ++ r1) :
    Runs (scaleHead k) X (scaleMid X h) (fun _ => True)
      (26 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 7 * bitLen h.p_in + 34 +
        C * (bitLen h.mr + bitLen h.p_in + 1)) := by
  have e1 := runs_lift (kS k) (rs_push AStk.P Sym.mark X)
  set S1 := Function.update X .P (Sym.mark :: X .P) with hS1
  have e2 := runs_lift (kS k) (rs_push AStk.Q Sym.mark S1)
  set S2 := Function.update S1 .Q (Sym.mark :: S1 .Q) with hS2
  have e3 := runs_lift (kS k) (rs_push AStk.PI Sym.mark S2)
  set S3 := Function.update S2 .PI (Sym.mark :: S2 .PI) with hS3
  have e4 := runs_lift (kS k) (rs_push AStk.SS Sym.mark S3)
  set S4 := Function.update S3 .SS (Sym.mark :: S3 .SS) with hS4
  have e5 := runs_lift (kS k) (rs_push AStk.D Sym.mark S4)
  set S5 := Function.update S4 .D (Sym.mark :: S4 .D) with hS5
  have hC0' : S5 .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0 := by
    simp [hS5, hS4, hS3, hS2, hS1, hC0]
  have e6 : Runs (kSym k (copyField 0 .C0 .P .H)) S5
      (Function.update S5 .P (natSyms h.pSub ++ S5 .P)) (fun _ => True)
      (13 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 11) :=
    runs_lift (kS k) (rs_copyField (by decide) (by decide) (by decide)
      (preTapeFields h.pSub h.m1 h.t1 h.r) 0 (by simp [preTapeFields]) r0 S5 hC0')
  set S6 := Function.update S5 .P (natSyms h.pSub ++ S5 .P) with hS6
  have hC0'' : S6 .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0 := by
    simp [hS6, hC0']
  have e7 : Runs (kSym k (copyField 5 .C0 .Q .H)) S6
      (Function.update S6 .Q (natSyms h.mr ++ S6 .Q)) (fun _ => True)
      (13 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 11) :=
    runs_lift (kS k) (rs_copyField (by decide) (by decide) (by decide)
      (preTapeFields h.pSub h.m1 h.t1 h.r) 5 (by simp [preTapeFields]) r0 S6 hC0'')
  set S7 := Function.update S6 .Q (natSyms h.mr ++ S6 .Q) with hS7
  have e8 := runs_lift (kS k) (rs_copy (src := AStk.C1) (dst := AStk.PI) (tmp := AStk.t)
    (by decide) (by decide) (by decide) h.p_in (Sym.mark :: r1) S7 (TermOK.cons rfl _)
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hC1, hdrSyms_cons, hdrSyms_nil]))
  set S8 := Function.update S7 .PI (natSyms h.p_in ++ S7 .PI) with hS8
  have e9 := rs_addN k hok.addN (x := AStk.Q) (y := AStk.PI) (z := AStk.SS)
    (embL3_inj k.hN (by decide) (by decide) (by decide) trivial trivial trivial) h.mr h.p_in
    (Sym.mark :: X .Q) (Sym.mark :: X .PI) S8 (TermOK.cons rfl _) (TermOK.cons rfl _)
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5 (runs_seq e6
    (runs_seq e7 (runs_seq e8 e9)))))))) ?_ (by omega)
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9
  funext x
  cases x <;> simp [scaleMid, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]

theorem rs_cmpK (x y : AStk) (hxy : x ≠ y) (hxE : x ≠ .E) (hxF : x ≠ .F) (hyE : y ≠ .E)
    (hyF : y ≠ .F) (a b : ℕ) (ra rb : List Sym) (S : AStk → List Sym) (hra : TermOK ra)
    (hrb : TermOK rb) (hx : S x = natSyms a ++ ra) (hy : S y = natSyms b ++ rb) :
    Runs (cmpK k x y) S S (fun v => ((kC k).get v).2.2 = Lib.ordOf a b) (12 * bitLen b + 15) := by
  refine runs_liftMacro (Qr := fun r : CReg => r.2.2 = Lib.ordOf a b) (kC k) (fun v =>
    ⟨_, _, cmpNum_eval hxy hxE hxF hyE hyF (by decide) v (encodeNat a) (encodeNat b) ra rb S hra
      hrb hx hy, ?_, ?_⟩)
  · show cmpAll .eq (encodeNat a) (encodeNat b) = Lib.ordOf a b
    rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
      bitsVal_encodeNat]
  · have := min_le_right (encodeNat a).length (encodeNat b).length
    simp only [bitLen]
    omega

theorem rs_scaleLE {C : ℕ} (hok : W3Ok k C) (Y : AStk → List Sym) (e q : ℕ) (zi zr : ℤ)
    (ssb pb db AIb ARb : List Sym) (hssb : TermOK ssb) (hpb : TermOK pb) (hdb : TermOK db)
    (hAIb : TermOK AIb) (hARb : TermOK ARb) (hle : e ≤ q)
    (hSS : Y .SS = natSyms e ++ ssb) (hP : Y .P = natSyms q ++ pb) (hD : Y .D = db)
    (hAI : Y .AI = intSyms zi ++ AIb) (hAR : Y .AR = intSyms zr ++ ARb) :
    Runs (.seq (cmpK k .SS .P) (scaleBranch k)) Y
      (Function.update (Function.update (Function.update Y .D (natSyms (q - e) ++ db)) .AI
        (intSyms (zi * ((2 ^ (q - e) : ℕ) : ℤ)) ++ AIb)) .AR
        (intSyms (zr * ((2 ^ (q - e) : ℕ) : ℤ)) ++ ARb))
      (fun _ => True)
      (12 * bitLen q + 24 + C * (bitLen q + bitLen e + 1) +
        2 * (C * (q - e + bitLen (q - e) + 1))) := by
  have hc : Runs (cmpK k .SS .P) Y Y (fun v => isGtR k v = false) (12 * bitLen q + 15) :=
    runs_mono (rs_cmpK k .SS .P (by decide) (by decide) (by decide) (by decide) (by decide) e q
      ssb pb Y hssb hpb hSS hP)
      (fun v (hv : ((kC k).get v).2.2 = Lib.ordOf e q) => by
        simp only [isGtR, hv, Lib.ordOf]
        split_ifs <;> first | rfl | omega) le_rfl
  have f1 := rs_subN k hok.subN (x := AStk.P) (y := AStk.SS) (z := AStk.D)
    (embL3_inj k.hM (by decide) (by decide) (by decide) trivial trivial trivial) q e pb ssb Y
    hpb hssb hle hP hSS
  set T1 := Function.update Y .D (natSyms (q - e) ++ Y .D) with hT1
  have f2 := rs_shlS k hok (z := AStk.AI) (Or.inl rfl) zi (q - e) AIb db hAIb hdb T1
    (by simp [hT1, hAI]) (by simp [hT1, hD])
  set T2 := Function.update T1 .AI (intSyms (zi * ((2 ^ (q - e) : ℕ) : ℤ)) ++ AIb) with hT2
  have f3 := rs_shlS k hok (z := AStk.AR) (Or.inr rfl) zr (q - e) ARb db hARb hdb T2
    (by simp [hT2, hT1, hAR]) (by simp [hT2, hT1, hD])
  refine runs_post (runs_ite_false hc (runs_seq f1 (runs_seq f2 f3))) ?_ (by omega)
  simp only [hT2, hT1, hD]

theorem rs_scaleGT {C : ℕ} (hok : W3Ok k C) (Y : AStk → List Sym) (e q : ℕ) (zi zr : ℤ)
    (ssb pb db AIb ARb : List Sym) (hssb : TermOK ssb) (hpb : TermOK pb) (hdb : TermOK db)
    (hAIb : TermOK AIb) (hARb : TermOK ARb) (hgt : q < e)
    (hSS : Y .SS = natSyms e ++ ssb) (hP : Y .P = natSyms q ++ pb) (hD : Y .D = db)
    (hAI : Y .AI = intSyms zi ++ AIb) (hAR : Y .AR = intSyms zr ++ ARb) :
    Runs (.seq (cmpK k .SS .P) (scaleBranch k)) Y
      (Function.update (Function.update (Function.update Y .D (natSyms (e - q) ++ db)) .AI
        (intSyms (divRoundPow2 zi (e - q)) ++ AIb)) .AR (intSyms (divRoundPow2 zr (e - q)) ++ ARb))
      (fun _ => True)
      (12 * bitLen q + 216 + C * (bitLen e + bitLen q + 1) +
        C * (bitLen zi.natAbs + 5 * (e - q) + 3) + C * (bitLen zr.natAbs + 5 * (e - q) + 3) +
        25 * bitLen zi.natAbs + 25 * bitLen zr.natAbs + 90 * (e - q)) := by
  have hc : Runs (cmpK k .SS .P) Y Y (fun v => isGtR k v = true) (12 * bitLen q + 15) :=
    runs_mono (rs_cmpK k .SS .P (by decide) (by decide) (by decide) (by decide) (by decide) e q
      ssb pb Y hssb hpb hSS hP)
      (fun v (hv : ((kC k).get v).2.2 = Lib.ordOf e q) => by
        simp only [isGtR, hv, Lib.ordOf]
        split_ifs <;> first | rfl | omega) le_rfl
  have f1 := rs_subN k hok.subN (x := AStk.SS) (y := AStk.P) (z := AStk.D)
    (embL3_inj k.hM (by decide) (by decide) (by decide) trivial trivial trivial) e q ssb pb Y
    hssb hpb (le_of_lt hgt) hSS hP
  set T1 := Function.update Y .D (natSyms (e - q) ++ Y .D) with hT1
  have f2 := rs_divRoundS k hok (z := AStk.AI) (Or.inl rfl) zi (e - q) (by omega) AIb db hAIb hdb
    T1 (by simp [hT1, hAI]) (by simp [hT1, hD])
  set T2 := Function.update T1 .AI (intSyms (divRoundPow2 zi (e - q)) ++ AIb) with hT2
  have f3 := rs_divRoundS k hok (z := AStk.AR) (Or.inr rfl) zr (e - q) (by omega) ARb db hARb hdb
    T2 (by simp [hT2, hT1, hAR]) (by simp [hT2, hT1, hD])
  refine runs_post (runs_ite_true hc (runs_seq f1 (runs_seq f2 f3))) ?_ (by omega)
  simp only [hT2, hT1, hD]

theorem rs_scaleTail (Y : AStk → List Sym) (dv e b m q : ℕ) (dD dS dPI dQ dP : List Sym)
    (hD : Y .D = natSyms dv ++ Sym.mark :: dD) (hSS : Y .SS = natSyms e ++ Sym.mark :: dS)
    (hPI : Y .PI = natSyms b ++ Sym.mark :: dPI) (hQ : Y .Q = natSyms m ++ Sym.mark :: dQ)
    (hP : Y .P = natSyms q ++ Sym.mark :: dP) :
    Runs (scaleTail k) Y
      (Function.update (Function.update (Function.update (Function.update (Function.update Y
        .D dD) .SS dS) .PI dPI) .Q dQ) .P dP) (fun _ => True)
      (3 * (bitLen dv + bitLen e + bitLen b + bitLen m + bitLen q) + 15) := by
  have e1 := runs_lift (kS k) (rs_dropNat AStk.D dv (Sym.mark :: dD) Y (TermOK.cons rfl _) hD)
  set S1 := Function.update Y .D (Sym.mark :: dD) with hS1
  have e2 := runs_lift (kS k) (rs_pop AStk.D Sym.mark dD S1 (by simp [hS1]))
  set S2 := Function.update S1 .D dD with hS2
  have e3 := runs_lift (kS k) (rs_dropNat AStk.SS e (Sym.mark :: dS) S2 (TermOK.cons rfl _)
    (by simp [hS2, hS1, hSS]))
  set S3 := Function.update S2 .SS (Sym.mark :: dS) with hS3
  have e4 := runs_lift (kS k) (rs_pop AStk.SS Sym.mark dS S3 (by simp [hS3]))
  set S4 := Function.update S3 .SS dS with hS4
  have e5 := runs_lift (kS k) (rs_dropNat AStk.PI b (Sym.mark :: dPI) S4 (TermOK.cons rfl _)
    (by simp [hS4, hS3, hS2, hS1, hPI]))
  set S5 := Function.update S4 .PI (Sym.mark :: dPI) with hS5
  have e6 := runs_lift (kS k) (rs_pop AStk.PI Sym.mark dPI S5 (by simp [hS5]))
  set S6 := Function.update S5 .PI dPI with hS6
  have e7 := runs_lift (kS k) (rs_dropNat AStk.Q m (Sym.mark :: dQ) S6 (TermOK.cons rfl _)
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1, hQ]))
  set S7 := Function.update S6 .Q (Sym.mark :: dQ) with hS7
  have e8 := runs_lift (kS k) (rs_pop AStk.Q Sym.mark dQ S7 (by simp [hS7]))
  set S8 := Function.update S7 .Q dQ with hS8
  have e9 := runs_lift (kS k) (rs_dropNat AStk.P q (Sym.mark :: dP) S8 (TermOK.cons rfl _)
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hP]))
  set S9 := Function.update S8 .P (Sym.mark :: dP) with hS9
  have e10 := runs_lift (kS k) (rs_pop AStk.P Sym.mark dP S9 (by simp [hS9]))
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5 (runs_seq e6
    (runs_seq e7 (runs_seq e8 (runs_seq e9 e10))))))))) ?_ (by omega)
  simp only [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_idem]

end ScaleProofs

#assert_std_axioms rs_scaleHead rs_cmpK rs_scaleLE rs_scaleGT rs_scaleTail

end WP.W9b
