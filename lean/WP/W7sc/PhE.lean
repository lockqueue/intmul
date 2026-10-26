import WP.W7sc.PhC

/-!
# WP.W7sc.PhE — phases `phE0` (sine series, `im`), the sign step, `phF` (record, drops), `phZ`
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

section Phases

variable {X : KX} {I : KI}

theorem phE0_spec (hX : X.OK I) (hE : I.SpecX X.C) {Cs : ℕ} (hss : SpecSer SK.sin I.ss Cs)
    (S : HL → List Sym) (q num den P w : ℕ) (hden : 0 < den) (hV : X.V = 2 * w)
    (hw : Wd q P num den w) :
    HT [] (stD S q P num den) (phE0 I) (stE0 S q P num den)
      (14 * X.U + Cs * (q + 2 + 25 + 1) * (w + 2) ^ 2) := by
  have hp := hw.par
  have hdt : 0 < dtv q den := Nat.mul_pos hden (Nat.two_pow_pos _)
  have hds : 0 < dsq q den := Nat.mul_pos hdt hdt
  unfold phE0 stD stE0
  apply HT.mono
  · refine HT.seq ((HT.ucpI hX (.inr 3) (.inr 2) (by decide) (by norm_num) _ _ _ (termOK_mark _)
        (by rw [cSt_3]) (vC hV hw.nt)).of_eq (by rw [cSt_2, cSt_upd2]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 3) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_3])
        (vC hV hw.nt)).of_eq (cSt_upd3 ..) le_rfl) <| HT.seq
      ((HT.ushlI hX hE (.inr 2) (.inr 11) (by decide) (by norm_num) _ _
        (q + 2 + 2 * (q + 2 + 25) + 22) _ _ (termOK_mark _) (termOK_mark _) (by rw [cSt_2])
        (by rw [cSt_11]) (vS hV (by omega))).of_eq (cSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.udv hX (.inr 2) (.inr 6) (.inr 4) (by decide) (by norm_num) _ _ (dtv q den) _ _ hdt
        (termOK_mark _) (termOK_mark _) (by rw [cSt_2]) (by rw [cSt_6]) (vZ hV hw.ns)
        (vB hV hw.dt)).of_eq (by rw [cSt_4, cSt_upd4]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 2) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_2])
        (vZ hV hw.ns)).of_eq (cSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.uss hss (.inr 4) (.inr 5) (.inr 8) (.inr 9) (.inr 7) (by decide) (by norm_num) _ w
        _ _ _ _ _ _ _ _ hds (by omega) hw.rs (termOK_mark _) (termOK_mark _) (termOK_mark _)
        (termOK_mark _) (by rw [cSt_4]) (by rw [cSt_5]) (by rw [cSt_8]) (by rw [cSt_9])).of_eq
        (by rw [cSt_7, cSt_upd7]) le_rfl) <| HT.seq
      ((HT.ushlI hX hE (.inr 7) (.inr 10) (by decide) (by norm_num) _ _ (q + 2) _ _
        (termOK_mark _) (termOK_mark _) (by rw [cSt_7]) (by rw [cSt_10])
        (vS hV (by omega))).of_eq (cSt_upd7 ..) le_rfl)
      ((HT.udv hX (.inr 7) (.inr 12) (.inr 1) (by decide) (by norm_num) _ _
        (2 ^ (q + 2 + 2 * (q + 2 + 25) + 22)) _ _ (Nat.two_pow_pos _) (termOK_mark _)
        (termOK_mark _) (by rw [cSt_7]) (by rw [cSt_12]) (vZ hV hw.sn) (vB hV hw.pw)).of_eq ?_
        le_rfl)
    rw [cSt_1, cSt_upd1]
  · have := KX.eight_le hX
    omega

theorem neg_spec (hX : X.OK I) (hE : I.SpecX X.C) (S : HL → List Sym) (q num den P : ℕ)
    (neg : Bool) :
    HT [] (stE0 S q P num den) (negStep I neg) (stE S q P num den neg) X.U := by
  unfold stE0 stE
  cases neg
  · refine (HT.skipL _).of_eq ?_ (by have := KX.eight_le hX; omega)
    rw [show imV q P num den false = imP q P num den from if_neg Bool.false_ne_true]
  · refine (HT.ung hX hE (.inr 1) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_1])).of_eq ?_
      le_rfl
    rw [cSt_upd1, show imV q P num den true = -imP q P num den from if_pos rfl]

theorem phF_spec (hX : X.OK I) (S : HL → List Sym) (q num den P w : ℕ) (neg : Bool)
    (hden : 0 < den) (hV : X.V = 2 * w) (hw : Wd q P num den w) :
    HT [] (stE S q P num den neg) (phF I) (stF S q P num den neg) (19 * X.U) := by
  have hp := hw.par
  unfold phF stE stF
  apply HT.mono
  · refine HT.seq ((HT.pushS (.inl 3) .sep _ []).of_eq (by rw [cSt_d, cSt_updd]) le_rfl) <| HT.seq
      ((HT.umvI hX (.inr 1) (.inl 3) (by decide) (by norm_num) _ _ _ (termOK_mark _)
        (by rw [cSt_1]) (vZ hV (hw.im_le neg))).of_eq (by rw [cSt_d, cSt_updd, cSt_upd1])
        le_rfl) <| HT.seq
      ((HT.umvI hX (.inr 14) (.inl 3) (by decide) (by norm_num) _ _ _ (termOK_mark _)
        (by rw [cSt_14]) (vZ hV hw.re_le)).of_eq (by rw [cSt_d, cSt_updd, cSt_upd14])
        le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 4) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_4])
        (vZ hV (hw.sa0_le hden))).of_eq (cSt_upd4 ..) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 5) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_5])
        (vZ2 hV hw.nsq_le)).of_eq (cSt_upd5 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 6) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_6])
        (vB hV hw.dt)).of_eq (cSt_upd6 ..) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 7) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_7])
        (vZ hV hw.sn)).of_eq (cSt_upd7 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 8) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_8])
        (vB2 hV hw.dsq_le)).of_eq (cSt_upd8 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 9) (by norm_num) _ (q + 2 + 25) _ (termOK_mark _) (by rw [cSt_9])
        (vN hV (by omega))).of_eq (cSt_upd9 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 10) (by norm_num) _ (q + 2) _ (termOK_mark _) (by rw [cSt_10])
        (vN hV (by omega))).of_eq (cSt_upd10 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 11) (by norm_num) _ (q + 2 + 2 * (q + 2 + 25) + 22) _ (termOK_mark _)
        (by rw [cSt_11]) (vN hV (by omega))).of_eq (cSt_upd11 ..) le_rfl)
      ((HT.udr hX (.inr 12) (by norm_num) _ (2 ^ (q + 2 + 2 * (q + 2 + 25) + 22)) _
        (termOK_mark _) (by rw [cSt_12]) (vB hV hw.pw)).of_eq ?_ le_rfl)
    rw [cSt_upd12]
  · have := KX.eight_le hX
    omega

theorem phZ_spec (S : HL → List Sym) (vd : List Sym) :
    HT [] (cSt S (.mark :: S (.inr 0)) (.mark :: S (.inr 1)) (.mark :: S (.inr 2))
        (.mark :: S (.inr 3)) (.mark :: S (.inr 4)) (.mark :: S (.inr 5)) (.mark :: S (.inr 6))
        (.mark :: S (.inr 7)) (.mark :: S (.inr 8)) (.mark :: S (.inr 9)) (.mark :: S (.inr 10))
        (.mark :: S (.inr 11)) (.mark :: S (.inr 12)) (.mark :: S (.inr 13))
        (.mark :: S (.inr 14)) (.mark :: S (.inr 15)) vd) (phZ I)
      (Function.update S (.inl 3) vd) 16 := by
  unfold phZ
  apply HT.mono
  · refine HT.seq ((HT.popS (.inr 0) _ Sym.mark (S (.inr 0)) (by rw [cSt_0]) []).of_eq (cSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 1) _ Sym.mark (S (.inr 1)) (by rw [cSt_1]) []).of_eq (cSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 2) _ Sym.mark (S (.inr 2)) (by rw [cSt_2]) []).of_eq (cSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 3) _ Sym.mark (S (.inr 3)) (by rw [cSt_3]) []).of_eq (cSt_upd3 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 4) _ Sym.mark (S (.inr 4)) (by rw [cSt_4]) []).of_eq (cSt_upd4 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 5) _ Sym.mark (S (.inr 5)) (by rw [cSt_5]) []).of_eq (cSt_upd5 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 6) _ Sym.mark (S (.inr 6)) (by rw [cSt_6]) []).of_eq (cSt_upd6 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 7) _ Sym.mark (S (.inr 7)) (by rw [cSt_7]) []).of_eq (cSt_upd7 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 8) _ Sym.mark (S (.inr 8)) (by rw [cSt_8]) []).of_eq (cSt_upd8 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 9) _ Sym.mark (S (.inr 9)) (by rw [cSt_9]) []).of_eq (cSt_upd9 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 10) _ Sym.mark (S (.inr 10)) (by rw [cSt_10]) []).of_eq (cSt_upd10 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 11) _ Sym.mark (S (.inr 11)) (by rw [cSt_11]) []).of_eq (cSt_upd11 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 12) _ Sym.mark (S (.inr 12)) (by rw [cSt_12]) []).of_eq (cSt_upd12 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 13) _ Sym.mark (S (.inr 13)) (by rw [cSt_13]) []).of_eq (cSt_upd13 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 14) _ Sym.mark (S (.inr 14)) (by rw [cSt_14]) []).of_eq (cSt_upd14 ..) le_rfl)
      ((HT.popS (.inr 15) _ Sym.mark (S (.inr 15)) (by rw [cSt_15]) []).of_eq (by rw [cSt_upd15, cSt_final]) le_rfl)
  · norm_num

end Phases

#assert_std_axioms phE0_spec neg_spec phF_spec phZ_spec

end WP.W7sc
