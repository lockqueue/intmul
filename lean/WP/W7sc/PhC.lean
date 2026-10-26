import WP.W7sc.PhA

/-!
# WP.W7sc.PhC — phases `phC` (`N`, `Bint`, `2^Bint`) and `phD` (cosine series, `re`)
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

section Phases

variable {X : KX} {I : KI}

theorem phC_spec (hX : X.OK I) (hE : I.SpecX X.C) (S : HL → List Sym) (q num den P w : ℕ)
    (hV : X.V = 2 * w) (hw : Wd q P num den w) :
    HT [] (stB S q P num den) (phC I) (stC S q P num den) (56 * X.U) := by
  have hp := hw.par
  have hbi : q + 2 + (q + 2 + 25 + (q + 2 + 25)) + 22 = q + 2 + 2 * (q + 2 + 25) + 22 := by omega
  unfold phC stB stC
  apply HT.mono
  · refine HT.seq ((HT.ucp hX (.inr 10) (.inr 9) (by decide) (by norm_num) _ (q + 2) _
        (termOK_mark _) (by rw [cSt_10]) (vN hV (by omega))).of_eq (by rw [cSt_9, cSt_upd9])
        le_rfl) <| HT.seq
      ((HT.uincN hX (.inr 9) (by norm_num) (.mark :: S (.inr 9)) (termOK_mark _) 25 (q + 2) _
        (by rw [cSt_9]) (vN hV (by omega))).of_eq (cSt_upd9 ..) le_rfl) <| HT.seq
      ((HT.ucp hX (.inr 9) (.inr 15) (by decide) (by norm_num) _ (q + 2 + 25) _ (termOK_mark _)
        (by rw [cSt_9]) (vN hV (by omega))).of_eq (by rw [cSt_15, cSt_upd15]) le_rfl) <| HT.seq
      ((HT.uad hX hE (.inr 9) (.inr 15) (.inr 12) (by decide) (by norm_num) _ (q + 2 + 25)
        (q + 2 + 25) _ _ (termOK_mark _) (termOK_mark _) (by rw [cSt_9]) (by rw [cSt_15])
        (vN hV (by omega)) (vN hV (by omega))).of_eq (by rw [cSt_12, cSt_upd12]) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 15) (by norm_num) _ (q + 2 + 25) _ (termOK_mark _) (by rw [cSt_15])
        (vN hV (by omega))).of_eq (cSt_upd15 ..) le_rfl) <| HT.seq
      ((HT.uad hX hE (.inr 10) (.inr 12) (.inr 11) (by decide) (by norm_num) _ (q + 2)
        (q + 2 + 25 + (q + 2 + 25)) _ _ (termOK_mark _) (termOK_mark _) (by rw [cSt_10])
        (by rw [cSt_12]) (vN hV (by omega)) (vN hV (by omega))).of_eq
        (by rw [cSt_11, cSt_upd11]) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 12) (by norm_num) _ (q + 2 + 25 + (q + 2 + 25)) _ (termOK_mark _)
        (by rw [cSt_12]) (vN hV (by omega))).of_eq (cSt_upd12 ..) le_rfl) <| HT.seq
      ((HT.uincN hX (.inr 11) (by norm_num) (.mark :: S (.inr 11)) (termOK_mark _) 22
        (q + 2 + (q + 2 + 25 + (q + 2 + 25))) _ (by rw [cSt_11]) (vN hV (by omega))).of_eq
        (by rw [cSt_upd11, hbi]) le_rfl) <| HT.seq
      ((HT.upushNat hX (.inr 12) 1 _ (vN hV (by omega))).of_eq (by rw [cSt_12, cSt_upd12])
        le_rfl) <| HT.seq
      ((HT.usv hX hE (.inr 12) (.inr 11) (by decide) (by norm_num) _ 1
        (q + 2 + 2 * (q + 2 + 25) + 22) _ _ (termOK_mark _) (termOK_mark _) (by rw [cSt_12])
        (by rw [cSt_11]) (vS hV (by omega))).of_eq (by rw [cSt_upd12, Nat.one_mul]) le_rfl)
      ((HT.pushS (.inr 12) .pos _ []).of_eq ?_ le_rfl)
    rw [cSt_12, cSt_upd12, intSyms_natCast']
  · have := KX.eight_le hX
    omega

theorem phD_spec (hX : X.OK I) (hE : I.SpecX X.C) {Cs : ℕ} (hsc : SpecSer SK.cos I.sc Cs)
    (S : HL → List Sym) (q num den P w : ℕ) (hden : 0 < den) (hV : X.V = 2 * w)
    (hw : Wd q P num den w) :
    HT [] (stC S q P num den) (phD I) (stD S q P num den)
      (6 * X.U + Cs * (q + 2 + 25 + 1) * (w + 2) ^ 2) := by
  have hp := hw.par
  have hdt : 0 < dtv q den := Nat.mul_pos hden (Nat.two_pow_pos _)
  have hds : 0 < dsq q den := Nat.mul_pos hdt hdt
  unfold phD stC stD
  apply HT.mono
  · refine HT.seq ((HT.usc hsc (.inr 12) (.inr 5) (.inr 8) (.inr 9) (.inr 13) (by decide)
        (by norm_num) _ w _ _ _ _ _ _ _ _ hds (by omega) hw.rc (termOK_mark _) (termOK_mark _)
        (termOK_mark _) (termOK_mark _) (by rw [cSt_12]) (by rw [cSt_5]) (by rw [cSt_8])
        (by rw [cSt_9])).of_eq (by rw [cSt_13, cSt_upd13]) le_rfl) <| HT.seq
      ((HT.popS (.inr 12) _ Sym.pos
        (natSyms (2 ^ (q + 2 + 2 * (q + 2 + 25) + 22)) ++ .mark :: S (.inr 12))
        (by simp only [cSt_12, intSyms_natCast, List.cons_append]) []).of_eq (cSt_upd12 ..)
        le_rfl) <| HT.seq
      ((HT.ushlI hX hE (.inr 13) (.inr 10) (by decide) (by norm_num) _ _ (q + 2) _ _
        (termOK_mark _) (termOK_mark _) (by rw [cSt_13]) (by rw [cSt_10])
        (vS hV (by omega))).of_eq (cSt_upd13 ..) le_rfl) <| HT.seq
      ((HT.udv hX (.inr 13) (.inr 12) (.inr 14) (by decide) (by norm_num) _ _
        (2 ^ (q + 2 + 2 * (q + 2 + 25) + 22)) _ _ (Nat.two_pow_pos _) (termOK_mark _)
        (termOK_mark _) (by rw [cSt_13]) (by rw [cSt_12]) (vZ hV hw.cs) (vB hV hw.pw)).of_eq
        (by rw [cSt_14, cSt_upd14]) le_rfl)
      ((HT.udrI hX (.inr 13) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_13])
        (vZ hV hw.cs)).of_eq ?_ le_rfl)
    rw [cSt_upd13]
  · have := KX.eight_le hX
    omega

end Phases

#assert_std_axioms phC_spec phD_spec

end WP.W7sc
