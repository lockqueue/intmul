import WP.W7sc.Prog
import WP.W7sc.Math

/-!
# WP.W7sc.PhA — sizes, the phase states, and phases `phM`, `phA`, `phB`

Every step is one call rule of `WP.W7k3.Rules` / `WP.W7k3.Helpers` (cost a multiple of the unit
`X.U`, operand sizes `≤ X.V = 2·w`) or a raw push/pop (cost 1), chained with `HT.seq` through the
explicit host states `cSt` (W7k1's style).
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

/-! ## Size side conditions (`X.V = 2·w`) -/

section Sizes

variable {X : KX} {w : ℕ}

theorem vN {x : ℕ} (hV : X.V = 2 * w) (h : x ≤ w) : bitLen x ≤ X.V := by
  have := bitLen_le_self x
  omega

theorem vB {x : ℕ} (hV : X.V = 2 * w) (h : bitLen x ≤ w) : bitLen x ≤ X.V := by omega

theorem vB2 {x : ℕ} (hV : X.V = 2 * w) (h : bitLen x ≤ 2 * w) : bitLen x ≤ X.V := by omega

theorem vC {n : ℕ} (hV : X.V = 2 * w) (h : bitLen n ≤ w) : bitLen ((n : ℤ)).natAbs ≤ X.V := by
  rw [Int.natAbs_natCast]
  omega

theorem vZ {z : ℤ} (hV : X.V = 2 * w) (h : bitLen z.natAbs ≤ w) : bitLen z.natAbs ≤ X.V := by
  omega

theorem vZ2 {z : ℤ} (hV : X.V = 2 * w) (h : bitLen z.natAbs ≤ 2 * w) : bitLen z.natAbs ≤ X.V := by
  omega

theorem vS {x : ℕ} (hV : X.V = 2 * w) (h : x ≤ w) : x ≤ X.V := by omega

end Sizes

/-! ## Phase states -/

/-- After `phM`: marks on all scratch stacks. -/
def stM (S : HL → List Sym)  : HL → List Sym :=
  cSt S (.mark :: S (.inr 0)) (.mark :: S (.inr 1)) (.mark :: S (.inr 2)) (.mark :: S (.inr 3))
    (.mark :: S (.inr 4)) (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (.mark :: S (.inr 7))
    (.mark :: S (.inr 8)) (.mark :: S (.inr 9)) (.mark :: S (.inr 10)) (.mark :: S (.inr 11))
    (.mark :: S (.inr 12)) (.mark :: S (.inr 13)) (.mark :: S (.inr 14)) (.mark :: S (.inr 15))
    (S (.inl 3))

/-- After `phA`. -/
def stA (S : HL → List Sym) (q P num : ℕ) : HL → List Sym :=
  cSt S (natSyms (q + 2 + 4) ++ .mark :: S (.inr 0)) (.mark :: S (.inr 1)) (.mark :: S (.inr 2))
    (intSyms ((ntv P num : ℕ) : ℤ) ++ .mark :: S (.inr 3)) (.mark :: S (.inr 4))
    (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (.mark :: S (.inr 7)) (.mark :: S (.inr 8))
    (.mark :: S (.inr 9)) (natSyms (q + 2) ++ .mark :: S (.inr 10)) (.mark :: S (.inr 11))
    (.mark :: S (.inr 12)) (.mark :: S (.inr 13)) (.mark :: S (.inr 14)) (.mark :: S (.inr 15))
    (S (.inl 3))

/-- After `phB`. -/
def stB (S : HL → List Sym) (q P num den : ℕ) : HL → List Sym :=
  cSt S (.mark :: S (.inr 0)) (.mark :: S (.inr 1)) (.mark :: S (.inr 2))
    (intSyms ((ntv P num : ℕ) : ℤ) ++ .mark :: S (.inr 3)) (.mark :: S (.inr 4))
    (intSyms (nsq P num) ++ .mark :: S (.inr 5)) (natSyms (dtv q den) ++ .mark :: S (.inr 6))
    (.mark :: S (.inr 7)) (natSyms (dsq q den) ++ .mark :: S (.inr 8)) (.mark :: S (.inr 9))
    (natSyms (q + 2) ++ .mark :: S (.inr 10)) (.mark :: S (.inr 11)) (.mark :: S (.inr 12))
    (.mark :: S (.inr 13)) (.mark :: S (.inr 14)) (.mark :: S (.inr 15)) (S (.inl 3))

/-- After `phC`. -/
def stC (S : HL → List Sym) (q P num den : ℕ) : HL → List Sym :=
  cSt S (.mark :: S (.inr 0)) (.mark :: S (.inr 1)) (.mark :: S (.inr 2))
    (intSyms ((ntv P num : ℕ) : ℤ) ++ .mark :: S (.inr 3)) (.mark :: S (.inr 4))
    (intSyms (nsq P num) ++ .mark :: S (.inr 5)) (natSyms (dtv q den) ++ .mark :: S (.inr 6))
    (.mark :: S (.inr 7)) (natSyms (dsq q den) ++ .mark :: S (.inr 8))
    (natSyms (q + 2 + 25) ++ .mark :: S (.inr 9)) (natSyms (q + 2) ++ .mark :: S (.inr 10))
    (natSyms (q + 2 + 2 * (q + 2 + 25) + 22) ++ .mark :: S (.inr 11))
    (intSyms ((2 ^ (q + 2 + 2 * (q + 2 + 25) + 22) : ℕ) : ℤ) ++ .mark :: S (.inr 12))
    (.mark :: S (.inr 13)) (.mark :: S (.inr 14)) (.mark :: S (.inr 15)) (S (.inl 3))

/-- After `phD`. -/
def stD (S : HL → List Sym) (q P num den : ℕ) : HL → List Sym :=
  cSt S (.mark :: S (.inr 0)) (.mark :: S (.inr 1)) (.mark :: S (.inr 2))
    (intSyms ((ntv P num : ℕ) : ℤ) ++ .mark :: S (.inr 3)) (.mark :: S (.inr 4))
    (intSyms (nsq P num) ++ .mark :: S (.inr 5)) (natSyms (dtv q den) ++ .mark :: S (.inr 6))
    (.mark :: S (.inr 7)) (natSyms (dsq q den) ++ .mark :: S (.inr 8))
    (natSyms (q + 2 + 25) ++ .mark :: S (.inr 9)) (natSyms (q + 2) ++ .mark :: S (.inr 10))
    (natSyms (q + 2 + 2 * (q + 2 + 25) + 22) ++ .mark :: S (.inr 11))
    (natSyms (2 ^ (q + 2 + 2 * (q + 2 + 25) + 22)) ++ .mark :: S (.inr 12))
    (.mark :: S (.inr 13)) (intSyms (reV q P num den) ++ .mark :: S (.inr 14))
    (.mark :: S (.inr 15)) (S (.inl 3))

/-- After `phE0`. -/
def stE0 (S : HL → List Sym) (q P num den : ℕ) : HL → List Sym :=
  cSt S (.mark :: S (.inr 0)) (intSyms (imP q P num den) ++ .mark :: S (.inr 1))
    (.mark :: S (.inr 2)) (.mark :: S (.inr 3))
    (intSyms (sa0V q P num den) ++ .mark :: S (.inr 4))
    (intSyms (nsq P num) ++ .mark :: S (.inr 5)) (natSyms (dtv q den) ++ .mark :: S (.inr 6))
    (intSyms (sinV q P num den * ((2 ^ (q + 2) : ℕ) : ℤ)) ++ .mark :: S (.inr 7))
    (natSyms (dsq q den) ++ .mark :: S (.inr 8)) (natSyms (q + 2 + 25) ++ .mark :: S (.inr 9))
    (natSyms (q + 2) ++ .mark :: S (.inr 10))
    (natSyms (q + 2 + 2 * (q + 2 + 25) + 22) ++ .mark :: S (.inr 11))
    (natSyms (2 ^ (q + 2 + 2 * (q + 2 + 25) + 22)) ++ .mark :: S (.inr 12))
    (.mark :: S (.inr 13)) (intSyms (reV q P num den) ++ .mark :: S (.inr 14))
    (.mark :: S (.inr 15)) (S (.inl 3))

/-- After the sign step. -/
def stE (S : HL → List Sym) (q P num den : ℕ) (neg : Bool) : HL → List Sym :=
  cSt S (.mark :: S (.inr 0)) (intSyms (imV q P num den neg) ++ .mark :: S (.inr 1))
    (.mark :: S (.inr 2)) (.mark :: S (.inr 3))
    (intSyms (sa0V q P num den) ++ .mark :: S (.inr 4))
    (intSyms (nsq P num) ++ .mark :: S (.inr 5)) (natSyms (dtv q den) ++ .mark :: S (.inr 6))
    (intSyms (sinV q P num den * ((2 ^ (q + 2) : ℕ) : ℤ)) ++ .mark :: S (.inr 7))
    (natSyms (dsq q den) ++ .mark :: S (.inr 8)) (natSyms (q + 2 + 25) ++ .mark :: S (.inr 9))
    (natSyms (q + 2) ++ .mark :: S (.inr 10))
    (natSyms (q + 2 + 2 * (q + 2 + 25) + 22) ++ .mark :: S (.inr 11))
    (natSyms (2 ^ (q + 2 + 2 * (q + 2 + 25) + 22)) ++ .mark :: S (.inr 12))
    (.mark :: S (.inr 13)) (intSyms (reV q P num den) ++ .mark :: S (.inr 14))
    (.mark :: S (.inr 15)) (S (.inl 3))

/-- After `phF`: the record is on the destination. -/
def stF (S : HL → List Sym) (q P num den : ℕ) (neg : Bool) : HL → List Sym :=
  cSt S (.mark :: S (.inr 0)) (.mark :: S (.inr 1)) (.mark :: S (.inr 2)) (.mark :: S (.inr 3))
    (.mark :: S (.inr 4)) (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (.mark :: S (.inr 7))
    (.mark :: S (.inr 8)) (.mark :: S (.inr 9)) (.mark :: S (.inr 10)) (.mark :: S (.inr 11))
    (.mark :: S (.inr 12)) (.mark :: S (.inr 13)) (.mark :: S (.inr 14)) (.mark :: S (.inr 15))
    (intSyms (reV q P num den) ++ (intSyms (imV q P num den neg) ++ (Sym.sep :: S (.inl 3))))

/-! ## Phases `phM`, `phA`, `phB` -/

section Phases

variable {X : KX} {I : KI}

theorem phM_spec (S : HL → List Sym) : HT [] S (phM I) (stM S) 16 := by
  unfold phM stM
  apply HT.mono
  · refine HT.seq ((HT.pushS (.inr 0) .mark S []).of_eq (cSt_init ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 1) .mark _ []).of_eq (by rw [cSt_1, cSt_upd1]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 2) .mark _ []).of_eq (by rw [cSt_2, cSt_upd2]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 3) .mark _ []).of_eq (by rw [cSt_3, cSt_upd3]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 4) .mark _ []).of_eq (by rw [cSt_4, cSt_upd4]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 5) .mark _ []).of_eq (by rw [cSt_5, cSt_upd5]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 6) .mark _ []).of_eq (by rw [cSt_6, cSt_upd6]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 7) .mark _ []).of_eq (by rw [cSt_7, cSt_upd7]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 8) .mark _ []).of_eq (by rw [cSt_8, cSt_upd8]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 9) .mark _ []).of_eq (by rw [cSt_9, cSt_upd9]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 10) .mark _ []).of_eq (by rw [cSt_10, cSt_upd10]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 11) .mark _ []).of_eq (by rw [cSt_11, cSt_upd11]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 12) .mark _ []).of_eq (by rw [cSt_12, cSt_upd12]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 13) .mark _ []).of_eq (by rw [cSt_13, cSt_upd13]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 14) .mark _ []).of_eq (by rw [cSt_14, cSt_upd14]) le_rfl)
      ((HT.pushS (.inr 15) .mark _ []).of_eq (by rw [cSt_15, cSt_upd15]) le_rfl)
  · norm_num

theorem phA_spec (hX : X.OK I) (hE : I.SpecX X.C) (S : HL → List Sym) (q num den P w : ℕ)
    (r0 r1 : List Sym) (hr0 : TermOK r0) (hr1 : TermOK r1)
    (e0 : S (.inl 0) = natSyms q ++ r0) (e1 : S (.inl 1) = natSyms num ++ r1)
    (hP : intSyms (IntMul.computablePiScaledWithCost (q + 2 + 4)).1 = Sym.pos :: natSyms P)
    (hV : X.V = 2 * w) (hw : Wd q P num den w) :
    HT [] (stM S) (phA I) (stA S q P num) (17 * X.U + X.C * (q + 2 + 4 + 1) ^ 4) := by
  have hp := hw.par
  unfold phA stM stA
  apply HT.mono
  · refine HT.seq ((HT.ucp hX (.inl 0) (.inr 10) (by decide) (by norm_num) _ q r0 hr0
        (by rw [cSt_in0]; exact e0) (vB hV hw.hq)).of_eq (by rw [cSt_10, cSt_upd10]) le_rfl) <| HT.seq
      ((HT.uincN hX (.inr 10) (by norm_num) (.mark :: S (.inr 10)) (termOK_mark _) 2 q _
        (by rw [cSt_10]) (vN hV (by omega))).of_eq (cSt_upd10 ..) le_rfl) <| HT.seq
      ((HT.ucp hX (.inr 10) (.inr 0) (by decide) (by norm_num) _ (q + 2) _ (termOK_mark _)
        (by rw [cSt_10]) (vN hV (by omega))).of_eq (by rw [cSt_0, cSt_upd0]) le_rfl) <| HT.seq
      ((HT.uincN hX (.inr 0) (by norm_num) (.mark :: S (.inr 0)) (termOK_mark _) 4 (q + 2) _
        (by rw [cSt_0]) (vN hV (by omega))).of_eq (cSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.upi hE (.inr 0) (.inr 1) (by decide) (by norm_num) _ (q + 2 + 4) _ (termOK_mark _)
        (by rw [cSt_0])).of_eq (by rw [cSt_1, cSt_upd1]) le_rfl) <| HT.seq
      ((HT.popS (.inr 1) _ Sym.pos (natSyms P ++ .mark :: S (.inr 1))
        (by simp only [cSt_1, hP, List.cons_append]) []).of_eq (cSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.us1 hX hE (.inr 1) (by norm_num) _ P _ (termOK_mark _) (by rw [cSt_1])).of_eq
        (cSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 1) .pos _ []).of_eq (by rw [cSt_1, cSt_upd1, intSyms_natCast']) le_rfl) <|
      HT.seq
      ((HT.ucp hX (.inl 1) (.inr 2) (by decide) (by norm_num) _ num r1 hr1
        (by rw [cSt_in1]; exact e1) (vB hV hw.hnum)).of_eq (by rw [cSt_2, cSt_upd2]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 2) .pos _ []).of_eq (by rw [cSt_2, cSt_upd2, intSyms_natCast']) le_rfl) <|
      HT.seq
      ((HT.umu hX (.inr 1) (.inr 2) (.inr 3) (by decide) (by norm_num) _ _ _ _ _ (termOK_mark _)
        (termOK_mark _) (by rw [cSt_1]) (by rw [cSt_2]) (vC hV hw.p2) (vC hV hw.hnum)).of_eq
        (by rw [cSt_3, cSt_upd3]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 1) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_1])
        (vC hV hw.p2)).of_eq (cSt_upd1 ..) le_rfl)
      ((HT.udrI hX (.inr 2) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_2])
        (vC hV hw.hnum)).of_eq ?_ le_rfl)
    rw [cSt_upd2, nt_cast]
  · have := KX.eight_le hX
    omega

theorem phB_spec (hX : X.OK I) (hE : I.SpecX X.C) (S : HL → List Sym) (q num den P w : ℕ)
    (r2 : List Sym) (hr2 : TermOK r2) (e2 : S (.inl 2) = natSyms den ++ r2)
    (hV : X.V = 2 * w) (hw : Wd q P num den w) :
    HT [] (stA S q P num) (phB I) (stB S q P num den) (16 * X.U) := by
  have hp := hw.par
  unfold phB stA stB
  apply HT.mono
  · refine HT.seq ((HT.ucpI hX (.inr 3) (.inr 4) (by decide) (by norm_num) _ _ _ (termOK_mark _)
        (by rw [cSt_3]) (vC hV hw.nt)).of_eq (by rw [cSt_4, cSt_upd4]) le_rfl) <| HT.seq
      ((HT.umu hX (.inr 3) (.inr 4) (.inr 5) (by decide) (by norm_num) _ _ _ _ _ (termOK_mark _)
        (termOK_mark _) (by rw [cSt_3]) (by rw [cSt_4]) (vC hV hw.nt) (vC hV hw.nt)).of_eq
        (by rw [cSt_5, cSt_upd5]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 4) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_4])
        (vC hV hw.nt)).of_eq (cSt_upd4 ..) le_rfl) <| HT.seq
      ((HT.ung hX hE (.inr 5) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_5])).of_eq
        (cSt_upd5 ..) le_rfl) <| HT.seq
      ((HT.ucp hX (.inl 2) (.inr 6) (by decide) (by norm_num) _ den r2 hr2
        (by rw [cSt_in2]; exact e2) (vB hV hw.hden)).of_eq (by rw [cSt_6, cSt_upd6]) le_rfl) <| HT.seq
      ((HT.usv hX hE (.inr 6) (.inr 0) (by decide) (by norm_num) _ den (q + 2 + 4) _ _
        (termOK_mark _) (termOK_mark _) (by rw [cSt_6]) (by rw [cSt_0])
        (vS hV (by omega))).of_eq (cSt_upd6 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 0) (by norm_num) _ (q + 2 + 4) _ (termOK_mark _) (by rw [cSt_0])
        (vN hV (by omega))).of_eq (cSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 6) .pos _ []).of_eq (by rw [cSt_6, cSt_upd6, intSyms_natCast']) le_rfl) <|
      HT.seq
      ((HT.ucpI hX (.inr 6) (.inr 7) (by decide) (by norm_num) _ _ _ (termOK_mark _)
        (by rw [cSt_6]) (vC hV hw.dt)).of_eq (by rw [cSt_7, cSt_upd7]) le_rfl) <| HT.seq
      ((HT.umu hX (.inr 6) (.inr 7) (.inr 8) (by decide) (by norm_num) _ _ _ _ _ (termOK_mark _)
        (termOK_mark _) (by rw [cSt_6]) (by rw [cSt_7]) (vC hV hw.dt) (vC hV hw.dt)).of_eq
        (by rw [cSt_8, cSt_upd8]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 7) (by norm_num) _ _ _ (termOK_mark _) (by rw [cSt_7])
        (vC hV hw.dt)).of_eq (cSt_upd7 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 8) _ Sym.pos (natSyms (dtv q den * dtv q den) ++ .mark :: S (.inr 8))
        (by simp only [cSt_8, intSyms_natMul, List.cons_append]) []).of_eq (cSt_upd8 ..) le_rfl)
      ((HT.popS (.inr 6) _ Sym.pos (natSyms (den * 2 ^ (q + 2 + 4)) ++ .mark :: S (.inr 6))
        (by simp only [cSt_6, intSyms_natCast, List.cons_append]) []).of_eq ?_ le_rfl)
    rw [cSt_upd6]
  · have := KX.eight_le hX
    omega

end Phases

#assert_std_axioms vN vB vB2 vC vZ vZ2 vS phM_spec phA_spec phB_spec

end WP.W7sc
