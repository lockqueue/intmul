import WP.W7k3.SerLoop

/-!
# WP.W7k3.SerEnds — setup and end of the series sub-kernel

* `serSetup_spec`: from any host state with the inputs on the named stacks, the setup pushes a
  `mark` on every scratch stack and loads `ctr := n`, `A := a0`, `Sacc := 0`, `F := fβ`,
  `G1 := gδ`, `G2 := gζ`, `Dz := d` (`9U`).
* `serEnd_spec`: from the loop's final state, the result is copied to the destination and every
  scratch stack is restored (`14U`).
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

theorem natSyms_zero_eq : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

theorem serSetup_spec {X : KX} {I : KI} (hX : X.OK I) (κ : SK) (S : SL → List Sym)
    (a0 : ℤ) (d n : ℕ) (r0 r2 r3 : List Sym) (hr0 : TermOK r0) (hr2 : TermOK r2)
    (hr3 : TermOK r3) (e0 : S (.inl 0) = intSyms a0 ++ r0) (e2 : S (.inl 2) = natSyms d ++ r2)
    (e3 : S (.inl 3) = natSyms n ++ r3) (wa0 : bitLen a0.natAbs ≤ X.V) (wd : bitLen d ≤ X.V)
    (wn : bitLen n ≤ X.V) (wf0 : bitLen κ.fβ ≤ X.V) (wg10 : bitLen κ.gδ ≤ X.V)
    (wg20 : bitLen κ.gζ ≤ X.V) :
    HT [] S (serSetup I κ)
      (sSt S (natSyms n ++ .mark :: S (.inr 0)) (intSyms a0 ++ .mark :: S (.inr 1))
        (intSyms 0 ++ .mark :: S (.inr 2)) (natSyms κ.fβ ++ .mark :: S (.inr 3))
        (natSyms κ.gδ ++ .mark :: S (.inr 4)) (natSyms κ.gζ ++ .mark :: S (.inr 5))
        (intSyms d ++ .mark :: S (.inr 6)) (.mark :: S (.inr 7)) (.mark :: S (.inr 8))
        (.mark :: S (.inr 9)) (.mark :: S (.inr 10)) (.mark :: S (.inr 11)) (S (.inl 4)))
      (9 * X.U) := by
  have e8 := KX.eight_le hX
  apply HT.mono
  · unfold serSetup
    refine HT.seq ((HT.pushS (.inr 0) .mark _ []).of_eq (sSt_init ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 1) .mark _ []).of_eq (by rw [sSt_1, sSt_upd1]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 2) .mark _ []).of_eq (by rw [sSt_2, sSt_upd2]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 3) .mark _ []).of_eq (by rw [sSt_3, sSt_upd3]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 4) .mark _ []).of_eq (by rw [sSt_4, sSt_upd4]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 5) .mark _ []).of_eq (by rw [sSt_5, sSt_upd5]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 6) .mark _ []).of_eq (by rw [sSt_6, sSt_upd6]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 7) .mark _ []).of_eq (by rw [sSt_7, sSt_upd7]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 8) .mark _ []).of_eq (by rw [sSt_8, sSt_upd8]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 9) .mark _ []).of_eq (by rw [sSt_9, sSt_upd9]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 10) .mark _ []).of_eq (by rw [sSt_10, sSt_upd10]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 11) .mark _ []).of_eq (by rw [sSt_11, sSt_upd11]) le_rfl) <| HT.seq
      ((HT.ucp hX (.inl 3) (.inr 0) (by decide) (by norm_num) _ n r3 hr3 (by simp [e3]) wn).of_eq
        (by rw [sSt_0, sSt_upd0]) le_rfl) <| HT.seq
      ((HT.ucpI hX (.inl 0) (.inr 1) (by decide) (by norm_num) _ a0 r0 hr0 (by simp [e0])
        wa0).of_eq (by rw [sSt_1, sSt_upd1]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 2) .pos _ []).of_eq
        (by rw [sSt_2, sSt_upd2, ← intSyms_zero_append]) le_rfl) <| HT.seq
      ((HT.upushNat hX (.inr 3) κ.fβ _ wf0).of_eq (by rw [sSt_3, sSt_upd3]) le_rfl) <| HT.seq
      ((HT.upushNat hX (.inr 4) κ.gδ _ wg10).of_eq (by rw [sSt_4, sSt_upd4]) le_rfl) <| HT.seq
      ((HT.upushNat hX (.inr 5) κ.gζ _ wg20).of_eq (by rw [sSt_5, sSt_upd5]) le_rfl) <| HT.seq
      ((HT.ucp hX (.inl 2) (.inr 6) (by decide) (by norm_num) _ d r2 hr2 (by simp [e2]) wd).of_eq
        (by rw [sSt_6, sSt_upd6]) le_rfl)
      ((HT.pushS (.inr 6) .pos _ []).of_eq (by rw [sSt_6, sSt_upd6, intSyms_natCast']) le_rfl)
  · by_contra hc
    omega

theorem serEnd_spec {X : KX} {I : KI} (hX : X.OK I) (S : SL → List Sym) (an sn : ℤ)
    (d fn g1 g2 : ℕ) (wa : bitLen an.natAbs ≤ X.V) (ws : bitLen sn.natAbs ≤ X.V)
    (wd : bitLen d ≤ X.V) (wf : bitLen fn ≤ X.V) (wg1 : bitLen g1 ≤ X.V)
    (wg2 : bitLen g2 ≤ X.V) :
    HT [] (sSt S (natSyms 0 ++ .mark :: S (.inr 0)) (intSyms an ++ .mark :: S (.inr 1))
        (intSyms sn ++ .mark :: S (.inr 2)) (natSyms fn ++ .mark :: S (.inr 3))
        (natSyms g1 ++ .mark :: S (.inr 4)) (natSyms g2 ++ .mark :: S (.inr 5))
        (intSyms d ++ .mark :: S (.inr 6)) (.mark :: S (.inr 7)) (.mark :: S (.inr 8))
        (.mark :: S (.inr 9)) (.mark :: S (.inr 10)) (.mark :: S (.inr 11)) (S (.inl 4)))
      ((kcpI I (.inr 2) (.inl 4)).seq (serClean I))
      (Function.update S (.inl 4) (intSyms sn ++ S (.inl 4))) (14 * X.U) := by
  have e8 := KX.eight_le hX
  have wdz : bitLen (d : ℤ).natAbs ≤ X.V := by simpa using wd
  apply HT.mono
  · unfold serClean
    refine HT.seq ((HT.ucpI hX (.inr 2) (.inl 4) (by decide) (by norm_num) _ sn
        (Sym.mark :: S (.inr 2)) (termOK_mark _) (by simp) ws).of_eq
        (by rw [sSt_d, sSt_updd]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 1) (by norm_num) _ an (Sym.mark :: S (.inr 1)) (termOK_mark _)
        (by simp) wa).of_eq (sSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 1) _ .mark (S (.inr 1)) (by simp) []).of_eq (sSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 2) (by norm_num) _ sn (Sym.mark :: S (.inr 2)) (termOK_mark _)
        (by simp) ws).of_eq (sSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 2) _ .mark (S (.inr 2)) (by simp) []).of_eq (sSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 3) (by norm_num) _ fn (Sym.mark :: S (.inr 3)) (termOK_mark _)
        (by simp) wf).of_eq (sSt_upd3 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 3) _ .mark (S (.inr 3)) (by simp) []).of_eq (sSt_upd3 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 4) (by norm_num) _ g1 (Sym.mark :: S (.inr 4)) (termOK_mark _)
        (by simp) wg1).of_eq (sSt_upd4 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 4) _ .mark (S (.inr 4)) (by simp) []).of_eq (sSt_upd4 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 5) (by norm_num) _ g2 (Sym.mark :: S (.inr 5)) (termOK_mark _)
        (by simp) wg2).of_eq (sSt_upd5 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 5) _ .mark (S (.inr 5)) (by simp) []).of_eq (sSt_upd5 ..) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 6) (by norm_num) _ (d : ℤ) (Sym.mark :: S (.inr 6)) (termOK_mark _)
        (by simp) wdz).of_eq (sSt_upd6 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 6) _ .mark (S (.inr 6)) (by simp) []).of_eq (sSt_upd6 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 0) _ .mark (S (.inr 0)) (by simp [natSyms_zero_eq]) []).of_eq
        (sSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 7) _ .mark (S (.inr 7)) (by simp) []).of_eq (sSt_upd7 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 8) _ .mark (S (.inr 8)) (by simp) []).of_eq (sSt_upd8 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 9) _ .mark (S (.inr 9)) (by simp) []).of_eq (sSt_upd9 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 10) _ .mark (S (.inr 10)) (by simp) []).of_eq (sSt_upd10 ..) le_rfl)
      ((HT.popS (.inr 11) _ .mark (S (.inr 11)) (by simp) []).of_eq
        (by rw [sSt_upd11, sSt_final]) le_rfl)
  · omega

#assert_std_axioms natSyms_zero_eq serSetup_spec serEnd_spec

end WP.W7k3
