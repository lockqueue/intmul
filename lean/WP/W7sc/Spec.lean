import WP.W7sc.PhE

/-!
# WP.W7sc.Spec — the `stdChar` kernel's main host triple

`scProg_spec`: from host stacks `S` with `q`, `num`, `den` on the named stacks `0, 1, 2`, the
program `scProg I neg` pushes `W7.cplxRec (computableStdCharWithProgramCost q num den neg).1` onto
the destination `3` and restores every other stack, within
`140·U + C·(q+7)^4 + 2·Cs·(q+28)·(w+2)^2` steps (`U` the unit of the cost context `X` with
`X.V = 2·w`, `w = wv q den` the snapshot's width, `Cs` the series constant).
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

theorem scProg_spec {X : KX} {I : KI} (hX : X.OK I) (hE : I.SpecX X.C) {Cs : ℕ}
    (hsc : SpecSer SK.cos I.sc Cs) (hss : SpecSer SK.sin I.ss Cs) (neg : Bool)
    (q num den : ℕ) (r0 r1 r2 : List Sym) (S : HL → List Sym)
    (hden : 0 < den) (hnum : num ≤ den) (hr0 : TermOK r0) (hr1 : TermOK r1) (hr2 : TermOK r2)
    (e0 : S (.inl 0) = natSyms q ++ r0) (e1 : S (.inl 1) = natSyms num ++ r1)
    (e2 : S (.inl 2) = natSyms den ++ r2) (hV : X.V = 2 * wv q den) :
    HT [] S (scProg I neg)
      (Function.update S (.inl 3)
        (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den neg).1 ++ S (.inl 3)))
      (140 * X.U + X.C * (q + 2 + 4 + 1) ^ 4 + 2 * (Cs * (q + 2 + 25 + 1) * (wv q den + 2) ^ 2)) := by
  have hw := wd_snap q num den hden hnum
  have hP : intSyms (IntMul.computablePiScaledWithCost (q + 2 + 4)).1 =
      Sym.pos :: natSyms (IntMul.computablePiScaledWithCost (q + 2 + 4)).1.toNat :=
    intSyms_pos (piScaled_nonneg _)
  have hval : intSyms (reV q (IntMul.computablePiScaledWithCost (q + 2 + 4)).1.toNat num den) ++
      (intSyms (imV q (IntMul.computablePiScaledWithCost (q + 2 + 4)).1.toNat num den neg) ++
        (Sym.sep :: S (.inl 3))) =
      W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den neg).1 ++ S (.inl 3) := by
    rw [← val_snap]
    simp only [W7.cplxRec, List.append_assoc, List.singleton_append]
  rw [← hval]
  unfold scProg
  apply HT.mono
  · exact HT.seq (phM_spec S) <|
      HT.seq (phA_spec hX hE S q num den _ _ r0 r1 hr0 hr1 e0 e1 hP hV hw) <|
      HT.seq (phB_spec hX hE S q num den _ _ r2 hr2 e2 hV hw) <|
      HT.seq (phC_spec hX hE S q num den _ _ hV hw) <|
      HT.seq (phD_spec hX hE hsc S q num den _ _ hden hV hw) <|
      HT.seq (phE0_spec hX hE hss S q num den _ _ hden hV hw) <|
      HT.seq (neg_spec hX hE S q num den _ neg) <|
      HT.seq (phF_spec hX S q num den _ _ neg hden hV hw) (phZ_spec S _)
  · have := KX.eight_le hX
    omega

#assert_std_axioms scProg_spec

end WP.W7sc
