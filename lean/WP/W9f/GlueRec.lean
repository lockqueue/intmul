import WP.W9f.GlueHdr

/-!
# WP.W9f.GlueRec — reading the POST record `(c0.re, c1.re, μ)` and advancing the table head

`recPass`: copies `a` onto `PA`, `c` onto `PC` (signed), `μ` onto `PMU` (natural), and moves the
record from `TR` to `TL` symbol by symbol (so `TL` receives it reversed: the head advance of
`W9_columnSolve`). `HT.recPass` states the exact effect; cost `O(|record|)`.
-/

namespace WP.W9f

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 Computability

variable {σ : Type} (lS : Lens σ (Option Sym))

/-- The register holds `neg`. -/
def isNegR : Option Sym → Bool
  | some Sym.neg => true
  | _ => false

/-- A signed record field whose sign `sg` was popped: copy the magnitude onto `dst`, push `sg`
there, and move sign, magnitude and the following `sep2` from `TR` onto `TL`. -/
def sfBody (dst : F) (sg : Sym) : Prog HL (fun _ => Sym) σ :=
  ((copyBlock F.TR.loc dst.loc F.X'.loc).liftRegs lS).seq
    ((pushS dst.loc sg).seq ((pushS F.TL.loc sg).seq
      (((moveBlock F.TR.loc F.TL.loc).liftRegs lS).seq
        ((popS F.TR.loc).seq (pushS F.TL.loc Sym.sep2)))))

/-- Read one signed record field into `dst`. -/
def sfStep (dst : F) : Prog HL (fun _ => Sym) σ :=
  (popR' lS F.TR.loc).seq
    (.ite (fun v => isNegR (lS.get v)) (sfBody lS dst .neg) (sfBody lS dst .pos))

/-- Read the natural field `μ` into `PMU`; move it and its `sep` from `TR` onto `TL`. -/
def muStep : Prog HL (fun _ => Sym) σ :=
  ((copyBlock F.TR.loc F.PMU.loc F.X'.loc).liftRegs lS).seq
    (((moveBlock F.TR.loc F.TL.loc).liftRegs lS).seq ((popS F.TR.loc).seq (pushS F.TL.loc Sym.sep)))

/-- The record pass. -/
def recPass : Prog HL (fun _ => Sym) σ := (sfStep lS .PA).seq ((sfStep lS .PC).seq (muStep lS))

theorem HT.sfBody (σ0 : HL → List Sym) (s : F → List Sym) (dst : F) (sg : Sym) (n : ℕ)
    (rest : List Sym) (hR : dst ≠ .TR) (hL : dst ≠ .TL) (hX : dst ≠ .X')
    (hs : s .TR = natSyms n ++ Sym.sep2 :: rest) :
    HT [] (henc σ0 s) (sfBody lS dst sg)
      (henc σ0 (Function.update (Function.update (Function.update s dst
        (sg :: (natSyms n ++ s dst))) .TL
        (Sym.sep2 :: ((encodeNat n).reverse.map Sym.bit ++ sg :: s .TL))) .TR rest))
      (10 * bitLen n + 15) := by
  have h1 := HT.copyBlockF lS σ0 s .TR dst .X' (Ne.symm hR) (by decide) hX (encodeNat n)
    (Sym.sep2 :: rest) (TermOK.cons rfl _) hs
  set s1 := Function.update s dst ((encodeNat n).map Sym.bit ++ s dst) with hs1
  have h2 := HT.pushF (σ := σ) σ0 s1 dst sg
  set s2 := Function.update s1 dst (sg :: s1 dst) with hs2
  have h3 := HT.pushF (σ := σ) σ0 s2 .TL sg
  set s3 := Function.update s2 .TL (sg :: s2 .TL) with hs3
  have hs3R : s3 .TR = (encodeNat n).map Sym.bit ++ Sym.sep2 :: rest := by
    rw [hs3, Function.update_of_ne (by decide), hs2, Function.update_of_ne (Ne.symm hR), hs1,
      Function.update_of_ne (Ne.symm hR), hs]
    rfl
  have h4 := HT.moveBlockF lS σ0 s3 .TR .TL (by decide) (encodeNat n) (Sym.sep2 :: rest)
    (TermOK.cons rfl _) hs3R
  set s4 := Function.update (Function.update s3 .TR (Sym.sep2 :: rest)) .TL
    ((encodeNat n).reverse.map Sym.bit ++ s3 .TL) with hs4
  have h5 := HT.popF (σ := σ) σ0 s4 .TR Sym.sep2 rest (by
    rw [hs4, Function.update_of_ne (by decide), Function.update_self])
  have h6 := HT.pushF (σ := σ) σ0 (Function.update s4 .TR rest) .TL Sym.sep2
  refine (HT.seq h1 (HT.seq h2 (HT.seq h3 (HT.seq h4 (HT.seq h5 h6))))).of_eq ?_
    (by simp only [bitLen]; omega)
  congr 1
  funext g
  by_cases gR : g = .TR
  · subst gR
    simp
  by_cases gL : g = .TL
  · subst gL
    simp [hs4, hs3, hs2, hs1, Ne.symm hL]
  by_cases gd : g = dst
  · subst gd
    simp [hs4, hs3, hs2, hs1, Function.update_apply, hR, hL, natSyms]
  · simp [hs4, hs3, hs2, hs1, Function.update_apply, gR, gL, gd]

theorem HT.sfStep (σ0 : HL → List Sym) (s : F → List Sym) (dst : F) (z : ℤ) (rest : List Sym)
    (hR : dst ≠ .TR) (hL : dst ≠ .TL) (hX : dst ≠ .X')
    (hs : s .TR = intSyms z ++ Sym.sep2 :: rest) :
    HT [] (henc σ0 s) (sfStep lS dst)
      (henc σ0 (Function.update (Function.update (Function.update s dst (intSyms z ++ s dst)) .TL
        (Sym.sep2 :: ((encodeNat z.natAbs).reverse.map Sym.bit ++ sgnSym z :: s .TL))) .TR rest))
      (10 * bitLen z.natAbs + 17) := by
  have hk : henc σ0 s F.TR.loc = sgnSym z :: (natSyms z.natAbs ++ Sym.sep2 :: rest) := by
    rw [henc_loc, hs]
    rfl
  have key : ∀ sg : Sym, sgnSym z = sg →
      HT [] (Function.update (henc σ0 s) F.TR.loc (natSyms z.natAbs ++ Sym.sep2 :: rest))
        (WP.W9f.sfBody lS dst sg)
        (henc σ0 (Function.update (Function.update (Function.update s dst (intSyms z ++ s dst))
          .TL (Sym.sep2 :: ((encodeNat z.natAbs).reverse.map Sym.bit ++ sgnSym z :: s .TL))) .TR
          rest)) (10 * bitLen z.natAbs + 15) := by
    intro sg hsg
    rw [henc_update]
    refine (HT.sfBody lS σ0 _ dst sg z.natAbs rest hR hL hX (by simp)).of_eq ?_ le_rfl
    congr 1
    funext g
    by_cases gR : g = .TR
    · subst gR
      simp [Function.update_apply]
    by_cases gL : g = .TL
    · subst gL
      simp [Function.update_apply, hsg]
    by_cases gd : g = dst
    · subst gd
      simp [Function.update_apply, hR, intSyms, hsg]
    · simp [Function.update_apply, gR, gL, gd]
  refine (HT.popBranch lS F.TR.loc (henc σ0 s) _ (sgnSym z) _ hk isNegR _ _ []
    (fun _ => key .neg ?_) (fun _ => key .pos ?_)).mono (by omega)
  · rename_i h
    unfold sgnSym at h ⊢
    split_ifs at h ⊢ <;> simp_all [isNegR]
  · rename_i h
    unfold sgnSym at h ⊢
    split_ifs at h ⊢ <;> simp_all [isNegR]

theorem HT.muStep (σ0 : HL → List Sym) (s : F → List Sym) (μ : ℕ) (rest : List Sym)
    (hs : s .TR = natSyms μ ++ Sym.sep :: rest) :
    HT [] (henc σ0 s) (muStep lS)
      (henc σ0 (Function.update (Function.update (Function.update s .PMU (natSyms μ ++ s .PMU)) .TL
        (Sym.sep :: ((encodeNat μ).reverse.map Sym.bit ++ s .TL))) .TR rest))
      (10 * bitLen μ + 13) := by
  have h1 := HT.copyBlockF lS σ0 s .TR .PMU .X' (by decide) (by decide) (by decide) (encodeNat μ)
    (Sym.sep :: rest) (TermOK.cons rfl _) hs
  set s1 := Function.update s .PMU ((encodeNat μ).map Sym.bit ++ s .PMU) with hs1
  have h2 := HT.moveBlockF lS σ0 s1 .TR .TL (by decide) (encodeNat μ) (Sym.sep :: rest)
    (TermOK.cons rfl _) (by rw [hs1, Function.update_of_ne (by decide), hs]; rfl)
  set s2 := Function.update (Function.update s1 .TR (Sym.sep :: rest)) .TL
    ((encodeNat μ).reverse.map Sym.bit ++ s1 .TL) with hs2
  have h3 := HT.popF (σ := σ) σ0 s2 .TR Sym.sep rest (by
    rw [hs2, Function.update_of_ne (by decide), Function.update_self])
  have h4 := HT.pushF (σ := σ) σ0 (Function.update s2 .TR rest) .TL Sym.sep
  refine (HT.seq h1 (HT.seq h2 (HT.seq h3 h4))).of_eq ?_ (by simp only [bitLen]; omega)
  congr 1
  funext g
  cases g <;> simp [hs2, hs1, natSyms]

/-- **The record pass**: `a, c, μ` copied onto `PA, PC, PMU`; the record moved `TR → TL`. -/
theorem HT.recPass (σ0 : HL → List Sym) (s : F → List Sym) (a c : ℤ) (μ : ℕ)
    (restT : List Sym) (hs : s .TR = postRecSyms a c μ ++ restT) :
    HT [] (henc σ0 s) (recPass lS)
      (henc σ0 (Function.update (Function.update (Function.update (Function.update
        (Function.update s .PA (intSyms a ++ s .PA)) .PC (intSyms c ++ s .PC)) .PMU
        (natSyms μ ++ s .PMU)) .TL ((postRecSyms a c μ).reverse ++ s .TL)) .TR restT))
      (10 * (bitLen a.natAbs + bitLen c.natAbs + bitLen μ) + 47) := by
  have hs' : s .TR = intSyms a ++ Sym.sep2 ::
      (intSyms c ++ Sym.sep2 :: (natSyms μ ++ Sym.sep :: restT)) := by
    rw [hs]
    simp [postRecSyms]
  have h1 := HT.sfStep lS σ0 s .PA a _ (by decide) (by decide) (by decide) hs'
  set s1 := Function.update (Function.update (Function.update s .PA (intSyms a ++ s .PA)) .TL
    (Sym.sep2 :: ((encodeNat a.natAbs).reverse.map Sym.bit ++ sgnSym a :: s .TL))) .TR
    (intSyms c ++ Sym.sep2 :: (natSyms μ ++ Sym.sep :: restT)) with hs1
  have h2 := HT.sfStep lS σ0 s1 .PC c _ (by decide) (by decide) (by decide)
    (by rw [hs1, Function.update_self])
  set s2 := Function.update (Function.update (Function.update s1 .PC (intSyms c ++ s1 .PC)) .TL
    (Sym.sep2 :: ((encodeNat c.natAbs).reverse.map Sym.bit ++ sgnSym c :: s1 .TL))) .TR
    (natSyms μ ++ Sym.sep :: restT) with hs2
  have h3 := HT.muStep lS σ0 s2 μ restT (by rw [hs2, Function.update_self])
  refine (HT.seq h1 (HT.seq h2 h3)).of_eq ?_ (by omega)
  congr 1
  funext g
  cases g <;> simp [hs2, hs1, postRecSyms, intSyms, natSyms,
    List.reverse_append, List.map_reverse]

#assert_std_axioms HT.sfBody HT.sfStep HT.muStep HT.recPass

end WP.W9f
