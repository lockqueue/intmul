import WP.W9c.PassMain

/-!
# WP.W9c.PassInst — the pass as a closed contract instance

`mkPKit` builds the pass kit from the sub-program instances (register type: the product of their
register types and one symbol register). `passInst` is the pass program as an `Inst 10 24 Unit`,
and `passInst_spec` its contract body `PassSpec` (from `ht_pass`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-- Register type of a pass. -/
abbrev PSig (pk : Inst 6 24 Unit) (up wn : Inst 4 24 Unit) (ce : Inst 3 24 Unit)
    (mu : Inst 3 8 Unit) (cp : Inst 2 4 Unit) (dr : Inst 1 4 Unit) (iz : Inst 1 4 Bool)
    (dc : Inst 1 4 Unit) : Type :=
  Option Sym × (pk.R × (up.R × (wn.R × (ce.R × (mu.R × (cp.R × (dr.R × (iz.R × dc.R))))))))

section
variable (pk : Inst 6 24 Unit) (up wn : Inst 4 24 Unit) (ce : Inst 3 24 Unit)
    (mu : Inst 3 8 Unit) (cp : Inst 2 4 Unit) (dr : Inst 1 4 Unit) (iz : Inst 1 4 Bool)
    (dc : Inst 1 4 Unit)

/-- The pass kit over `PSig`. -/
def mkPKit : PKit (PSig pk up wn ce mu cp dr iz dc) where
  lS := Lens.fst _ _
  pk := pk
  lpk := (Lens.snd _ _).comp (Lens.fst _ _)
  up := up
  lup := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
  wn := wn
  lwn := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
  ce := ce
  lce := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
  mu := mu
  lmu := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
  cp := cp
  lcp := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
  dr := dr
  ldr := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))
  iz := iz
  liz := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      (Lens.fst _ _))))))))
  dc := dc
  ldc := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      (Lens.snd _ _))))))))

/-- The pass as a closed contract instance. -/
def passInst : Inst 10 24 Unit where
  m := 24
  R := PSig pk up wn ce mu cp dr iz dc
  obs := fun _ => ()
  P := passProg (mkPKit pk up wn ce mu cp dr iz dc)
  hm := le_refl _
  fin := by
    haveI := pk.fin; haveI := up.fin; haveI := wn.fin; haveI := ce.fin; haveI := mu.fin
    haveI := cp.fin; haveI := dr.fin; haveI := iz.fin; haveI := dc.fin
    infer_instance
  ne := by
    haveI := pk.ne; haveI := up.ne; haveI := wn.ne; haveI := ce.ne; haveI := mu.ne
    haveI := cp.ne; haveI := dr.ne; haveI := iz.ne; haveI := dc.ne
    infer_instance
  cl := passProg_closed _

end

/-- Contract body of a pass instance (cost `passT C Mul …`). -/
def PassSpec (Mul : ℕ → ℕ) (I : Inst 10 24 Unit) (C : ℕ) : Prop :=
  ∀ (k p_in q W zl zr ol wd Bin Bd Bv Bc : ℕ) (Pg : ℤ) (x : List ℤ)
    (rx rg rk ra rb rW rzl rzr rol : List Sym) (S : Loc 10 I.m → List Sym),
    1 ≤ k → 1 ≤ W → W ≤ ol → ol ≤ 2 * W → zl < zl + zr → EndOK rx →
    TermOK rg → TermOK rk → TermOK ra → TermOK rb → TermOK rW → TermOK rzl → TermOK rzr →
    TermOK rol →
    bitLen Pg.natAbs ≤ wd → (∀ v ∈ x, bitLen v.natAbs ≤ Bin) →
    (∀ blk ∈ chunks W x.length x, bitLen (packSignedKronecker ((2 ^ k : ℕ) : ℤ)
      (blk.map (gQuantizeCoordToScale p_in q))).natAbs ≤ wd) →
    (∀ ds ∈ passDigits k p_in q W ol Pg x, ∀ d ∈ ds, bitLen d.natAbs ≤ Bd) →
    (∀ e ∈ passEmit k p_in q W ol Pg x, bitLen e.natAbs ≤ Bv) →
    (∀ m ≤ (passEmit k p_in q W ol Pg x).length,
      ∀ c ∈ (cycAdd (zl + zr) (List.replicate (zl + zr) 0) zl
        ((passEmit k p_in q W ol Pg x).take m)).1, bitLen c.natAbs ≤ Bc) →
    S (.inl 0) = listSyms x ++ rx → S (.inl 1) = intSyms Pg ++ rg →
    S (.inl 3) = natSyms k ++ rk → S (.inl 4) = natSyms p_in ++ ra →
    S (.inl 5) = natSyms q ++ rb → S (.inl 6) = natSyms W ++ rW →
    S (.inl 7) = natSyms zl ++ rzl → S (.inl 8) = natSyms zr ++ rzr →
    S (.inl 9) = natSyms ol ++ rol →
    Runs I.P S (Function.update (Function.update S (.inl 0) rx) (.inl 2)
        (listSyms (passCells k p_in q W (zl + zr) zl ol Pg x).reverse ++ Sym.mark :: S (.inl 2)))
      (fun _ => True)
      (passT C Mul k p_in q W zl zr ol wd Bin Bd Bv Bc (chunks W x.length x).length)

theorem passInst_spec {Mul : ℕ → ℕ} {C : ℕ} (pk : Inst 6 24 Unit) (up wn : Inst 4 24 Unit)
    (ce : Inst 3 24 Unit) (mu : Inst 3 8 Unit) (cp : Inst 2 4 Unit) (dr : Inst 1 4 Unit)
    (iz : Inst 1 4 Bool) (dc : Inst 1 4 Unit)
    (hK : PKitOK Mul (mkPKit pk up wn ce mu cp dr iz dc) C) :
    PassSpec Mul (passInst pk up wn ce mu cp dr iz dc) C := by
  intro k p_in q W zl zr ol wd Bin Bd Bv Bc Pg x rx rg rk ra rb rW rzl rzr rol S hk hW hol1 hol2
    hzl hrx tg tk ta tb tW tzl tzr tol hPg hx hP hD hV hC eX eg ek ea eb eW ezl ezr eol
  have hA : PArgsOK S Pg k p_in q W zl zr ol rg rk ra rb rW rzl rzr rol :=
    ⟨tg, tk, ta, tb, tW, tzl, tzr, tol, eg, ek, ea, eb, eW, ezl, ezr, eol⟩
  exact HT.runs (ht_pass (mkPKit pk up wn ce mu cp dr iz dc) hK hA x rx hrx eX wd Bin Bd Bv Bc
    hk hW hol1 hol2 hzl hPg hx hP hD hV hC [])

#assert_std_axioms passInst_spec

end WP.W9c
