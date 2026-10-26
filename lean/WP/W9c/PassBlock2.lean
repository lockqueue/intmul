import WP.W9c.PassBlock

/-!
# WP.W9c.PassBlock2 — the block step of the pass

`ht_block`: from `loopSt … v ws E` (with `v ≠ []`), one `blockBody` reaches
`loopSt … (v.drop W) ws' (E ++ es)`, where `ds` = the block's digits,
`(es, ws') = winStep W ws ds`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-- The pass's named inputs at entry. -/
structure PArgsOK (S : PL → List Sym) (Pg : ℤ) (k p_in q W zl zr ol : ℕ)
    (rg rk ra rb rW rzl rzr rol : List Sym) : Prop where
  tg : TermOK rg
  tk : TermOK rk
  ta : TermOK ra
  tb : TermOK rb
  tW : TermOK rW
  tzl : TermOK rzl
  tzr : TermOK rzr
  tol : TermOK rol
  eg : S pPG = intSyms Pg ++ rg
  ek : S pK = natSyms k ++ rk
  ea : S pPIN = natSyms p_in ++ ra
  eb : S pQ = natSyms q ++ rb
  eW : S pWW = natSyms W ++ rW
  ezl : S pZL = natSyms zl ++ rzl
  ezr : S pZR = natSyms zr ++ rzr
  eol : S pOL = natSyms ol ++ rol

/-- Cost of one block. -/
def blockT (C : ℕ) (Mul : ℕ → ℕ) (nv k p_in q W ol wd Bin Bd Bv Bc p r lPf lP : ℕ) : ℕ :=
  C * (nv * (Bin + k + p_in + q + 1) + bitLen W + 1) + (C * Mul wd + C) + 1 + C * (lPf + 1) +
    C * (lP + ol * (k + 1) + 1) + C * (W * (Bd + 1) + 1) +
    C * (W * (Bv + Bc + 1) + (p + W - 1) / r * (r * (Bc + 1)) + 1)

variable {σ : Type} (K : PKit σ) {Mul : ℕ → ℕ} {C : ℕ}

theorem ht_block (hK : PKitOK Mul K C) {S : PL → List Sym} {Pg : ℤ} {k p_in q W zl zr ol : ℕ}
    {rg rk ra rb rW rzl rzr rol : List Sym}
    (hA : PArgsOK S Pg k p_in q W zl zr ol rg rk ra rb rW rzl rzr rol)
    (rx : List Sym) (hrx : EndOK rx) (r wd Bin Bd Bv Bc : ℕ) (v ws E : List ℤ)
    (Pf : ℤ) (ds : List ℤ)
    (hPfd : Pf = packSignedKronecker ((2 ^ k : ℕ) : ℤ) ((v.take W).map (gQuantizeCoordToScale p_in q)))
    (hdsd : ds = blockDigits k p_in q ol Pg (v.take W))
    (hk : 1 ≤ k) (hvB : ∀ x ∈ v, bitLen x.natAbs ≤ Bin) (hws : ws.length = W)
    (hol1 : W ≤ ol) (hol2 : ol ≤ 2 * W)
    (hPf : bitLen Pf.natAbs ≤ wd) (hPg : bitLen Pg.natAbs ≤ wd)
    (hdB : ∀ d ∈ ds, bitLen d.natAbs ≤ Bd) (hwsB : ∀ x ∈ ws, bitLen x.natAbs ≤ Bd)
    (hesB : ∀ e ∈ (winStep W ws ds).1, bitLen e.natAbs ≤ Bv)
    (hr : 0 < r) (hp : (cyc r zl E).2 ≤ r)
    (hcells : ∀ j ≤ (winStep W ws ds).1.length, ∀ c ∈ (cycAdd r (cyc r zl E).1 (cyc r zl E).2
      ((winStep W ws ds).1.take j)).1, bitLen c.natAbs ≤ Bc)
    (ρ : List (HP 10 24 σ)) :
    HT ρ (loopSt S rx r zl v ws E) (blockBody K)
      (loopSt S rx r zl (v.drop W) (winStep W ws ds).2 (E ++ (winStep W ws ds).1))
      (blockT C Mul (v.take W).length k p_in q W ol wd Bin Bd Bv Bc (cyc r zl E).2 r
        (bitLen Pf.natAbs) (bitLen (Pf * Pg).natAbs)) := by
  have hlen : (cyc r zl E).1.length = r := by simp [cyc, cycAdd_length]
  have hesl : (winStep W ws ds).1.length = W := by
    have : ds.length = ol := by rw [hdsd]; exact length_unpack _ _ _
    simp [winStep, hws]; omega
  -- 1: block pack
  have e10 : loopSt S rx r zl v ws E pX = listSyms v ++ rx := by simp
  have e11 : loopSt S rx r zl v ws E pK = natSyms k ++ rk := by simp [loopSt, hA.ek]
  have e12 : loopSt S rx r zl v ws E pPIN = natSyms p_in ++ ra := by simp [loopSt, hA.ea]
  have e13 : loopSt S rx r zl v ws E pQ = natSyms q ++ rb := by simp [loopSt, hA.eb]
  have e14 : loopSt S rx r zl v ws E pWW = natSyms W ++ rW := by simp [loopSt, hA.eW]
  have s1 : HT ρ (loopSt S rx r zl v ws E) (callI K.pk [pX, pK, pPIN, pQ, pWW, pPF] pX K.lpk)
      (Function.update (Function.update (loopSt S rx r zl v ws E) pX (listSyms (v.drop W) ++ rx))
        pPF (intSyms Pf ++ loopSt S rx r zl v ws E pPF))
      (C * ((v.take W).length * (Bin + k + p_in + q + 1) + bitLen W + 1)) := by
    rw [hPfd]
    exact HT.callI_upd2 K.pk [pX, pK, pPIN, pQ, pWW, pPF] pX (by decide) rfl (by norm_num) K.lpk
      _ (.inl 0) (.inl 5) _ _ (hK.pk k p_in q W Bin v rx rk ra rb rW _ hk hvB hrx hA.tk hA.ta hA.tb
        hA.tW e10 e11 e12 e13 e14) ρ
  set L0 := loopSt S rx r zl v ws E with hL0
  set L1 := Function.update (Function.update L0 pX (listSyms (v.drop W) ++ rx)) pPF
    (intSyms Pf ++ L0 pPF) with hL1
  -- 2: product
  have e20 : L1 pPF = intSyms Pf ++ Sym.mark :: S pPF := by simp [hL1, hL0]
  have e21 : L1 pPG = intSyms Pg ++ rg := by simp [hL1, hL0, loopSt, hA.eg]
  have s2 : HT ρ L1 (callI K.mu [pPF, pPG, pPP] pX K.lmu)
      (Function.update L1 pPP (intSyms (Pf * Pg) ++ L1 pPP)) (C * Mul wd + C) :=
    HT.callI_upd K.mu [pPF, pPG, pPP] pX (by decide) rfl (by norm_num) K.lmu L1 (.inl 2) _
      (hK.mu wd Pf Pg (Sym.mark :: S pPF) rg _ hPf hPg (termOK_mark _) hA.tg e20 e21) ρ
  set L2 := Function.update L1 pPP (intSyms (Pf * Pg) ++ L1 pPP) with hL2
  -- 3: pop the sign of Pf
  have e30 : L2 pPF = sgnSym Pf :: (natSyms Pf.natAbs ++ Sym.mark :: S pPF) := by
    simp [hL2, hL1, hL0, intSyms]
  have s3 : HT ρ L2 (popS pPF) (Function.update L2 pPF (natSyms Pf.natAbs ++ Sym.mark :: S pPF))
      1 := HT.popS pPF L2 _ _ e30 ρ
  set L3 := Function.update L2 pPF (natSyms Pf.natAbs ++ Sym.mark :: S pPF) with hL3
  -- 4: drop |Pf|
  have e40 : L3 pPF = natSyms Pf.natAbs ++ Sym.mark :: S pPF := by simp [hL3]
  have s4 : HT ρ L3 (callI K.dr [pPF] pX K.ldr) (Function.update L3 pPF (Sym.mark :: S pPF))
      (C * (bitLen Pf.natAbs + 1)) :=
    HT.dropNat hK.dr pX K.ldr pPF (by norm_num) L3 Pf.natAbs _ (termOK_mark _) e40 ρ
  set L4 := Function.update L3 pPF (Sym.mark :: S pPF) with hL4
  -- 5: unpack
  have e50 : L4 pPP = intSyms (Pf * Pg) ++ Sym.mark :: S pPP := by
    simp [hL4, hL3, hL2, hL1, hL0]
  have e51 : L4 pK = natSyms k ++ rk := by simp [hL4, hL3, hL2, hL1, hL0, loopSt, hA.ek]
  have e52 : L4 pOL = natSyms ol ++ rol := by simp [hL4, hL3, hL2, hL1, hL0, loopSt, hA.eol]
  have hds' : ds = unpackSignedKronecker ((2 ^ (k - 1) : ℕ) : ℤ) ol (Pf * Pg) := by
    rw [hdsd, hPfd]; rfl
  have s5 : HT ρ L4 (callI K.up [pPP, pK, pOL, pD] pX K.lup)
      (Function.update (Function.update L4 pPP (Sym.mark :: S pPP)) pD (listSyms ds ++ L4 pD))
      (C * (bitLen (Pf * Pg).natAbs + ol * (k + 1) + 1)) := by
    rw [hds']
    exact HT.callI_upd2 K.up [pPP, pK, pOL, pD] pX (by decide) rfl (by norm_num) K.lup L4
      (.inl 0) (.inl 3) _ _
      (hK.up k ol (Pf * Pg) (Sym.mark :: S pPP) rk rol _ hk (termOK_mark _) hA.tk hA.tol e50 e51
        e52) ρ
  set L5 := Function.update (Function.update L4 pPP (Sym.mark :: S pPP)) pD (listSyms ds ++ L4 pD)
    with hL5
  -- 6: window
  have e60 : L5 pD = listSyms ds ++ Sym.mark :: S pD := by simp [hL5, hL4, hL3, hL2, hL1, hL0]
  have e61 : L5 pWIN = listSyms ws ++ Sym.mark :: S pWIN := by
    simp [hL5, hL4, hL3, hL2, hL1, hL0]
  have e63 : L5 pWW = natSyms W ++ rW := by simp [hL5, hL4, hL3, hL2, hL1, hL0, loopSt, hA.eW]
  have hdl : ds.length = ol := by rw [hdsd]; exact length_unpack _ _ _
  have s6 : HT ρ L5 (callI K.wn [pD, pWIN, pE, pWW] pX K.lwn)
      (Function.update (Function.update (Function.update L5 pD (Sym.mark :: S pD)) pWIN
        (listSyms (winStep W ws ds).2 ++ Sym.mark :: S pWIN)) pE
        (listSyms (winStep W ws ds).1 ++ L5 pE)) (C * (W * (Bd + 1) + 1)) :=
    HT.callI_upd3 K.wn [pD, pWIN, pE, pWW] pX (by decide) rfl (by norm_num) K.lwn L5 (.inl 0)
      (.inl 1) (.inl 2) _ _ _
      (hK.wn W Bd ds ws (Sym.mark :: S pD) (Sym.mark :: S pWIN) rW _ hws (by omega) (by omega)
        hdB hwsB (endOK_mark _) (endOK_mark _) hA.tW e60 e61 e63) ρ
  set L6 := Function.update (Function.update (Function.update L5 pD (Sym.mark :: S pD)) pWIN
    (listSyms (winStep W ws ds).2 ++ Sym.mark :: S pWIN)) pE
    (listSyms (winStep W ws ds).1 ++ L5 pE) with hL6
  -- 7: cyclic emit
  have e70 : L6 pE = listSyms (winStep W ws ds).1 ++ Sym.mark :: S pE := by
    simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
  have e71 : L6 pOUT = tapeL (cyc r zl E).1 (cyc r zl E).2 ++ S pOUT := by
    simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
  have e72 : L6 pTR = tapeR (cyc r zl E).1 (cyc r zl E).2 ++ S pTR := by
    simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
  have hcells' : ∀ j ≤ (winStep W ws ds).1.length, ∀ c ∈ (cycAdd (cyc r zl E).1.length
      (cyc r zl E).1 (cyc r zl E).2 ((winStep W ws ds).1.take j)).1, bitLen c.natAbs ≤ Bc := by
    rw [hlen]; exact hcells
  have happ : cyc r zl (E ++ (winStep W ws ds).1) =
      cycAdd r (cyc r zl E).1 (cyc r zl E).2 (winStep W ws ds).1 := by
    unfold cyc; exact cycAdd_append _ _ _ _ _
  have s7 : HT ρ L6 (callI K.ce [pE, pOUT, pTR] pX K.lce)
      (Function.update (Function.update (Function.update L6 pE (Sym.mark :: S pE)) pOUT
        (tapeL (cyc r zl (E ++ (winStep W ws ds).1)).1 (cyc r zl (E ++ (winStep W ws ds).1)).2 ++
          S pOUT)) pTR
        (tapeR (cyc r zl (E ++ (winStep W ws ds).1)).1 (cyc r zl (E ++ (winStep W ws ds).1)).2 ++
          S pTR))
      (C * (W * (Bv + Bc + 1) + ((cyc r zl E).2 + W - 1) / r * (r * (Bc + 1)) + 1)) := by
    have h := HT.callI_upd3 K.ce [pE, pOUT, pTR] pX (by decide) rfl (by norm_num) K.lce L6 (.inl 0)
      (.inl 1) (.inl 2) _ _ _
      (hK.ce Bc Bv (cyc r zl E).2 (cyc r zl E).1 (winStep W ws ds).1 (Sym.mark :: S pE) (S pOUT)
        (S pTR) _ (by rw [hlen]; exact hr) (by rw [hlen]; exact hp) (endOK_mark _) hesB hcells'
        e70 e71 e72) ρ
    rw [hlen, hesl] at h
    rw [happ]
    exact h
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 s7)))))).of_eq ?_ ?_
  · funext j
    by_cases h1 : j = pX
    · subst h1; simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
    by_cases h2 : j = pOUT
    · subst h2; simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
    by_cases h3 : j = pTR
    · subst h3; simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
    by_cases h4 : j = pWIN
    · subst h4; simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
    by_cases h5 : j = pD
    · subst h5; simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
    by_cases h6 : j = pE
    · subst h6; simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
    by_cases h7 : j = pPF
    · subst h7; simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
    by_cases h8 : j = pPP
    · subst h8; simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0]
    rw [loopSt_other _ _ _ _ _ _ _ j h1 h2 h3 h4 h5 h6 h7 h8]
    simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0, Function.update_of_ne, h1, h2, h3, h4, h5, h6, h7, h8,
      loopSt_other _ _ _ _ _ _ _ j h1 h2 h3 h4 h5 h6 h7 h8]
  · unfold blockT
    omega

end WP.W9c
