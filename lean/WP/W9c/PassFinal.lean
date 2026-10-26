import WP.W9c.PassInit

/-!
# WP.W9c.PassFinal — pass initialisation and finalisation as exact-stacks triples

* `ht_init`: entry stacks → `loopSt … x (0^W) []` (zero tape split `zl | zr`, zero window).
* `ht_rewind`: move all right cells onto the left (`OUT`), keeping their orientation.
* `ht_final`: emit the last window, rewind, pop the markers.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

variable {σ : Type} (K : PKit σ) {Mul : ℕ → ℕ} {C : ℕ}

theorem tapeL_replicate (r zl : ℕ) (h : zl ≤ r) :
    tapeL (List.replicate r 0) zl = listSyms (List.replicate zl 0) ++ [Sym.mark] := by
  simp [tapeL, List.take_replicate, Nat.min_eq_left h]

theorem tapeR_replicate (zl zr : ℕ) :
    tapeR (List.replicate (zl + zr) 0) zl = listSyms (List.replicate zr 0) ++ [Sym.mark] := by
  simp [tapeR, List.drop_replicate]

theorem ht_init (hK : PKitOK Mul K C) {S : PL → List Sym} {Pg : ℤ} {k p_in q W zl zr ol : ℕ}
    {rg rk ra rb rW rzl rzr rol : List Sym}
    (hA : PArgsOK S Pg k p_in q W zl zr ol rg rk ra rb rW rzl rzr rol)
    (x : List ℤ) (rx : List Sym) (hX : S pX = listSyms x ++ rx) (ρ : List (HP 10 24 σ)) :
    HT ρ S (passInit K) (loopSt S rx (zl + zr) zl x (List.replicate W 0) [])
      (1 + (1 + (pzT C zl + (pzT C zr + (1 + (pzT C W + (1 + (1 + (1 + 1))))))))) := by
  set B1 := Function.update S pOUT (Sym.mark :: S pOUT) with hB1
  set B2 := Function.update B1 pTR (Sym.mark :: B1 pTR) with hB2
  set B3 := Function.update B2 pOUT (listSyms (List.replicate zl 0) ++ B2 pOUT) with hB3
  set B4 := Function.update B3 pTR (listSyms (List.replicate zr 0) ++ B3 pTR) with hB4
  set B5 := Function.update B4 pWIN (Sym.mark :: B4 pWIN) with hB5
  set B6 := Function.update B5 pWIN (listSyms (List.replicate W 0) ++ B5 pWIN) with hB6
  set B7 := Function.update B6 pD (Sym.mark :: B6 pD) with hB7
  set B8 := Function.update B7 pE (Sym.mark :: B7 pE) with hB8
  set B9 := Function.update B8 pPF (Sym.mark :: B8 pPF) with hB9
  set B10 := Function.update B9 pPP (Sym.mark :: B9 pPP) with hB10
  have s1 : HT ρ S (pushS pOUT .mark) B1 1 := HT.pushS pOUT .mark S ρ
  have s2 : HT ρ B1 (pushS pTR .mark) B2 1 := HT.pushS pTR .mark B1 ρ
  have s3 : HT ρ B2 (pushZeros K pZL pOUT) B3 (pzT C zl) :=
    ht_pushZeros K hK pZL pOUT (by decide) (by decide) B2 zl rzl hA.tzl
      (by simp [hB2, hB1, hA.ezl]) ρ
  have s4 : HT ρ B3 (pushZeros K pZR pTR) B4 (pzT C zr) :=
    ht_pushZeros K hK pZR pTR (by decide) (by decide) B3 zr rzr hA.tzr
      (by simp [hB3, hB2, hB1, hA.ezr]) ρ
  have s5 : HT ρ B4 (pushS pWIN .mark) B5 1 := HT.pushS pWIN .mark B4 ρ
  have s6 : HT ρ B5 (pushZeros K pWW pWIN) B6 (pzT C W) :=
    ht_pushZeros K hK pWW pWIN (by decide) (by decide) B5 W rW hA.tW
      (by simp [hB5, hB4, hB3, hB2, hB1, hA.eW]) ρ
  have s7 : HT ρ B6 (pushS pD .mark) B7 1 := HT.pushS pD .mark B6 ρ
  have s8 : HT ρ B7 (pushS pE .mark) B8 1 := HT.pushS pE .mark B7 ρ
  have s9 : HT ρ B8 (pushS pPF .mark) B9 1 := HT.pushS pPF .mark B8 ρ
  have s10 : HT ρ B9 (pushS pPP .mark) B10 1 := HT.pushS pPP .mark B9 ρ
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 (HT.seq s7
    (HT.seq s8 (HT.seq s9 s10))))))))).of_eq ?_ le_rfl
  have hc : cyc (zl + zr) zl [] = (List.replicate (zl + zr) 0, zl) := rfl
  funext j
  by_cases h1 : j = pX
  · subst h1; simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1, hX]
  by_cases h2 : j = pOUT
  · subst h2
    simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1, hc,
      tapeL_replicate (zl + zr) zl (by omega)]
  by_cases h3 : j = pTR
  · subst h3; simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1, hc, tapeR_replicate]
  by_cases h4 : j = pWIN
  · subst h4; simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]
  by_cases h5 : j = pD
  · subst h5; simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]
  by_cases h6 : j = pE
  · subst h6; simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]
  by_cases h7 : j = pPF
  · subst h7; simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]
  by_cases h8 : j = pPP
  · subst h8; simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]
  rw [loopSt_other _ _ _ _ _ _ _ j h1 h2 h3 h4 h5 h6 h7 h8]
  simp [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1, Function.update_of_ne, h2, h3, h4, h5,
    h6, h7, h8]

#assert_std_axioms tapeL_replicate tapeR_replicate ht_init

end WP.W9c
