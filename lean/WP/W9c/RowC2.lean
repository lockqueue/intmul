import WP.W9c.RowC

/-!
# WP.W9c.RowC2 — proof of `RowCOK` (phase C)
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

theorem effectiveFilterWidth_pos (m1 r : ℕ) (hr : 0 < r) : 1 ≤ effectiveFilterWidth m1 r := by
  unfold effectiveFilterWidth; omega

theorem rowCOK_holds : RowCOK := by
  intro hPW hDg hEm hCe σ K Mul C ρ hK σ0 pSub m1 r p_in w taps restT row hr hr0 hlen hrowB htB
    htW
  have hW1 := effectiveFilterWidth_pos m1 r hr0
  have hWr := effectiveFilterWidth_le_r m1 r
  have hlowr : lowOf m1 r < r := by
    unfold lowOf
    have := Nat.mod_lt m1 (show 0 < 2 ^ natLog2Fuel r r by positivity)
    omega
  have hzlzr : zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r) = r := by
    unfold zlOf zrOf; split_ifs <;> omega
  have hzl : zlOf r (lowOf m1 r) < zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r) := by
    unfold zlOf zrOf; split_ifs <;> omega
  have hol1 : effectiveFilterWidth m1 r ≤ outLenOf (effectiveFilterWidth m1 r) taps := by
    unfold outLenOf; split_ifs with h
    · exact le_rfl
    · have : taps.length ≠ 0 := fun e => h (List.eq_nil_of_length_eq_zero e)
      omega
  have hol2 : outLenOf (effectiveFilterWidth m1 r) taps ≤ 2 * effectiveFilterWidth m1 r := by
    unfold outLenOf; split_ifs <;> omega
  have hk : 1 ≤ strideOf pSub - 1 + 1 := by omega
  have hq : pSub ≤ strideOf pSub := by unfold strideOf; omega
  have hPg := (hPW (strideOf pSub) p_in pSub w (effectiveFilterWidth m1 r) [] taps hq (by simp) htW
    (by simp) htB).2
  -- the pass hypotheses for one coordinate list
  have hpass : ∀ x : List ℤ, x.length = r → (∀ v ∈ x, bitLen v.natAbs ≤ w) →
      (∀ blk ∈ chunks (effectiveFilterWidth m1 r) x.length x,
        bitLen (packSignedKronecker ((2 ^ (strideOf pSub - 1 + 1) : ℕ) : ℤ)
          (blk.map (gQuantizeCoordToScale p_in pSub))).natAbs ≤
            (effectiveFilterWidth m1 r + 1) * (strideOf pSub + w)) ∧
      (∀ m ≤ (passEmit (strideOf pSub - 1 + 1) p_in pSub (effectiveFilterWidth m1 r)
          (outLenOf (effectiveFilterWidth m1 r) taps)
          (packSignedKronecker ((2 ^ (strideOf pSub - 1 + 1) : ℕ) : ℤ) taps) x).length,
        ∀ c ∈ (cycAdd (zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r))
          (List.replicate (zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r)) 0) (zlOf r (lowOf m1 r))
          ((passEmit (strideOf pSub - 1 + 1) p_in pSub (effectiveFilterWidth m1 r)
            (outLenOf (effectiveFilterWidth m1 r) taps)
            (packSignedKronecker ((2 ^ (strideOf pSub - 1 + 1) : ℕ) : ℤ) taps) x).take m)).1,
          bitLen c.natAbs ≤ strideOf pSub - 1 + 1 + 3) := by
    intro x hxl hxB
    refine ⟨fun blk hb => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := chunks_mem _ _ _ _ hb
      exact (hPW (strideOf pSub) p_in pSub w (effectiveFilterWidth m1 r) blk taps hq h1 htW
        (fun v hv => hxB v (h2 v hv)) htB).1
    · rw [hzlzr]
      exact hCe _ _ _ _ _ _ _ _ x hk hW1 hWr (by omega) hol1 hol2
        (by have := length_chunks_mul _ hW1 x.length x; omega)
  -- stack values after phase B
  set L0 := stB σ0 pSub m1 r p_in taps restT row with hL0
  set k := strideOf pSub - 1 + 1 with hkdef
  set W := effectiveFilterWidth m1 r with hWdef
  set zl := zlOf r (lowOf m1 r) with hzldef
  set zr := zrOf r (lowOf m1 r) with hzrdef
  set ol := outLenOf W taps with holdef
  set Pg := packSignedKronecker ((2 ^ k : ℕ) : ℤ) taps with hPgdef
  set wd := (W + 1) * (strideOf pSub + w) with hwd
  set re := row.map Prod.fst with hre
  set im := row.map Prod.snd with him
  have hreB : ∀ v ∈ re, bitLen v.natAbs ≤ w := fun v hv => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv; exact (hrowB z hz).1
  have himB : ∀ v ∈ im, bitLen v.natAbs ≤ w := fun v hv => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv; exact (hrowB z hz).2
  have hrel : re.length = r := by simp [hre, hlen]
  have himl : im.length = r := by simp [him, hlen]
  obtain ⟨hPre, hCre⟩ := hpass re hrel hreB
  obtain ⟨hPim, hCim⟩ := hpass im himl himB
  have eXR : L0 rXR = listSyms re ++ Sym.mark :: σ0 rXR := by simp [hL0, stB, hre]
  have eXI : L0 rXI = listSyms im ++ Sym.mark :: σ0 rXI := by simp [hL0, stB, him]
  have ePG : L0 rPG = intSyms Pg ++ Sym.mark :: σ0 rPG := by simp [hL0, stB, hPgdef, hkdef]
  have eK : L0 rK = natSyms k ++ Sym.mark :: σ0 rK := by simp [hL0, stB, stA, hkdef]
  have ePIN : L0 rPIN = natSyms p_in ++ Sym.mark :: σ0 rPIN := by simp [hL0, stB, stA]
  have eQ : L0 rQ = natSyms pSub ++ Sym.mark :: σ0 rQ := by simp [hL0, stB, stA]
  have eWW : L0 rWW = natSyms W ++ Sym.mark :: σ0 rWW := by simp [hL0, stB, stA, hWdef]
  have eZL : L0 rZL = natSyms zl ++ Sym.mark :: σ0 rZL := by
    simp [hL0, stB, stA, hzldef, lowOf]
  have eZR : L0 rZR = natSyms zr ++ Sym.mark :: σ0 rZR := by
    simp [hL0, stB, stA, hzrdef, lowOf]
  have eOL : L0 rOL = natSyms ol ++ Sym.mark :: σ0 rOL := by simp [hL0, stB, holdef, hWdef]
  have eOR : L0 rOR = σ0 rOR := by simp [hL0, stB, stA]
  have eOI : L0 rOI = σ0 rOI := by simp [hL0, stB, stA]
  have eW0 : L0 rW0 = [] := by simp [hL0, stB]
  -- 1: real pass
  set L1 := Function.update (Function.update L0 rXR (Sym.mark :: σ0 rXR)) rOR
    (listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg re).reverse ++ Sym.mark :: σ0 rOR)
    with hL1
  have s1 : HT ρ L0 (callI K.ps [rXR, rPG, rOR, rK, rPIN, rQ, rWW, rZL, rZR, rOL] rS K.lps) L1
      (passT C Mul k p_in pSub W zl zr ol wd w k (k + 1) (k + 3) (chunks W re.length re).length) := by
    have h : HT ρ L0 (callI K.ps [rXR, rPG, rOR, rK, rPIN, rQ, rWW, rZL, rZR, rOL] rS K.lps)
        (Function.update (Function.update L0 rXR (Sym.mark :: σ0 rXR)) rOR
          (listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg re).reverse ++ Sym.mark :: L0 rOR))
        (passT C Mul k p_in pSub W zl zr ol wd w k (k + 1) (k + 3)
          (chunks W re.length re).length) :=
      HT.callI_upd2 K.ps [rXR, rPG, rOR, rK, rPIN, rQ, rWW, rZL, rZR, rOL] rS (by decide)
      rfl (by norm_num) K.lps L0 (.inl 0) (.inl 2) _ _
      (hK.ps k p_in pSub W zl zr ol wd w k (k + 1) (k + 3) Pg re (Sym.mark :: σ0 rXR)
        (Sym.mark :: σ0 rPG) (Sym.mark :: σ0 rK) (Sym.mark :: σ0 rPIN) (Sym.mark :: σ0 rQ)
        (Sym.mark :: σ0 rWW) (Sym.mark :: σ0 rZL) (Sym.mark :: σ0 rZR) (Sym.mark :: σ0 rOL) _ hk
        hW1 hol1 hol2 hzl (endOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _)
        (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _) hPg hreB
        hPre (hDg _ _ _ _ _ _ _ hk) (hEm _ _ _ _ _ _ _ hk hol1 hol2) hCre eXR ePG eK ePIN eQ eWW
        eZL eZR eOL) ρ
    rw [eOR] at h
    exact h
  -- 2: imaginary pass
  have e1XI : L1 rXI = listSyms im ++ Sym.mark :: σ0 rXI := by simp [hL1, eXI]
  have e1 : ∀ j, j ≠ rXR → j ≠ rOR → L1 j = L0 j := fun j h1 h2 => by
    simp [hL1, Function.update_of_ne h1, Function.update_of_ne h2]
  set L2 := Function.update (Function.update L1 rXI (Sym.mark :: σ0 rXI)) rOI
    (listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg im).reverse ++ Sym.mark :: σ0 rOI)
    with hL2
  have s2 : HT ρ L1 (callI K.ps [rXI, rPG, rOI, rK, rPIN, rQ, rWW, rZL, rZR, rOL] rS K.lps) L2
      (passT C Mul k p_in pSub W zl zr ol wd w k (k + 1) (k + 3) (chunks W im.length im).length) := by
    have e1PG : L1 rPG = intSyms Pg ++ Sym.mark :: σ0 rPG := by
      rw [e1 rPG (by decide) (by decide)]; exact ePG
    have e1K : L1 rK = natSyms k ++ Sym.mark :: σ0 rK := by
      rw [e1 rK (by decide) (by decide)]; exact eK
    have e1PIN : L1 rPIN = natSyms p_in ++ Sym.mark :: σ0 rPIN := by
      rw [e1 rPIN (by decide) (by decide)]; exact ePIN
    have e1Q : L1 rQ = natSyms pSub ++ Sym.mark :: σ0 rQ := by
      rw [e1 rQ (by decide) (by decide)]; exact eQ
    have e1WW : L1 rWW = natSyms W ++ Sym.mark :: σ0 rWW := by
      rw [e1 rWW (by decide) (by decide)]; exact eWW
    have e1ZL : L1 rZL = natSyms zl ++ Sym.mark :: σ0 rZL := by
      rw [e1 rZL (by decide) (by decide)]; exact eZL
    have e1ZR : L1 rZR = natSyms zr ++ Sym.mark :: σ0 rZR := by
      rw [e1 rZR (by decide) (by decide)]; exact eZR
    have e1OL : L1 rOL = natSyms ol ++ Sym.mark :: σ0 rOL := by
      rw [e1 rOL (by decide) (by decide)]; exact eOL
    have e1OI : L1 rOI = σ0 rOI := by rw [e1 rOI (by decide) (by decide)]; exact eOI
    have h : HT ρ L1 (callI K.ps [rXI, rPG, rOI, rK, rPIN, rQ, rWW, rZL, rZR, rOL] rS K.lps)
        (Function.update (Function.update L1 rXI (Sym.mark :: σ0 rXI)) rOI
          (listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg im).reverse ++ Sym.mark :: L1 rOI))
        (passT C Mul k p_in pSub W zl zr ol wd w k (k + 1) (k + 3)
          (chunks W im.length im).length) :=
      HT.callI_upd2 K.ps [rXI, rPG, rOI, rK, rPIN, rQ, rWW, rZL, rZR, rOL] rS (by decide)
      rfl (by norm_num) K.lps L1 (.inl 0) (.inl 2) _ _
      (hK.ps k p_in pSub W zl zr ol wd w k (k + 1) (k + 3) Pg im (Sym.mark :: σ0 rXI)
        (Sym.mark :: σ0 rPG) (Sym.mark :: σ0 rK) (Sym.mark :: σ0 rPIN) (Sym.mark :: σ0 rQ)
        (Sym.mark :: σ0 rWW) (Sym.mark :: σ0 rZL) (Sym.mark :: σ0 rZR) (Sym.mark :: σ0 rOL) _ hk
        hW1 hol1 hol2 hzl (endOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _)
        (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _) hPg himB
        hPim (hDg _ _ _ _ _ _ _ hk) (hEm _ _ _ _ _ _ _ hk hol1 hol2) hCim e1XI e1PG e1K e1PIN
        e1Q e1WW e1ZL e1ZR e1OL) ρ
    rw [e1OI] at h
    exact h
  -- 3: zip
  have hlc : (passCells k p_in pSub W (zl + zr) zl ol Pg re).length =
      (passCells k p_in pSub W (zl + zr) zl ol Pg im).length := by
    simp [passCells, cycAdd_length]
  have e2OR : L2 rOR = listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg re).reverse ++
      Sym.mark :: σ0 rOR := by simp [hL2, hL1]
  have e2OI : L2 rOI = listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg im).reverse ++
      Sym.mark :: σ0 rOI := by simp [hL2]
  have e2W0 : L2 rW0 = [] := by simp [hL2, hL1, eW0]
  set L3 := Function.update (Function.update (Function.update L2 rOR (Sym.mark :: σ0 rOR)) rOI
    (Sym.mark :: σ0 rOI)) rW0 (blkE (List.zip (passCells k p_in pSub W (zl + zr) zl ol Pg re)
      (passCells k p_in pSub W (zl + zr) zl ol Pg im)) ++ L2 rW0) with hL3
  have s3 : HT ρ L2 (callI K.zp [rOR, rOI, rW0] rS K.lzp) L3
      (C * ((listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg re)).length +
        (listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg im)).length + 1)) :=
    HT.callI_upd3 K.zp [rOR, rOI, rW0] rS (by decide) rfl (by norm_num) K.lzp L2 (.inl 0) (.inl 1)
      (.inl 2) _ _ _ (hK.zp _ _ _ _ _ hlc (endOK_mark _) (endOK_mark _) e2OR e2OI) ρ
  refine ⟨_, (HT.seq s1 (HT.seq s2 s3)).of_eq ?_ le_rfl, ?_⟩
  · funext j
    by_cases h1 : j = rXR
    · subst h1; simp [hL3, hL2, hL1, stC, rowCells, hL0]
    by_cases h2 : j = rXI
    · subst h2; simp [hL3, hL2, hL1, stC, rowCells, hL0]
    by_cases h3 : j = rOR
    · subst h3; simp [hL3, hL2, hL1, stC, rowCells, hL0]
    by_cases h4 : j = rOI
    · subst h4; simp [hL3, hL2, hL1, stC, rowCells, hL0]
    by_cases h5 : j = rW0
    · subst h5
      simp only [hL3, Function.update_self, e2W0, List.append_nil, stC]
      rfl
    simp [hL3, hL2, hL1, stC, Function.update_of_ne, h1, h2, h3, h4, h5, hL0]
  · have hc : (chunks W im.length im).length = (chunks W re.length re).length := by
      rw [himl, hrel]; exact length_chunks_congr W hW1 r im re (by rw [himl, hrel])
    have hcost : costC C Mul pSub m1 r p_in w taps row =
        2 * passT C Mul k p_in pSub W zl zr ol wd w k (k + 1) (k + 3)
          (chunks W re.length re).length +
        C * ((listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg re)).length +
          (listSyms (passCells k p_in pSub W (zl + zr) zl ol Pg im)).length + 1) := by
      unfold costC rowCells
      rw [show row.length = re.length by rw [hrel, hlen]]
    rw [hcost, hc]
    omega

#assert_std_axioms effectiveFilterWidth_pos chunks_mem length_chunks_congr length_chunks_mul
  rowCOK_holds

end WP.W9c
