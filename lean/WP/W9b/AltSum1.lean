import WP.W9b.AltCost

/-!
# WP.W9b.AltSum1 — the P2 kernel on its local stacks

`altKernel = altPre ; altMid ; altPost`. From `W0 = xRows` it pushes the retained value
`computableNyquistAltSumContiguous p_in pSub r xRows[t1/2]` (reversed) onto `RET` and restores every
other stack, within `1100·(C+1)·altSumBound` steps (`alt_cost_le`).
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability
open IntMul (gRescale computableNyquistAltSumContiguous)

/-- **The P2 kernel** on its local stacks. -/
def altKernel (k : W3Kit) : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (altPre k) (.seq (altMid k) (altPost k))

theorem closed_altKernel (k : W3Kit) (hA : k.PA.Closed) (hS : k.PS.Closed) (hN : k.PN.Closed)
    (hM : k.PM.Closed) (hL : k.PL.Closed) (hR : k.PR.Closed) : (altKernel k).Closed :=
  ⟨closed_altPre k, closed_altMid k hA hS, closed_altPost k hA hN hM hL hR⟩

theorem preDims_facts {h : PreHdr} (hd : PreDims h) :
    2 ≤ h.t1 ∧ h.r = 2 ^ h.mr ∧ 1 ≤ h.mr ∧ h.r = 2 * (h.r / 2) := by
  obtain ⟨ht, hr, h1, h2⟩ := hd
  have a : 2 ^ 1 ≤ 2 ^ h.mt1 := Nat.pow_le_pow_right (by norm_num) h1
  obtain ⟨j, hj⟩ : ∃ j, h.mr = j + 1 := ⟨h.mr - 1, by omega⟩
  have b : 2 ^ h.mr = 2 * 2 ^ j := by rw [hj, pow_succ]; ring
  refine ⟨by rw [ht]; simpa using a, hr, by omega, by omega⟩

theorem rs_altKernel {C : ℕ} (k : W3Kit) (hok : W3Ok k C) (h : PreHdr) (w : ℕ)
    (xRows : Array (Array (ℤ × ℤ))) (X : AStk → List Sym) (r0 r1 : List Sym)
    (hdims : PreDims h) (hC0 : X .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0)
    (hC1 : X .C1 = hdrSyms [h.p_in] ++ r1) (hsize : xRows.size = h.t1)
    (hrows : ∀ row ∈ xRows.toList, row.size = h.r) (hW : MatW w xRows)
    (hout : EntryW w (computableNyquistAltSumContiguous h.p_in h.pSub h.r
      (xRows.getD (h.t1 / 2) #[])))
    (hW0 : X .W0 = matSyms xRows) :
    Runs (altKernel k) X
      (Function.update X .RET ((entrySyms (computableNyquistAltSumContiguous h.p_in h.pSub h.r
        (xRows.getD (h.t1 / 2) #[]))).reverse ++ X .RET)) (fun _ => True)
      (1100 * (C + 1) * altSumBound w h) := by
  obtain ⟨ht2, hr, hmr, hreven⟩ := preDims_facts hdims
  have hr1 : 1 ≤ h.r := by rw [hr]; exact Nat.one_le_two_pow
  have hi : h.t1 / 2 < xRows.size := by omega
  have hlt : h.t1 / 2 < xRows.toList.length := by simpa using hi
  have hgetD : xRows.getD (h.t1 / 2) #[] = xRows.toList[h.t1 / 2] := by
    first
      | (simp [Array.getD, hi]; done)
      | (unfold Array.getD; rw [dif_pos hi]; rfl)
  rw [hgetD] at hout ⊢
  have hsplit0 : xRows.toList = xRows.toList.take (h.t1 / 2) ++
      xRows.toList[h.t1 / 2] :: xRows.toList.drop (h.t1 / 2 + 1) := by
    rw [← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  have hmidmem : xRows.toList[h.t1 / 2] ∈ xRows.toList := List.getElem_mem hlt
  have hrowslen : (xRows.toList.take (h.t1 / 2)).length = h.t1 / 2 := by simp; omega
  have hrowsr : ∀ row ∈ xRows.toList.take (h.t1 / 2), row.size = h.r := fun row hr' =>
    hrows row (List.mem_of_mem_take hr')
  have hrowsw : ∀ row ∈ xRows.toList.take (h.t1 / 2), ArrW w row := fun row hr' =>
    hW row (List.mem_of_mem_take hr')
  have hmidsize : (xRows.toList[h.t1 / 2]).size = h.r := hrows _ hmidmem
  have hmidw : ∀ z ∈ (xRows.toList[h.t1 / 2]).toList, EntryW w z := hW _ hmidmem
  have hW0' : X .W0 = blkE ((xRows.toList.take (h.t1 / 2)).flatMap Array.toList ++
      ((xRows.toList[h.t1 / 2]).toList ++
        (xRows.toList.drop (h.t1 / 2 + 1)).flatMap Array.toList)) := by
    rw [hW0, matSyms]
    conv_lhs => rw [hsplit0]
    simp
  generalize xRows.toList[h.t1 / 2] = mid at hout hmidsize hmidw hW0' ⊢
  generalize xRows.toList.take (h.t1 / 2) = rows at hrowslen hrowsr hrowsw hW0'
  generalize xRows.toList.drop (h.t1 / 2 + 1) = rest at hW0'
  -- the value
  have hval : computableNyquistAltSumContiguous h.p_in h.pSub h.r mid =
      gRescale (h.mr + h.p_in) h.pSub (accIm (pairUp mid.toList), accRe (pairUp mid.toList)) := by
    have := nyq_eq_acc h.p_in h.pSub h.mr hmr mid (by rw [hmidsize, hr])
    rw [← hr] at this
    exact this
  rw [hval] at hout ⊢
  -- accumulator widths
  have hpl : (pairUp mid.toList).length = h.r / 2 :=
    (unpair_pairUp (h.r / 2) mid.toList (by simp [hmidsize]; omega)).2
  have hB1 : ∀ p ∈ pairUp mid.toList, p.1.1.natAbs ≤ 2 ^ w - 1 ∧ p.2.1.natAbs ≤ 2 ^ w - 1 :=
    fun p hp => by
      have h1 := natAbs_lt_of_entryW (hmidw _ (mem_pairUp _ p hp).1)
      have h2 := natAbs_lt_of_entryW (hmidw _ (mem_pairUp _ p hp).2)
      omega
  have hB2 : ∀ p ∈ pairUp mid.toList, p.1.2.natAbs ≤ 2 ^ w - 1 ∧ p.2.2.natAbs ≤ 2 ^ w - 1 :=
    fun p hp => by
      have h1 := natAbs_lt_of_entryW (hmidw _ (mem_pairUp _ p hp).1)
      have h2 := natAbs_lt_of_entryW (hmidw _ (mem_pairUp _ p hp).2)
      omega
  have hzr : bitLen (accRe (pairUp mid.toList)).natAbs ≤ w + h.mr :=
    bitLen_le_of_natAbs_le (natAbs_accRe_le _ _ hB1) (by rw [hpl]; omega)
  have hzi : bitLen (accIm (pairUp mid.toList)).natAbs ≤ w + h.mr :=
    bitLen_le_of_natAbs_le (natAbs_accIm_le _ _ hB2) (by rw [hpl]; omega)
  -- the three phases
  have hTm : ∀ l : List Sym, TermOK (Sym.mark :: l) := fun l => TermOK.cons rfl l
  have e1 := rs_altPre k h X r0 rows (mid.toList ++ rest.flatMap Array.toList) (by omega)
    hrowslen hrowsr hC0 hW0'
  have e2 := rs_altMid k hok (preOut X h.r rows (mid.toList ++ rest.flatMap Array.toList)) h.r
    h.mr w (Sym.mark :: X .R) (Sym.mark :: X .K) (X .T) (Sym.mark :: X .AR) (Sym.mark :: X .AI)
    (rows.flatMap Array.toList) mid.toList (rest.flatMap Array.toList) (hTm _) (hTm _) (hTm _)
    (hTm _) hr hmr (by simpa using hmidsize) hmidw (by simp [preOut]) (by simp [preOut])
    (by simp [preOut]) (by simp [preOut]) (by simp [preOut]) (by simp [preOut])
    (by simpa [preOut] using hTm (X .AR')) (by simpa [preOut] using hTm (X .AI'))
  refine runs_post (runs_seq e1 (runs_seq e2 (rs_altPost k hok h _ r0 r1
    (accIm (pairUp mid.toList)) (accRe (pairUp mid.toList)) (w + h.mr) (X .AI) (X .AR) (X .AR')
    (X .AI') (X .K) (X .J) (X .R) hzi hzr (by simp [preOut, hC0]) (by simp [preOut, hC1])
    (by simp [preOut]) (by simp [preOut]) (by simp [preOut]) (by simp [preOut])
    (by simp [preOut]) (by simp [preOut]) (by simp [preOut])))) ?_ ?_
  · clear e1 e2
    funext x
    cases x <;> simp [preOut, hW0']
  · have hLsk : (blkE (rows.flatMap Array.toList)).length ≤ rows.length * h.r * (2 * w + 4) := by
      have h1 := length_blkE_le w (rows.flatMap Array.toList) (fun z hz => by
        rw [List.mem_flatMap] at hz
        obtain ⟨row, hrow, hz⟩ := hz
        exact hrowsw row hrow z hz)
      rw [length_flatMap_rows rows h.r hrowsr] at h1
      exact h1
    have hLrow : (blkE mid.toList).length ≤ h.r * (2 * w + 4) := by
      have h1 := length_blkE_le w mid.toList hmidw
      rw [show mid.toList.length = h.r by simp [hmidsize]] at h1
      exact h1
    have hc := alt_cost_le C w h.t1 h.r h.mr h.p_in h.pSub
      (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length (bitLen h.p_in) rows.length
      (blkE (rows.flatMap Array.toList)).length (blkE mid.toList).length _ _ ht2 hr1
      (by omega) hLsk hLrow hout.1 hout.2
    simp only [altSumBound, PreHdr.N, PreHdr.hdrLen, eb]
    omega

#assert_std_axioms closed_altKernel preDims_facts rs_altKernel

end WP.W9b
