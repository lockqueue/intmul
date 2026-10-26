import WP.W9c.RowCostLem

/-!
# WP.W9c.RowCostBC — phases B and C of the row cost, and the assembly (`rowCostLe_of_AD`)

With `S = spreadRowBound Mul w h = nb·(2·M) + nb·((W+1)(s+w+p_in+2)) + nb·(W·eb w) + (r+W)·eb w +
hdrLen + 1` (`M = Mul ((W+1)(s+w))`), `1 ≤ W ≤ r ≤ nb·W` and `1 ≤ nb`:
* phase B: every term is `C·x` with `x ≤ c·S` (filter row `≤ W·(w+2)+1`, tap loop
  `≤ 2·(W+1)(s+w+p_in+2)`, row block `≤ r·eb w`, counters `≤ hdrLen` or `≤ 2r`);
* phase C: two passes, `passT ≤ nb·C·M + 64(C+3)(nb(W+1)(s+w+p_in+2) + (r+W)(s+5) + 1)`
  (`passTBound_holds`, with `nb` = the machine's block count by `chunks_count`, `zl + zr = r`), and
  `(r+W)(s+5) ≤ 6·nb(W+1)(s+w+p_in+2)`; the zip reads `2·r·(w+2)` cell symbols
  (`rowCells_listSyms_le`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- **Phases B and C** of the row driver within `4000·(C·S + S)`. -/
theorem costBC_le (hA : W3_dec_amortised) (C : ℕ) (Mul : ℕ → ℕ) (h : PreHdr) (w : ℕ)
    (taps : List ℤ) (row : Array (ℤ × ℤ)) (hD : PreDims h) (hrow : row.size = h.r)
    (hrowW : ArrW w row) (htapsW : TapsW w taps) (htapsL : taps.length ≤ h.W)
    (hout : ArrW w (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1
      h.r taps row)) :
    costB C h.pSub h.m1 h.r w taps row.toList + costC C Mul h.pSub h.m1 h.r h.p_in w taps row.toList ≤
      4000 * (C * spreadRowBound Mul w h) + 4000 * spreadRowBound Mul w h := by
  obtain ⟨p_in, pSub, m1, t1, r⟩ := h
  obtain ⟨-, hr2, -, -⟩ := hD
  change r = 2 ^ natLog2Fuel r r at hr2
  change row.size = r at hrow
  change taps.length ≤ effectiveFilterWidth m1 r at htapsL
  change ArrW w (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => strideOf pSub) p_in pSub m1
    r taps row) at hout
  have hSdef : spreadRowBound Mul w ⟨p_in, pSub, m1, t1, r⟩ =
      kroneckerSpreadNumBlocks m1 r * (2 * Mul ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w))) +
      kroneckerSpreadNumBlocks m1 r * ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w + p_in + 2)) +
      kroneckerSpreadNumBlocks m1 r * (effectiveFilterWidth m1 r * eb w) +
      (r + effectiveFilterWidth m1 r) * eb w +
      ((hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 2) + 1 := by
    simp only [spreadRowBound, PreHdr.nb, PreHdr.W, PreHdr.s, PreHdr.hdrLen]
    ring
  change costB C pSub m1 r w taps row.toList + costC C Mul pSub m1 r p_in w taps row.toList ≤
    4000 * (C * spreadRowBound Mul w ⟨p_in, pSub, m1, t1, r⟩) +
      4000 * spreadRowBound Mul w ⟨p_in, pSub, m1, t1, r⟩
  generalize spreadRowBound Mul w ⟨p_in, pSub, m1, t1, r⟩ = S at hSdef ⊢
  -- basic facts
  have hr0 : 0 < r := by rw [hr2]; exact Nat.two_pow_pos _
  have hW1 : 1 ≤ effectiveFilterWidth m1 r := effectiveFilterWidth_pos m1 r hr0
  have hWr : effectiveFilterWidth m1 r ≤ r := effectiveFilterWidth_le_r m1 r
  have hx : (row.toList.map Prod.fst).length = r := by simp [hrow]
  have hnb := chunks_count pSub m1 r p_in taps _ hr0 hx htapsL
  have hmul := length_chunks_mul (effectiveFilterWidth m1 r) hW1 r (row.toList.map Prod.fst)
  rw [hnb, hx] at hmul
  have hnb1 : 1 ≤ kroneckerSpreadNumBlocks m1 r := by
    rcases Nat.eq_zero_or_pos (kroneckerSpreadNumBlocks m1 r) with h0 | h0
    · exfalso
      unfold kroneckerSpreadNumBlocks at h0
      rw [Nat.div_eq_zero_iff_lt (by omega)] at h0
      omega
    · exact h0
  have hrnb : r ≤ kroneckerSpreadNumBlocks m1 r * effectiveFilterWidth m1 r := by
    have h1 := Nat.div_add_mod (r + effectiveFilterWidth m1 r - 1) (effectiveFilterWidth m1 r)
    have h2 := Nat.mod_lt (r + effectiveFilterWidth m1 r - 1) (show 0 < effectiveFilterWidth m1 r by omega)
    have h3 : kroneckerSpreadNumBlocks m1 r = (r + effectiveFilterWidth m1 r - 1) /
        effectiveFilterWidth m1 r := rfl
    rw [h3, Nat.mul_comm]
    omega
  have hzz := zl_add_zr m1 r hr2 hr0
  -- the shape of S
  have hL : (hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 2 ≤ S := by omega
  have hS1 : 1 ≤ S := by omega
  have hA2 : kroneckerSpreadNumBlocks m1 r * ((effectiveFilterWidth m1 r + 1) *
      (strideOf pSub + w + p_in + 2)) ≤ S := by omega
  have hA1 : kroneckerSpreadNumBlocks m1 r *
      (2 * Mul ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w))) ≤ S := by omega
  have hA3 : kroneckerSpreadNumBlocks m1 r * (effectiveFilterWidth m1 r * eb w) ≤ S := by omega
  have hA4 : (r + effectiveFilterWidth m1 r) * eb w ≤ S := by omega
  have hr4 : 4 * r ≤ S := by
    have : r * 4 ≤ (r + effectiveFilterWidth m1 r) * eb w :=
      Nat.mul_le_mul (by omega) (by unfold eb; omega)
    omega
  have hWfield : bitLen (effectiveFilterWidth m1 r) ≤ (hdrSyms (preTapeFields pSub m1 t1 r)).length :=
    bitLen_le_pre pSub m1 t1 r _ (by simp [preTapeFields])
  -- phase B
  have hB : costB C pSub m1 r w taps row.toList ≤ 14 * (C * S) + 4 * S := by
    unfold costB
    have hfr := length_filterRowSyms_le w taps htapsW
    have hfW : taps.length * (w + 2) ≤ S := by
      have h1 : taps.length * (w + 2) ≤ effectiveFilterWidth m1 r * eb w :=
        Nat.mul_le_mul htapsL (by unfold eb; omega)
      have h2 : effectiveFilterWidth m1 r * eb w ≤
          kroneckerSpreadNumBlocks m1 r * (effectiveFilterWidth m1 r * eb w) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have t1 : C * ((filterRowSyms taps).length + 1) ≤ 2 * (C * S) := rc_cmul (by omega)
    have hbt : bitLen taps.length ≤ bitLen (effectiveFilterWidth m1 r) := bitLen_mono htapsL
    have t2 : C * (bitLen (effectiveFilterWidth m1 r) + bitLen taps.length + 1) ≤ 3 * (C * S) :=
      rc_cmul (by omega)
    have hzl : zerosLead (Computability.encodeNat (effectiveFilterWidth m1 r + taps.length)) ≤
        effectiveFilterWidth m1 r + taps.length :=
      le_trans (zerosLead_le_length _) (bitLen_le_self _)
    have t3 : C * (zerosLead (Computability.encodeNat (effectiveFilterWidth m1 r + taps.length)) + 1) ≤
        2 * (C * S) := rc_cmul (by omega)
    have m3 := rc_max (a := 1)
      (b := C * (zerosLead (Computability.encodeNat (effectiveFilterWidth m1 r + taps.length)) + 1))
    have hX : taps.length * (w + (strideOf pSub - 1 + 1) + 0 + 2 + 1) ≤ 2 * S := by
      have h1 : taps.length * (w + (strideOf pSub - 1 + 1) + 0 + 2 + 1) ≤
          (effectiveFilterWidth m1 r + 1) * (2 * (strideOf pSub + w + p_in + 2)) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (effectiveFilterWidth m1 r + 1) * (2 * (strideOf pSub + w + p_in + 2)) =
          2 * ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w + p_in + 2)) := by ring
      have h3 : (effectiveFilterWidth m1 r + 1) * (strideOf pSub + w + p_in + 2) ≤
          kroneckerSpreadNumBlocks m1 r * ((effectiveFilterWidth m1 r + 1) *
            (strideOf pSub + w + p_in + 2)) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have t4 : C * (taps.length * (w + (strideOf pSub - 1 + 1) + 0 + 2 + 1) +
        bitLen (effectiveFilterWidth m1 r) + 1) ≤ 4 * (C * S) := rc_cmul (by omega)
    have hblk := length_blkE_le w row.toList hrowW
    have hrl : row.toList.length = r := by simp [hrow]
    rw [hrl] at hblk
    have hblk2 : r * eb w ≤ (r + effectiveFilterWidth m1 r) * eb w := Nat.mul_le_mul_right _ (by omega)
    have t5 : C * ((blkE row.toList).length + 1) ≤ 2 * (C * S) := rc_cmul (by omega)
    have hC : C ≤ C * S := Nat.le_mul_of_pos_right _ hS1
    omega
  -- phase C
  have hC : costC C Mul pSub m1 r p_in w taps row.toList ≤ 1028 * (C * S) + 3072 * S := by
    unfold costC
    rw [show row.toList.length = r by simp [hrow], chunks_count pSub m1 r p_in taps _ hr0 hx htapsL]
    have hol : outLenOf (effectiveFilterWidth m1 r) taps ≤ 2 * effectiveFilterWidth m1 r := by
      unfold outLenOf
      split_ifs <;> omega
    have pT := passTBound_holds hA C Mul (strideOf pSub - 1 + 1) p_in pSub (effectiveFilterWidth m1 r)
      (zlOf r (lowOf m1 r)) (zrOf r (lowOf m1 r)) (outLenOf (effectiveFilterWidth m1 r) taps) w
      (strideOf pSub) (kroneckerSpreadNumBlocks m1 r) hW1 (by omega) (by unfold strideOf; omega)
      hol (by omega)
    have f1 : 2 * (kroneckerSpreadNumBlocks m1 r *
        (C * Mul ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w)))) ≤ C * S := by
      have h1 : C * (kroneckerSpreadNumBlocks m1 r *
          (2 * Mul ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w)))) ≤ C * S :=
        Nat.mul_le_mul_left _ hA1
      have h2 : C * (kroneckerSpreadNumBlocks m1 r *
          (2 * Mul ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w)))) =
          2 * (kroneckerSpreadNumBlocks m1 r *
            (C * Mul ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w)))) := by ring
      omega
    have hRW : (zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r) + effectiveFilterWidth m1 r) *
        (strideOf pSub + 5) ≤ 6 * S := by
      rw [hzz]
      have h1 : r + effectiveFilterWidth m1 r ≤ 2 * (kroneckerSpreadNumBlocks m1 r *
          (effectiveFilterWidth m1 r + 1)) := by
        have : kroneckerSpreadNumBlocks m1 r * effectiveFilterWidth m1 r ≤
            kroneckerSpreadNumBlocks m1 r * (effectiveFilterWidth m1 r + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have : effectiveFilterWidth m1 r ≤ kroneckerSpreadNumBlocks m1 r * effectiveFilterWidth m1 r :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      have h2 : (r + effectiveFilterWidth m1 r) * (strideOf pSub + 5) ≤
          (2 * (kroneckerSpreadNumBlocks m1 r * (effectiveFilterWidth m1 r + 1))) *
            (3 * (strideOf pSub + w + p_in + 2)) := Nat.mul_le_mul h1 (by omega)
      have h3 : (2 * (kroneckerSpreadNumBlocks m1 r * (effectiveFilterWidth m1 r + 1))) *
          (3 * (strideOf pSub + w + p_in + 2)) = 6 * (kroneckerSpreadNumBlocks m1 r *
            ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w + p_in + 2))) := by ring
      omega
    have f2 : (C + 3) * 64 * (kroneckerSpreadNumBlocks m1 r * ((effectiveFilterWidth m1 r + 1) *
        (strideOf pSub + w + p_in + 2)) + (zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r) +
          effectiveFilterWidth m1 r) * (strideOf pSub + 5) + 1) ≤ 512 * (C * S) + 1536 * S := by
      have h1 : (C + 3) * 64 * (kroneckerSpreadNumBlocks m1 r * ((effectiveFilterWidth m1 r + 1) *
          (strideOf pSub + w + p_in + 2)) + (zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r) +
            effectiveFilterWidth m1 r) * (strideOf pSub + 5) + 1) ≤ (C + 3) * 64 * (8 * S) :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : (C + 3) * 64 * (8 * S) = 512 * (C * S) + 1536 * S := by ring
      omega
    obtain ⟨hR, hI⟩ := rowCells_listSyms_le pSub m1 r p_in w taps row hr2 hr0 hrow htapsL hout
    have hrw : r * (w + 2) ≤ S := by
      have : r * (w + 2) ≤ (r + effectiveFilterWidth m1 r) * eb w :=
        Nat.mul_le_mul (by omega) (by unfold eb; omega)
      omega
    have f3 : C * ((listSyms (rowCells pSub m1 r p_in taps (row.toList.map Prod.fst))).length +
        (listSyms (rowCells pSub m1 r p_in taps (row.toList.map Prod.snd))).length + 1) ≤
        3 * (C * S) := rc_cmul (by omega)
    omega
  omega

/-- **The row cost obligation**, given phases A and D (`RowCostAD`). -/
theorem rowCostLe_of_AD (hAD : RowCostAD) : RowCostLe := by
  intro hA
  obtain ⟨K, hK⟩ := hAD
  refine ⟨K + 4000, fun C Mul h w taps row hD hrow hrowW htapsW htapsL hout => ?_⟩
  have h1 := hK C Mul h w taps hD htapsW htapsL
  have h2 := costBC_le hA C Mul h w taps row hD hrow hrowW htapsW htapsL hout
  have e : (K + 4000) * (C + 1) * spreadRowBound Mul w h =
      K * (C + 1) * spreadRowBound Mul w h + 4000 * (C * spreadRowBound Mul w h) +
        4000 * spreadRowBound Mul w h := by ring
  omega

#assert_std_axioms costBC_le rowCostLe_of_AD

end WP.W9c
