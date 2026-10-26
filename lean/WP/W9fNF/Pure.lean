import WP.W9fN.FinishSpec
import IntMulTM.SpecFacts

/-!
# WP.W9fNF.Pure — pure facts for the Nyquist finish (`W9f_nyqFinish`)

* pass 1: `altAcc (0,0)` over the reversed Z block is the snapshot's alternating sum (`altAcc_reverse`);
* pass 2: `nyqOut` as the list `outList D Z.toList` (`nyqOut_toList`);
* the machine rounding `((x >>> (k-1)) + 1) >>> 1 = divRoundPow2 x k` (`rnd_eq`);
* magnitude and bit-length helpers.
-/

namespace WP.W9fNF

open IntMul TMFw.Contracts TMFw.Contracts.W9

/-- One pass-1 step: `A := z - A`, per coordinate. -/
def altStep (A z : ℤ × ℤ) : ℤ × ℤ := (z.1 - A.1, z.2 - A.2)

/-- Pass-1 accumulator after a list, processed front to back. -/
def altAcc : ℤ × ℤ → List (ℤ × ℤ) → ℤ × ℤ
  | A, [] => A
  | A, z :: zs => altAcc (altStep A z) zs

/-- Pass-2 outputs: `z + D`, then `D` flips sign. -/
def outList : ℤ × ℤ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | _, [] => []
  | D, z :: zs => (z.1 + D.1, z.2 + D.2) :: outList (-D.1, -D.2) zs

/-- Alternating sum `z₀ − z₁ + z₂ − …` of a list (helper). -/
def altSumL : List (ℤ × ℤ) → ℤ × ℤ
  | [] => (0, 0)
  | z :: l => altStep (altSumL l) z

/-! ## Helpers -/

theorem read1D_eq_getD (Z : Array (ℤ × ℤ)) (v : ℕ) : read1D Z v = Z.toList.getD v 0 := by
  unfold read1D
  by_cases h : v < Z.size <;> simp [h, List.getD_eq_getElem?_getD]

theorem toList_runSequentialScanSteps {α : Type} (f : ℕ → α) :
    ∀ n, (runSequentialScanSteps f n).outTape.toList = (List.range n).map f
  | 0 => by simp [runSequentialScanSteps]
  | n + 1 => by
    simp only [runSequentialScanSteps, scanHeadStep, Array.toList_push,
      runSequentialScanSteps_inHead, toList_runSequentialScanSteps f n, List.range_succ,
      List.map_append, List.map_cons, List.map_nil]

theorem gAltTerm_succ (v : ℕ) (z : ℤ × ℤ) : gAltTerm (v + 1) z = gNeg (gAltTerm v z) := by
  unfold gAltTerm
  rcases Nat.mod_two_eq_zero_or_one v with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega)]
    simp [gNeg]

theorem gAltTerm_negPair (v : ℕ) (D : ℤ × ℤ) : gAltTerm v (-D.1, -D.2) = gNeg (gAltTerm v D) := by
  unfold gAltTerm
  split_ifs <;> rfl

theorem sumRangePair_shift (f : ℕ → ℤ × ℤ) :
    ∀ n, sumRangePair f (n + 1) = gAdd (f 0) (sumRangePair (fun v => f (v + 1)) n)
  | 0 => by
    show gAdd (sumRangePair f 0) (f 0) = gAdd (f 0) (sumRangePair (fun v => f (v + 1)) 0)
    simp only [sumRangePair, gAdd, zero_add, add_zero]
  | n + 1 => by
    have ih := sumRangePair_shift f n
    show gAdd (sumRangePair f (n + 1)) (f (n + 1)) =
      gAdd (f 0) (gAdd (sumRangePair (fun v => f (v + 1)) n) (f (n + 1)))
    rw [ih]
    simp only [gAdd, add_assoc]

theorem sumRangePair_gNeg (g : ℕ → ℤ × ℤ) :
    ∀ n, sumRangePair (fun v => gNeg (g v)) n = gNeg (sumRangePair g n)
  | 0 => by simp only [sumRangePair, gNeg, neg_zero]
  | n + 1 => by
    show gAdd (sumRangePair (fun v => gNeg (g v)) n) (gNeg (g n)) = gNeg (gAdd (sumRangePair g n) (g n))
    rw [sumRangePair_gNeg g n]
    simp only [gAdd, gNeg, neg_add]

theorem altAcc_append_singleton (A : ℤ × ℤ) (l : List (ℤ × ℤ)) (z : ℤ × ℤ) :
    altAcc A (l ++ [z]) = altStep (altAcc A l) z := by
  induction l generalizing A with
  | nil => rfl
  | cons w l ih => exact ih (altStep A w)

theorem altAcc_reverse_eq_altSumL : ∀ l : List (ℤ × ℤ), altAcc (0, 0) l.reverse = altSumL l
  | [] => rfl
  | z :: l => by
    rw [List.reverse_cons, altAcc_append_singleton, altAcc_reverse_eq_altSumL l]
    rfl

theorem sum_alt_getD : ∀ l : List (ℤ × ℤ),
    sumRangePair (fun v => gAltTerm v (l.getD v 0)) l.length = altSumL l
  | [] => rfl
  | z :: l => by
    have hs : sumRangePair (fun v => gAltTerm v ((z :: l).getD v 0)) (l.length + 1) =
        gAdd (gAltTerm 0 ((z :: l).getD 0 0))
          (sumRangePair (fun v => gAltTerm (v + 1) ((z :: l).getD (v + 1) 0)) l.length) :=
      sumRangePair_shift _ _
    have e : (fun v => gAltTerm (v + 1) ((z :: l).getD (v + 1) 0)) =
        (fun v => gNeg (gAltTerm v (l.getD v 0))) := by
      funext v
      rw [List.getD_cons_succ, gAltTerm_succ]
    have h0 : gAltTerm 0 ((z :: l).getD 0 0) = z := by simp [gAltTerm]
    rw [List.length_cons, hs, e, sumRangePair_gNeg, sum_alt_getD l, h0]
    show gAdd z (gNeg (altSumL l)) = altStep (altSumL l) z
    simp only [gAdd, gNeg, altStep, sub_eq_add_neg]

theorem outList_eq (D : ℤ × ℤ) (l : List (ℤ × ℤ)) :
    outList D l = (List.range l.length).map (fun i => gAdd (l.getD i 0) (gAltTerm i D)) := by
  induction l generalizing D with
  | nil => rfl
  | cons z l ih =>
    rw [outList, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    show (z.1 + D.1, z.2 + D.2) ::
        List.map (fun i => gAdd (l.getD i 0) (gAltTerm i (-D.1, -D.2))) (List.range l.length) =
      (z.1 + D.1, z.2 + D.2) ::
        List.map (fun i => gAdd ((z :: l).getD (i + 1) 0) (gAltTerm (i + 1) D)) (List.range l.length)
    congr 1
    apply List.map_congr_left
    intro i _
    rw [List.getD_cons_succ, gAltTerm_succ, gAltTerm_negPair]

/-! ## P1–P3 -/

/-- **P1.** Pass 1 over the reversed block is the snapshot's alternating sum. -/
theorem altAcc_reverse (Z : Array (ℤ × ℤ)) :
    altAcc (0, 0) Z.toList.reverse = sumRangePair (fun v => gAltTerm v (read1D Z v)) Z.size := by
  rw [altAcc_reverse_eq_altSumL, ← sum_alt_getD, Array.length_toList]
  congr 1
  funext v
  rw [read1D_eq_getD]

/-- **P2.** The finish output as a list. -/
theorem nyqOut_toList (k : ℕ) (alt : ℤ × ℤ) (Z : Array (ℤ × ℤ)) :
    (WP.W9f.nyqOut k alt Z).toList =
      outList (divRoundPow2 (alt.1 - (altAcc (0, 0) Z.toList.reverse).1) k,
        divRoundPow2 (alt.2 - (altAcc (0, 0) Z.toList.reverse).2) k) Z.toList := by
  rw [altAcc_reverse, outList_eq]
  simp only [WP.W9f.nyqOut]
  rw [toList_runSequentialScanSteps, Array.length_toList]
  apply List.map_congr_left
  intro i _
  rw [read1D_eq_getD]

/-- **P3.** The rounding shift as the machine computes it. -/
theorem rnd_eq (x : ℤ) (k : ℕ) (hk : 1 ≤ k) : (x >>> (k - 1) + 1) >>> 1 = divRoundPow2 x k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow]
  unfold divRoundPow2
  rw [if_neg (by omega), Nat.add_sub_cancel]
  have hP : (0 : ℤ) < ((2 ^ m : ℕ) : ℤ) := by positivity
  have e1 : x / ((2 ^ m : ℕ) : ℤ) + 1 = (x + 1 * ((2 ^ m : ℕ) : ℤ)) / ((2 ^ m : ℕ) : ℤ) := by
    rw [Int.add_mul_ediv_right _ _ hP.ne']
  have e2 : ((2 ^ (m + 1) : ℕ) : ℤ) = ((2 ^ m : ℕ) : ℤ) * ((2 ^ 1 : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← pow_add]
  rw [e1, Int.ediv_ediv_of_nonneg hP.le, ← e2, one_mul]

/-! ## P4–P6 -/

/-- **P4.** -/
theorem natAbs_shiftRight_le (x : ℤ) (s : ℕ) : (x >>> s).natAbs ≤ x.natAbs := by
  rw [Int.shiftRight_eq_div_pow]
  exact Int.natAbs_ediv_le_natAbs _ _

/-- **P5.** Accumulator magnitude along any list. -/
theorem altAcc_natAbs_le (A : ℤ × ℤ) (L : List (ℤ × ℤ)) (B : ℕ)
    (hL : ∀ z ∈ L, z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B) :
    (altAcc A L).1.natAbs ≤ A.1.natAbs + L.length * B ∧
      (altAcc A L).2.natAbs ≤ A.2.natAbs + L.length * B := by
  induction L generalizing A with
  | nil => simp [altAcc]
  | cons z L ih =>
    have hz := hL z (List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih (altStep A z) (fun w hw => hL w (List.mem_cons.mpr (Or.inr hw)))
    have h1 : (altStep A z).1.natAbs ≤ z.1.natAbs + A.1.natAbs := Int.natAbs_sub_le _ _
    have h2 : (altStep A z).2.natAbs ≤ z.2.natAbs + A.2.natAbs := Int.natAbs_sub_le _ _
    have e : (z :: L).length * B = L.length * B + B := by
      rw [List.length_cons]
      ring
    show (altAcc (altStep A z) L).1.natAbs ≤ A.1.natAbs + (z :: L).length * B ∧
      (altAcc (altStep A z) L).2.natAbs ≤ A.2.natAbs + (z :: L).length * B
    rw [e]
    omega

/-- **P6.** `bitLen` and powers of two. -/
theorem bitLen_le_of_lt (n w : ℕ) (h : n < 2 ^ w) : bitLen n ≤ w := by
  rw [bitLen, IntMulTM.length_encodeNat]
  exact Nat.size_le.mpr h

theorem lt_of_bitLen_le (n w : ℕ) (h : bitLen n ≤ w) : n < 2 ^ w := by
  rw [bitLen, IntMulTM.length_encodeNat] at h
  exact Nat.size_le.mp h

#assert_std_axioms read1D_eq_getD toList_runSequentialScanSteps gAltTerm_succ gAltTerm_negPair
  sumRangePair_shift sumRangePair_gNeg altAcc_append_singleton altAcc_reverse_eq_altSumL
  sum_alt_getD outList_eq altAcc_reverse nyqOut_toList rnd_eq natAbs_shiftRight_le
  altAcc_natAbs_le bitLen_le_of_lt lt_of_bitLen_le

end WP.W9fNF
