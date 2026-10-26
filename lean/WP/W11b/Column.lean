import WP.W11b.Acs

/-!
# WP.W11b.Column — W9's `ColumnOK` (the W8 Barrett call-site premises) on every column

The dividend bounds come from `W8_numBound_of_widths_holds` at `q = pSub = 2p′`, `w = 4p′`, so
`H = 4p′ + 2p′ + 2 = barrettH pSub`:
* the column input `Y` and the recurrence states fit `4p′` signed bits (`acsV`, i.e. CSWS:1593-1607);
* the multiplier satisfies `0 ≤ c ≤ 2^(pSub+2)` (hC01, FTP:77-78).
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

theorem size_yV_row {p_in pSub t1 r : ℕ} {ft : Array (List ℤ)} {preTw postTw : Array (ℤ × ℤ)}
    {cChild : ComputablePaperFastDFTSpec} {x : Array (ℤ × ℤ)} {u2 : ℕ} (hu2 : u2 < r) :
    ((yV p_in pSub t1 r ft preTw postTw cChild x).getD u2 #[]).size = t1 := by
  unfold yV w9Y
  exact runScan2DWithSteps_row_size _ _ _ _ hu2

theorem fsw_zero (w : ℕ) : FitsSignedWord w ((0 : ℤ), (0 : ℤ)) :=
  ⟨by simp only [abs_zero]; positivity, by simp only [abs_zero]; positivity⟩

theorem fwdBound_of {q pc H n : ℕ} {a c : ℤ} {Y : Array (ℤ × ℤ)} (hH : H = 4 * pc + q + 2)
    (hpc : 1 ≤ 4 * pc) (hc : |c| ≤ (2 : ℤ) ^ (q + 2))
    (hY : ∀ m < n, FitsSignedWord (4 * pc) (read1D Y (m + 1)))
    (hz : ∀ m < n, FitsSignedWord (4 * pc)
      (read1D (buildComputableZPartFwdExact q (a, 0) (c, 0) Y m) m)) :
    IntMulTM.Contracts.W8.zPartFwdBound q H a c Y n := by
  intro m hm
  rw [hH]
  exact IntMulTM.Contracts.W8_numBound_of_widths_holds q (4 * pc) _ _ c hpc (hY m hm) (hz m hm) hc

theorem homBound_of {q pc H n : ℕ} {a c : ℤ} (hH : H = 4 * pc + q + 2)
    (hpc : 1 ≤ 4 * pc) (hc : |c| ≤ (2 : ℤ) ^ (q + 2))
    (hz : ∀ m < n, FitsSignedWord (4 * pc)
      (read1D (buildComputableZHomFwdExact q (a, 0) (c, 0) m) m)) :
    IntMulTM.Contracts.W8.zHomFwdBound q H a c n := by
  intro m hm
  rw [hH]
  exact IntMulTM.Contracts.W8_numBound_of_widths_holds q (4 * pc) _ _ c hpc (fsw_zero _) (hz m hm) hc

theorem nyqBound_of {q pc H n : ℕ} {a : ℤ} {Y : Array (ℤ × ℤ)} (hH : H = 4 * pc + q + 2)
    (hpc : 1 ≤ 4 * pc) (ha : |a| ≤ (2 : ℤ) ^ (q + 2))
    (hY : ∀ m < n, FitsSignedWord (4 * pc) (read1D Y (m + 1)))
    (hz : ∀ m < n, FitsSignedWord (4 * pc)
      (read1D (buildComputableZPartNyqExact q (a, 0) Y m) m)) :
    IntMulTM.Contracts.W8.zPartNyqBound q H a Y n := by
  intro m hm
  rw [hH]
  exact IntMulTM.Contracts.W8_numBound_of_widths_holds q (4 * pc) _ _ a hpc (hY m hm) (hz m hm) ha

theorem columnOK_of {p K t1 r p_in : ℕ} (hsize : t1 * r = 2 ^ K)
    {ft : Array (List ℤ)} {preTw postTw c0T c1T : Array (ℤ × ℤ)}
    {cChild : ComputablePaperFastDFTSpec} {x : Array (ℤ × ℤ)}
    (hacs : AllCallSitesWidthSound p_in
      (.step p (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw c0T c1T cChild) x)
    (hC : ∀ u2 < r, (read1D c0T u2).2 = 0 ∧ (read1D c1T u2).2 = 0 ∧ 0 ≤ (read1D c0T u2).1 ∧
      (read1D c0T u2).1 ≤ (2 : ℤ) ^ (2 * pChild p K + 2) ∧ 0 ≤ (read1D c1T u2).1 ∧
      (read1D c1T u2).1 ≤ (2 : ℤ) ^ (2 * pChild p K + 2))
    (hdiv : ∀ u2 < r,
      0 < IntMulTM.Contracts.W8.columnDivisor r u2 (read1D c0T u2).1 (read1D c1T u2).1) :
    ∀ u2 < r, ColumnOK (2 * pChild p K) t1 r u2 (read1D c0T u2) (read1D c1T u2)
      ((yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x).getD u2 #[])
      (altNodeV p_in (2 * pChild p K) t1 r x) := by
  intro u2 hu2
  obtain ⟨-, -, halt, hY, hsol, -⟩ := acsV p_in p K t1 r ft preTw postTw c0T c1T cChild x hacs
  obtain ⟨h0, h1, hc0lo, hc0hi, hc1lo, hc1hi⟩ := hC u2 hu2
  have hpc12 : 12 ≤ pChild p K := by rw [pChild_eq_additive]; omega
  have hH : barrettH (2 * pChild p K) = 4 * pChild p K + 2 * pChild p K + 2 := by
    unfold barrettH; ring
  have hpc : 1 ≤ 4 * pChild p K := by omega
  have e0 : read1D c0T u2 = ((read1D c0T u2).1, 0) := Prod.ext rfl h0
  have e1 : read1D c1T u2 = ((read1D c1T u2).1, 0) := Prod.ext rfl h1
  have hpos : (0 : ℤ) < (2 : ℤ) ^ (2 * pChild p K + 2) := by positivity
  have habs0 : |(read1D c0T u2).1| ≤ (2 : ℤ) ^ (2 * pChild p K + 2) :=
    abs_le.mpr ⟨by linarith, hc0hi⟩
  have habs1 : |(read1D c1T u2).1| ≤ (2 : ℤ) ^ (2 * pChild p K + 2) :=
    abs_le.mpr ⟨by linarith, hc1hi⟩
  have hYf : ∀ k < t1, FitsSignedWord (4 * pChild p K)
      (read1D ((yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x).getD u2 #[]) k) := by
    intro k hk
    rw [read1D_array_getD_eq_read2D]
    exact hY u2 hu2 k hk
  have hs := hsol u2 hu2
  refine ⟨h0, h1, ?_, hdiv u2 hu2, ?_, ?_, ?_, ?_,
    entryW_of_fitsSignedWord halt (by unfold barrettH; omega), ?_, ?_⟩
  · rw [natLog2Fuel_self]
    exact (two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize).1.symm
  · intro hlt
    refine ⟨fwdBound_of hH hpc habs1 (fun m hm => hYf (m + 1) (by omega)) (fun m hm => ?_),
      homBound_of hH hpc habs1 (fun m hm => ?_)⟩
    · have h := ((hs m (by omega) m le_rfl).1 hlt).1
      rw [e0, e1] at h
      exact h
    · have h := ((hs m (by omega) m le_rfl).1 hlt).2
      rw [e0, e1] at h
      exact h
  · intro heq
    refine nyqBound_of hH hpc habs0 (fun m hm => hYf (m + 1) (by omega)) (fun m hm => ?_)
    have h := (hs m (by omega) m le_rfl).2.1 heq
    rw [e0] at h
    exact h
  · intro hgt
    refine ⟨fwdBound_of hH hpc habs0 (fun m hm => ?_) (fun m hm => ?_),
      homBound_of hH hpc habs0 (fun m hm => ?_)⟩
    · rw [read1D_runBwdRevSteps_eq t1 _ t1 (m + 1) (by omega), if_neg (Nat.succ_ne_zero m)]
      exact hYf _ (by omega)
    · have h := ((hs m (by omega) m le_rfl).2.2.1 hgt).1
      rw [e0, e1] at h
      exact h
    · have h := ((hs m (by omega) m le_rfl).2.2.1 hgt).2
      rw [e0, e1] at h
      exact h
  · refine arrW_of_read1D fun k hk => entryW_of_fitsSignedWord (hYf k ?_) (by unfold barrettH; omega)
    rwa [size_yV_row hu2] at hk
  · have := bitLen_natAbs_le_of_abs_le habs0
    unfold barrettH; omega
  · have := bitLen_natAbs_le_of_abs_le habs1
    unfold barrettH; omega

#assert_std_axioms size_yV_row fsw_zero fwdBound_of homBound_of nyqBound_of columnOK_of

end WP.W11b
