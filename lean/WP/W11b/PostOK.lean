import WP.W11b.PostNode

/-!
# WP.W11b.PostOK — W9's `PostNodeOK` for one node of a faithful step level

Every matrix of the POST kernel has entries of width `≤ w` (`w ≥ 3·pSub + 3`):
* the children outputs `qHat` by `dft_out` on the children's node invariant (`preNode_children`);
* their transpose `w9QHatT` by `arrW_transpose`/`entryW_flatten` (data movement);
* `Y`, the solver outputs and the node output by the snapshot certificate (`acsV`);
* the column premises by `columnOK_of`.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

theorem size_w9Out (p pSub t1 r : ℕ) (Zc : Array (Array (ℤ × ℤ))) :
    (w9Out p pSub t1 r Zc).size = t1 * r := by
  unfold w9Out
  simp [size_runSequentialScanSteps]

theorem postNodeOK_of {p K t1 r c1 p_in w : ℕ} {child : QuantizedFastDFTSpec}
    (hchild : child.Valid) (hchild_size : child.size = r) (hchild_p : child.p = pChild p K)
    (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K) (hc1 : c1 * t1 = r)
    {ft : Array (List ℤ)} {preTw postTw c0T c1T : Array (ℤ × ℤ)}
    {cChild : ComputablePaperFastDFTSpec} (hchild_faith : TablesFaithful cChild child)
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      ft.getD j1 [] =
        (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
              (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
            G s) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
      (∀ s < 2 * (2 * pChild p K) + 1, (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
    (hPre : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D preTw k2) - zetaRoot r (k2 : ℝ)‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (hPost : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D postTw k2) - zetaRoot r (-(k2 : ℝ))‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (hC : ∀ u2 < r, (read1D c0T u2).2 = 0 ∧ (read1D c1T u2).2 = 0 ∧ 0 ≤ (read1D c0T u2).1 ∧
      (read1D c0T u2).1 ≤ (2 : ℤ) ^ (2 * pChild p K + 2) ∧ 0 ≤ (read1D c1T u2).1 ∧
      (read1D c1T u2).1 ≤ (2 : ℤ) ^ (2 * pChild p K + 2))
    (hdiv : ∀ u2 < r,
      0 < IntMulTM.Contracts.W8.columnDivisor r u2 (read1D c0T u2).1 (read1D c1T u2).1)
    (hw2 : 3 * (2 * pChild p K) + 3 ≤ w) {x : Array (ℤ × ℤ)}
    (hx : ∀ k < t1 * r, ‖toScaledComplex p_in (read1D x k)‖ ≤ (2 : ℝ) ^ p)
    (hacs : AllCallSitesWidthSound p_in
      (.step p (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw c0T c1T cChild) x) :
    PostNodeOK w ⟨p, 2 * pChild p K, t1, r, cChild.p⟩ c0T c1T (altNodeV p_in (2 * pChild p K) t1 r x)
      (qHatV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x) := by
  obtain ⟨-, -, halt, hY, hsol, hout⟩ := acsV p_in p K t1 r ft preTw postTw c0T c1T cChild x hacs
  have h4 : ∀ z, FitsSignedWord (4 * pChild p K) z → EntryW w z :=
    fun z hz => entryW_of_fitsSignedWord hz (by omega)
  have hch := preNode_children ht1 hr hsize hc1 hTaps hPre hPost hx
  have hpc12 : 12 ≤ pChild p K := by rw [pChild_eq_additive]; omega
  have hqHat : MatW w (qHatV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x) := by
    unfold qHatV
    refine matW_ofFn fun v1 => ?_
    have hy := hch v1.val v1.isLt
    have hd := dft_out hchild hchild_faith (p_in := 2 * pChild p K)
      (y := (preNodeV p_in (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw x).getD v1.val #[])
      (fun k hk => by rw [hchild_p]; exact hy.2 k (hchild_size ▸ hk))
    exact arrW_mono hd.2 (by rw [hchild_p]; omega)
  refine ⟨hqHat, ?_, ?_, columnOK_of hsize hacs hC hdiv, ?_, h4 _ halt, ?_⟩
  · unfold w9QHatT
    exact arrW_transpose _ _ fun k => entryW_flatten hr hqHat _ k
  · show MatW w (yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x)
    unfold yV w9Y
    exact matW_scan_of_read2D fun i hi j hj => h4 _ (hY i hi j hj)
  · refine matW_of_read2D fun i hi j hj => ?_
    have hi' : i < r := by simpa [w9ZExact] using hi
    have hj' : j < t1 := by rwa [size_w9ZExact_row _ _ _ _ _ _ _ hi'] at hj
    exact entryW_of_fitsSignedWord (hsol i hi' j hj' j le_rfl).2.2.2
      (le_min (by omega) (by simp only [PostHdr.H, barrettH]; omega))
  · rw [postNodeV_eq_phases]
    refine arrW_of_read1D fun u hu => h4 _ (hout u ?_)
    rwa [size_w9Out] at hu

#assert_std_axioms size_w9Out postNodeOK_of

end WP.W11b
