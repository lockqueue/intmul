import WP.W11b.Acs
import WP.W11b.PreEq

/-!
# WP.W11b.PreNode — `PreNodeOK` and the children's node invariant

For a node `x` of a faithful step level with `NodeInv`:
* `preNodeOK_of`: W9's `PreNodeOK` at any width `w ≥ max (p + p_in + 3) (3·pSub + 3)`. The phase
  widths come from the snapshot certificate (`acsV`), the input widths from the norm bound, and
  `SpreadStrideOK` from `W8_staticStride_sixP_holds`;
* `preNode_children`: every child input (row of `preNodeV`) has `r` entries and dequantizes to
  magnitudes `≤ 2^(pChild p K)` (FTP:1096 through `qPost_eq_w9`).
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

theorem size_preNodeV (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : (preNodeV p_in pSub m1 t1 r ft preTw postTw x).size = t1 := by
  rw [← preNode_eq_V, preNode_size]

theorem row_preNodeV (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) {v1 : ℕ} (hv1 : v1 < t1) :
    ((preNodeV p_in pSub m1 t1 r ft preTw postTw x).getD v1 #[]).size = r := by
  rw [← preNode_eq_V, preNode_row_size _ _ _ _ _ _ _ _ _ _ hv1]

theorem matW_scan_of_read2D {w n1 n2 : ℕ} {f : ℕ → ℕ → ℤ × ℤ}
    (h : ∀ i < n1, ∀ j < n2, EntryW w (read2D (runScan2DWithSteps n1 n2 f).1 i j)) :
    MatW w (runScan2DWithSteps n1 n2 f).1 := by
  refine matW_of_read2D fun i hi j hj => ?_
  have hi' : i < n1 := by rwa [runScan2DWithSteps_fst_size] at hi
  have hj' : j < n2 := by rwa [runScan2DWithSteps_row_size _ _ _ _ hi'] at hj
  exact h i hi' j hj'

theorem arrW_input {w p p_in N : ℕ} {x : Array (ℤ × ℤ)} (hxs : x.size = N)
    (hx : ∀ k < N, ‖toScaledComplex p_in (read1D x k)‖ ≤ (2 : ℝ) ^ p) (hw : p + p_in + 3 ≤ w) :
    ArrW w x :=
  arrW_of_read1D fun k hk => entryW_mono (entryW_of_norm_le (hx k (hxs ▸ hk))) hw

theorem preNodeOK_of {p K t1 r p_in w : ℕ} (hp : 8 ≤ p) (hK : 2 ≤ K) (hr : 0 < r)
    (hsize : t1 * r = 2 ^ K) {ft : Array (List ℤ)} {preTw postTw c0T c1T : Array (ℤ × ℤ)}
    {cChild : ComputablePaperFastDFTSpec}
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
    (hw1 : p + p_in + 3 ≤ w) (hw2 : 3 * (2 * pChild p K) + 3 ≤ w)
    {x : Array (ℤ × ℤ)} (hxs : x.size = t1 * r)
    (hx : ∀ k < t1 * r, ‖toScaledComplex p_in (read1D x k)‖ ≤ (2 : ℝ) ^ p)
    (hacs : AllCallSitesWidthSound p_in
      (.step p (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw c0T c1T cChild) x) :
    PreNodeOK w ⟨p_in, 2 * pChild p K, 2 * pChild p K, t1, r⟩ ft preTw postTw x := by
  obtain ⟨hUP, hQq, halt, -, -, -⟩ := acsV p_in p K t1 r ft preTw postTw c0T c1T cChild x hacs
  have hxw : ArrW w x := arrW_input hxs hx hw1
  have h6 : ∀ z, FitsSignedWord (6 * pChild p K) z → EntryW w z :=
    fun z hz => entryW_of_fitsSignedWord hz (by omega)
  have h4 : ∀ z, FitsSignedWord (4 * pChild p K) z → EntryW w z :=
    fun z hz => entryW_of_fitsSignedWord hz (by omega)
  refine ⟨hxw, matW_w9XRows hxw, ?_, ?_, ?_, ?_, h4 _ halt, ?_⟩
  · refine matW_of_read2D fun i hi j hj => ?_
    have hi' : i < t1 := by simpa [w9U] using hi
    have hj' : j < r := by
      have h := hj
      unfold w9U at h
      rwa [array_getD_ofFn_of_lt _ _ _ _ hi', size_spreadRow] at h
    exact h6 _ (hUP i hi' j hj').1
  · unfold w9P
    exact matW_scan_of_read2D fun i hi j hj => h4 _ (hUP i hi j hj).2
  · unfold w9Q
    exact matW_scan_of_read2D fun i hi j hj => h4 _ (hQq i hi j hj).1
  · refine matW_of_read2D fun i hi j hj => ?_
    have hi' : i < t1 := by rwa [size_preNodeV] at hi
    have hj' : j < r := by rwa [row_preNodeV _ _ _ _ _ _ _ _ _ hi'] at hj
    exact h4 _ (hQq i hi' j hj').2
  · intro j1 hj1 b _
    obtain ⟨G, hFold, -, hG⟩ := hTaps j1 hj1
    have hpc : p ≤ pChild p K := by rw [pChild_eq_additive]; omega
    have hb := IntMulTM.Contracts.W8_staticStride_sixP_holds p K t1 r hp hK hr (ft.getD j1 []) G hFold hG p_in
      ((w9XRows t1 r x).getD j1 #[]) (xOf p_in x) j1 hj1
      (fun k hk => (hx k hk).trans (pow_le_pow_right₀ (by norm_num) hpc))
      (hxRow_w9 K hsize hr p_in x j1 hj1) b
    have hs : 6 * pChild p K ≤ PreHdr.s ⟨p_in, 2 * pChild p K, 2 * pChild p K, t1, r⟩ := by
      simp only [PreHdr.s, strideOf]
      omega
    exact ⟨hb.1.trans hs, hb.2.trans hs⟩

theorem preNode_children {p K t1 r c1 p_in : ℕ} (ht1 : 0 < t1) (hr : 0 < r)
    (hsize : t1 * r = 2 ^ K) (hc1 : c1 * t1 = r) {ft : Array (List ℤ)}
    {preTw postTw : Array (ℤ × ℤ)}
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
    {x : Array (ℤ × ℤ)}
    (hx : ∀ k < t1 * r, ‖toScaledComplex p_in (read1D x k)‖ ≤ (2 : ℝ) ^ p) :
    ∀ v1 < t1,
      ((preNodeV p_in (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw x).getD v1 #[]).size = r ∧
      ∀ k < r, ‖toScaledComplex (2 * pChild p K)
        (read1D ((preNodeV p_in (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw x).getD v1 #[]) k)‖ ≤
          (2 : ℝ) ^ (pChild p K) := by
  intro v1 hv1
  refine ⟨row_preNodeV _ _ _ _ _ _ _ _ _ hv1, fun k hk => ?_⟩
  rw [read1D_array_getD_eq_read2D, qPost_eq_w9 K hsize ht1 hr hc1 p_in _ ft preTw postTw x v1 hv1 k hk]
  exact norm_qPost_of_faithful_le_two_pow_pChild p K t1 r ht1 hr hsize ft preTw postTw hTaps hPre hPost
    (xOf p_in x) hx v1 k hk

#assert_std_axioms size_preNodeV row_preNodeV matW_scan_of_read2D arrW_input preNodeOK_of
  preNode_children

end WP.W11b
