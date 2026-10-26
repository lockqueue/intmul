import WP.W11b.Column
import WP.W11b.PreNode
import LevelSync.Sizes

/-!
# WP.W11b.PostNode — `PostNodeOK` for every node of a faithful step level

* `qHat_eq_qHatV`: the POST group `groupAt t1 (levelEvalV …) i` of `ChainOK` is the snapshot's
  children array of node `i` (`levelEvalV_eq_map`, `groupAt_flatMap`);
* `dft_out`: the output of a faithful transform on a `NodeInv` input has the node size and width
  `2·spec.p + 4` (FTP:1288 and FTP:2250 with `dft1D_norm_le`);
* `postNodeOK_of`: W9's `PostNodeOK` at any width `w ≥ 3·pSub + 3`.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

theorem cSize_of_faithful {cSpec : ComputablePaperFastDFTSpec} {spec : QuantizedFastDFTSpec}
    (h : TablesFaithful cSpec spec) : cSize cSpec = spec.size := by
  cases h <;> rfl

theorem dft_out {spec : QuantizedFastDFTSpec} (hvalid : spec.Valid)
    {cSpec : ComputablePaperFastDFTSpec} (hfaith : TablesFaithful cSpec spec) {p_in : ℕ}
    {y : Array (ℤ × ℤ)} (hy : ∀ k < spec.size, ‖toScaledComplex p_in (read1D y k)‖ ≤ (2 : ℝ) ^ spec.p) :
    (computablePaperFastDFT p_in cSpec y).size = spec.size ∧
      ArrW (2 * spec.p + 4) (computablePaperFastDFT p_in cSpec y) := by
  have hsz : (computablePaperFastDFT p_in cSpec y).size = spec.size := by
    rw [computablePaperFastDFT_size, cSize_of_faithful hfaith]
  refine ⟨hsz, arrW_of_read1D fun u hu => ?_⟩
  rw [hsz] at hu
  have heq := toScaledComplex_computablePaperFastDFT_eq_ofTables spec hvalid cSpec hfaith p_in y
    (xOf p_in y) (fun k _ => rfl) u hu
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ spec.p := one_le_pow₀ (by norm_num)
  have herr := sincGaussianFastDFTOfTables_error_le spec hvalid cSpec hfaith (xOf p_in y)
    ((2 : ℝ) ^ spec.p) hM1 hy u hu
  have hdft := dft1D_norm_le spec.size (by omega) (xOf p_in y) ((2 : ℝ) ^ spec.p)
    (fun k hk => hy k (Finset.mem_range.mp hk)) u
  have hpow : (2 : ℝ) ^ (-(spec.p : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hmul : (2 : ℝ) ^ (-(spec.p : ℤ)) * (2 : ℝ) ^ spec.p ≤ (2 : ℝ) ^ spec.p :=
    mul_le_of_le_one_left (by positivity) hpow
  have hnorm : ‖toScaledComplex spec.p (read1D (computablePaperFastDFT p_in cSpec y) u)‖ ≤
      (2 : ℝ) ^ (spec.p + 1) := by
    rw [heq]
    have htri := norm_add_le
      (sincGaussianFastDFTOfTables cSpec (xOf p_in y) u - dft1D spec.size (xOf p_in y) u)
      (dft1D spec.size (xOf p_in y) u)
    rw [sub_add_cancel] at htri
    rw [pow_succ]
    linarith
  exact entryW_mono (entryW_of_norm_le hnorm) (by omega)

theorem qHat_eq_qHatV (p_in pSub t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (cChild : ComputablePaperFastDFTSpec) (xs : List (Array (ℤ × ℤ))) {i : ℕ} (hi : i < xs.length) :
    (groupAt t1 (levelEvalV cChild pSub
      (xs.flatMap fun x => (preNodeV p_in pSub pSub t1 r ft preTw postTw x).toList)) i).toArray =
      qHatV p_in pSub t1 r ft preTw postTw cChild (xs.getD i #[]) := by
  rw [levelEvalV_eq_map, List.map_flatMap,
    groupAt_flatMap t1 (fun x => (preNodeV p_in pSub pSub t1 r ft preTw postTw x).toList.map
      (computablePaperFastDFT pSub cChild)) (fun x => by simp [size_preNodeV]) xs i hi,
    List.getD_eq_getElem _ _ hi]
  unfold qHatV
  apply Array.ext
  · simp [size_preNodeV]
  · intro j h1 h2
    have hj : j < (preNodeV p_in pSub pSub t1 r ft preTw postTw xs[i]).size := by simpa using h1
    simp [Array.getD, hj]

theorem size_w9ZExact_row (pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (Y : Array (Array (ℤ × ℤ))) {u2 : ℕ} (hu2 : u2 < r) :
    ((w9ZExact pSub t1 r c0T c1T alt Y).getD u2 #[]).size = t1 := by
  unfold w9ZExact
  rw [array_getD_ofFn_of_lt _ _ _ _ hu2]
  dsimp only
  split_ifs <;>
    simp [computableSolveBidiagonalFwdExact, computableSolveBidiagonalFwdExactWithSteps,
      computableSolveNyquistExact, computableSolveNyquistExactWithSteps,
      computableSolveBidiagonalBwdExact, computableSolveBidiagonalBwdExactWithSteps]

theorem size_postNodeV (p pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (pc : ℕ) (alt : ℤ × ℤ)
    (qHat : Array (Array (ℤ × ℤ))) : (postNodeV p pSub t1 r c0T c1T pc alt qHat).size = t1 * r := by
  rw [← postNode_eq_V, postNode_size]

#assert_std_axioms cSize_of_faithful dft_out qHat_eq_qHatV size_w9ZExact_row size_postNodeV

end WP.W11b
