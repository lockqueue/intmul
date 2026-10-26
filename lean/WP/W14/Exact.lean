import WP.W14.Admissible

/-!
# W14: exact multiplication at any admissible schedule

`computablePaperFastDFTMultiplyAt_faithful_eq_mul` is FTP:2304
(`computablePaperFastDFTMultiply_faithful_eq_mul`) for the schedule-parametric multiplier
`computablePaperFastDFTMultiplyAt S.qLeaf` and tables faithful at `S`; the proof is the snapshot's,
with the multi-level error bound supplied by `sincGaussianFastDFTOfTablesAt_error_le` and the
integer-to-complex bridge by `toScaledComplex_computablePaperFastDFTAt_eq`.
-/

namespace WP.W14

open IntMul Complex Real

attribute [local instance 10000] instZeroIntElementary

/-- **Exact multiplication at an admissible schedule** (FTP:2304 generalized). -/
theorem computablePaperFastDFTMultiplyAt_faithful_eq_mul
    (S : StepSchedule) (P : ℕ → ℕ → Prop) (hS : Admissible S P)
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hP : StepsSatisfy P spec)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithfulAt S cSpec spec)
    (b K0 k1 k2 : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    computablePaperFastDFTMultiplyAt S.qLeaf cSpec b K0 k1 k2 A B = A * B := by
  unfold computablePaperFastDFTMultiplyAt computablePaperFastDFTMultiplyAtWithProgramCost
  dsimp only [runSequentialScanCostedSteps, costedGMulScaled, costedDivRoundRatInt]
  rw [reconstructChunksTreeWithProgramCost_fst, reconstructChunksTree_eq_reconstructChunks,
      splitChunksTreeWithProgramCost_fst, splitChunksTreeWithProgramCost_fst]
  set xs := splitChunks b k1 A
  set ys := splitChunks b k2 B
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set x_AB := packNormalizedChunks b k1 k2 A B
  set asArr := (splitChunksTree b k1 A).toArray
  set bsArr := (splitChunksTree b k2 B).toArray
  set stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  set fwd := computablePaperFastDFTAt S.qLeaf b cSpec stPack.outTape
  set stSq := runSequentialScanSteps (fun u =>
    gConj (gMulScaled (p0 + 2) (read1D fwd.1 u) (read1D fwd.1 u))) R0
  set inv := computablePaperFastDFTAt S.qLeaf p0 cSpec stSq.outTape
  set numScale : ℤ := ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ)
  set denScale : ℤ := 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ)
  set stExt := runSequentialScanSteps (fun j =>
    let imInt : ℤ := -(read1D inv.1 j).2
    let d := divRoundRatInt (imInt * numScale) denScale
    d.toNat) R0
  have hmap :
      (List.range (k1 + k2)).map (fun j => read1D stExt.outTape j) =
      (List.range (k1 + k2)).map (fun j => (polyMulList xs ys).getD j 0) := by
    refine List.map_congr_left fun j hj_mem => ?_
    have hj_lt : j < k1 + k2 := List.mem_range.mp hj_mem
    have hj_R0 : j < R0 := by dsimp [R0]; omega
    rw [read1D_runSequentialScanSteps_eq _ R0 j hj_R0]
    have hy : ∀ u < R0, toScaledComplex p0 (read1D fwd.1 u) =
        sincGaussianFastDFTOfTablesAt S.qLeaf cSpec x_AB u := by
      intro u hu
      rw [← hp0]
      exact toScaledComplex_computablePaperFastDFTAt_eq S spec hvalid cSpec hfaith b
        stPack.outTape x_AB
        (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k
          (hsize ▸ hk)).symm)
        u (hsize.symm ▸ hu)
    have hsConj : ∀ u < spec.size,
        star (complexQuantize p0 ((sincGaussianFastDFTOfTablesAt S.qLeaf cSpec x_AB u) ^ 2)) =
          toScaledComplex p0 (read1D stSq.outTape u) := by
      intro u hu
      have hu_R0 : u < R0 := hsize ▸ hu
      dsimp only [stSq]
      rw [read1D_runSequentialScanSteps_eq _ R0 u hu_R0, toScaledComplex_gConj,
          toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u hu_R0, sq]
    have hz : toScaledComplex p0 (read1D inv.1 j) =
        sincGaussianFastDFTOfTablesAt S.qLeaf cSpec
          (fun u => star (complexQuantize p0
            ((sincGaussianFastDFTOfTablesAt S.qLeaf cSpec x_AB u) ^ 2))) j := by
      have h := toScaledComplex_computablePaperFastDFTAt_eq S spec hvalid cSpec hfaith p0
        stSq.outTape
        (fun u => star (complexQuantize p0
          ((sincGaussianFastDFTOfTablesAt S.qLeaf cSpec x_AB u) ^ 2)))
        hsConj j (hsize.symm ▸ hj_R0)
      rwa [hp0] at h
    have hzim :
        (star (sincGaussianFastDFTOfTablesAt S.qLeaf cSpec
          (fun u => star (complexQuantize p0
            ((sincGaussianFastDFTOfTablesAt S.qLeaf cSpec x_AB u) ^ 2))) j)).im =
        ((-(read1D inv.1 j).2 : ℤ) : ℝ) / (2 : ℝ) ^ (p0 + 2) := by
      rw [← hz, ← toScaledComplex_gConj]
      simp [toScaledComplex, gConj]
    have hden_pos : (0 : ℤ) < 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ) := by positivity
    dsimp only [numScale, denScale]
    rw [divRoundRatInt_eq_floor _ _ hden_pos]
    have hfloor_eq :
        ⌊(((-(read1D inv.1 j).2 : ℤ) * ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ) : ℤ) : ℝ) /
            ((2 * ((2 ^ (p0 + 2) : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2⌋ =
        ⌊(star (sincGaussianFastDFTOfTablesAt S.qLeaf cSpec
          (fun u => star (complexQuantize p0
            ((sincGaussianFastDFTOfTablesAt S.qLeaf cSpec x_AB u) ^ 2))) j)).im *
          (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) + (1 / 2 : ℝ)⌋ := by
      rw [hzim]
      congr 2
      have hzpow :
          (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) =
            (((2 ^ (2 * b + 2 * K0) : ℕ) : ℝ) / 2) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        have hcast : (2 : ℤ) * (b : ℤ) + 2 * (K0 : ℤ) = ((2 * b + 2 * K0 : ℕ) : ℤ) := by
          push_cast; ring
        rw [hcast, zpow_natCast]; push_cast; rfl
      rw [hzpow]
      have hpow_ne : (2 : ℝ) ^ (p0 + 2) ≠ 0 := by positivity
      push_cast
      field_simp [hpow_ne]
    rw [hfloor_eq]
    have hround := dftApproxConvApprox_round_eq (sincGaussianFastDFTOfTablesAt S.qLeaf cSpec)
      b K0 k1 k2 A B
      (fun x' M' hM1' hx' u' hu' => by
        have herr := sincGaussianFastDFTOfTablesAt_error_le S P hS spec hvalid hP cSpec hfaith
          x' M' hM1' (by rwa [hsize]) u' (by rwa [hsize])
        rwa [hsize, hp0] at herr)
      hk j hj_R0
    dsimp only at hround
    rw [hround, Int.toNat_natCast]
  have hpoly_len : (polyMulList xs ys).length ≤ k1 + k2 := by
    have := length_polyMulList_le xs ys
    rw [length_splitChunks, length_splitChunks] at this
    exact this
  rw [hmap, reconstructChunks_eq_evalRadix, evalRadix_range_getD (2 ^ b) _ (k1 + k2) hpoly_len,
      ← reconstructChunks_eq_evalRadix]
  exact reconstructChunks_polyMulList_splitChunks b k1 k2 A B hA hB

#assert_std_axioms computablePaperFastDFTMultiplyAt_faithful_eq_mul

end WP.W14
