import IntMul.ExecutableAlgorithm.IntrinsicScheduleAndCost

namespace IntMul

/-- For any `0 < r` and `m1 : ℕ`, `1 ≤ effectiveFilterWidth m1 r`. -/
theorem one_le_effectiveFilterWidth (m1 r : ℕ) (hr : 0 < r) :
    1 ≤ effectiveFilterWidth m1 r := by
  unfold effectiveFilterWidth
  omega

/-- For any `r : ℕ` and `p' ≤ P`, with `W_eff = effectiveFilterWidth (2 * p') r`,
`Nat.log2 (W_eff * (6 * p')) + 1 ≤ 7 * (Nat.log2 P + 1)`. -/
theorem log2_effectiveFilterWidth_mul_six_succ_le
    (r p' P : ℕ) (hp' : p' ≤ P) :
    Nat.log2 (effectiveFilterWidth (2 * p') r * (6 * p')) + 1 ≤
      7 * (Nat.log2 P + 1) := by
  set W_eff := effectiveFilterWidth (2 * p') r
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · have hp0 : p' = 0 := by omega
    subst hp0
    simp
  · by_cases hne : W_eff * (6 * p') = 0
    · rw [hne]
      simp
      omega
    · have hW_le : W_eff ≤ 5 * P := by
        have hfull : W_eff ≤ 2 * (2 * p') + 1 := effectiveFilterWidth_le_full (2 * p') r
        omega
      have h6_le : 6 * p' ≤ 6 * P := by omega
      have hprod_le : W_eff * (6 * p') ≤ 30 * (P * P) := by
        calc W_eff * (6 * p')
            ≤ (5 * P) * (6 * P) := Nat.mul_le_mul hW_le h6_le
          _ = 30 * (P * P) := by ring
      set Q := 2 ^ (Nat.log2 P + 1)
      have hP_lt : P < Q := lt_two_pow_log2_succ P
      have hPQ : (P + 1) * (P + 1) ≤ Q * Q := Nat.mul_le_mul hP_lt hP_lt
      have h30_lt : 30 * (P * P) < 32 * (Q * Q) := by nlinarith
      have hpow_combine : 32 * (Q * Q) = 2 ^ (2 * Nat.log2 P + 7) := by
        have h32 : (32 : ℕ) = 2 ^ 5 := by decide
        dsimp [Q]
        rw [h32, ← pow_add, ← pow_add]
        congr 1
        ring
      have hlt_pow : W_eff * (6 * p') < 2 ^ (2 * Nat.log2 P + 7) := by
        rw [← hpow_combine]
        exact hprod_le.trans_lt h30_lt
      have hlog_lt : Nat.log2 (W_eff * (6 * p')) < 2 * Nat.log2 P + 7 :=
        (Nat.log2_lt hne).mpr hlt_pow
      omega

/-- For any `r : ℕ` and `p' ≤ P`, with `W_eff = effectiveFilterWidth (2 * p') r`,
`Nat.log2 (Nat.log2 (W_eff * (6 * p')) + 1) + 1 ≤ 4 * (Nat.log2 (Nat.log2 P + 1) + 1)`. -/
theorem log2_log2_effectiveFilterWidth_mul_six_succ_le
    (r p' P : ℕ) (hp' : p' ≤ P) :
    Nat.log2 (Nat.log2 (effectiveFilterWidth (2 * p') r * (6 * p')) + 1) + 1 ≤
      4 * (Nat.log2 (Nat.log2 P + 1) + 1) := by
  have h1 := log2_effectiveFilterWidth_mul_six_succ_le r p' P hp'
  have h2 : 7 * (Nat.log2 P + 1) < 2 ^ (Nat.log2 (Nat.log2 P + 1) + 4) := by
    have hlt := lt_two_pow_log2_succ (Nat.log2 P + 1)
    have hpow : 2 ^ (Nat.log2 (Nat.log2 P + 1) + 4) = 8 * 2 ^ (Nat.log2 (Nat.log2 P + 1) + 1) := by ring
    omega
  have h3 := (Nat.log2_lt (by omega)).mpr (h1.trans_lt h2)
  omega

/-- For any `p' ≤ P`, `mulBitCost (4 * p') ≤ 36 * subMulRate P`. -/
theorem mulBitCost_four_mul_le (p' P : ℕ) (hp' : p' ≤ P) :
    mulBitCost (4 * p') ≤ 36 * subMulRate P := by
  unfold mulBitCost subMulRate
  rcases Nat.eq_zero_or_pos p' with rfl | hp'_pos
  · simp
  · have hP_lt : P < 2 ^ (Nat.log2 P + 1) := lt_two_pow_log2_succ P
    have h4p_lt : 4 * p' < 2 ^ (Nat.log2 P + 3) := by
      have hpow : 2 ^ (Nat.log2 P + 3) = 4 * 2 ^ (Nat.log2 P + 1) := by ring
      omega
    have hlog_lt : Nat.log2 (4 * p') < Nat.log2 P + 3 :=
      (Nat.log2_lt (by omega)).mpr h4p_lt
    have hlog_le : Nat.log2 (4 * p') + 1 ≤ 3 * (Nat.log2 P + 1) := by omega
    have hLL_lt : Nat.log2 P + 1 < 2 ^ (Nat.log2 (Nat.log2 P + 1) + 1) :=
      lt_two_pow_log2_succ (Nat.log2 P + 1)
    have h3LL_lt : Nat.log2 (4 * p') + 1 < 2 ^ (Nat.log2 (Nat.log2 P + 1) + 3) := by
      have hpow : 2 ^ (Nat.log2 (Nat.log2 P + 1) + 3) = 4 * 2 ^ (Nat.log2 (Nat.log2 P + 1) + 1) := by ring
      omega
    have hllog_lt : Nat.log2 (Nat.log2 (4 * p') + 1) < Nat.log2 (Nat.log2 P + 1) + 3 :=
      (Nat.log2_lt (by omega)).mpr h3LL_lt
    have hllog_le : Nat.log2 (Nat.log2 (4 * p') + 1) + 1 ≤ 3 * (Nat.log2 (Nat.log2 P + 1) + 1) := by omega
    have h4p_le : 4 * p' ≤ 4 * P := by omega
    calc 4 * p' * (Nat.log2 (4 * p') + 1) * (Nat.log2 (Nat.log2 (4 * p') + 1) + 1)
        ≤ (4 * P) * (3 * (Nat.log2 P + 1)) * (3 * (Nat.log2 (Nat.log2 P + 1) + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul h4p_le hlog_le) hllog_le
      _ = 36 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)) := by ring

/-- For any `p' ≤ P`, `addBitCost (4 * p') ≤ 4 * subMulRate P`. -/
theorem addBitCost_four_mul_le (p' P : ℕ) (hp' : p' ≤ P) :
    addBitCost (4 * p') ≤ 4 * subMulRate P := by
  unfold addBitCost subMulRate
  calc 4 * p' = (4 * p') * 1 * 1 := by ring
    _ ≤ (4 * P) * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    _ = 4 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)) := by ring

/-- For any `t1, r : ℕ` and `p' ≤ P`,
`kroneckerSpreadStepBitCost t1 r p' ≤ (t1 * r) * (720 * subMulRate P)`. -/
theorem kroneckerSpreadStepBitCost_le (t1 r p' P : ℕ) (hp' : p' ≤ P) :
    kroneckerSpreadStepBitCost t1 r p' ≤
      (t1 * r) * (720 * subMulRate P) := by
  unfold kroneckerSpreadStepBitCost mulBitCost addBitCost subMulRate
  dsimp only
  set W_eff := effectiveFilterWidth (2 * p') r
  set numBlocks := kroneckerSpreadNumBlocks (2 * p') r
  have hlog := log2_effectiveFilterWidth_mul_six_succ_le r p' P hp'
  have hllog := log2_log2_effectiveFilterWidth_mul_six_succ_le r p' P hp'
  have h6p : 6 * p' ≤ 6 * P := by omega
  have hmul_part :
      2 * (W_eff * (6 * p') * (Nat.log2 (W_eff * (6 * p')) + 1) *
        (Nat.log2 (Nat.log2 (W_eff * (6 * p')) + 1) + 1)) ≤
        W_eff * (336 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) := by
    calc 2 * (W_eff * (6 * p') * (Nat.log2 (W_eff * (6 * p')) + 1) *
          (Nat.log2 (Nat.log2 (W_eff * (6 * p')) + 1) + 1))
        ≤ 2 * (W_eff * (6 * P) * (7 * (Nat.log2 P + 1)) * (4 * (Nat.log2 (Nat.log2 P + 1) + 1))) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left W_eff h6p) hlog) hllog)
      _ = W_eff * (336 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) := by ring
  have hadd_part :
      4 * W_eff * (6 * p') ≤
        W_eff * (24 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) := by
    calc 4 * W_eff * (6 * p')
        = W_eff * (24 * (p' * 1 * 1)) := by ring
      _ ≤ W_eff * (24 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) :=
          Nat.mul_le_mul_left W_eff
            (Nat.mul_le_mul_left 24 (Nat.mul_le_mul (Nat.mul_le_mul hp' (by omega)) (by omega)))
  have hblock_inner :
      2 * (W_eff * (6 * p') * (Nat.log2 (W_eff * (6 * p')) + 1) *
        (Nat.log2 (Nat.log2 (W_eff * (6 * p')) + 1) + 1)) + 4 * W_eff * (6 * p') ≤
        W_eff * (360 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) := by
    calc 2 * (W_eff * (6 * p') * (Nat.log2 (W_eff * (6 * p')) + 1) *
          (Nat.log2 (Nat.log2 (W_eff * (6 * p')) + 1) + 1)) + 4 * W_eff * (6 * p')
        ≤ W_eff * (336 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) +
          W_eff * (24 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) :=
          Nat.add_le_add hmul_part hadd_part
      _ = W_eff * (360 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) := by ring
  have hnumW : numBlocks * W_eff ≤ 2 * r :=
    kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le (2 * p') r
  calc t1 * numBlocks *
        (2 * (W_eff * (6 * p') * (Nat.log2 (W_eff * (6 * p')) + 1) *
          (Nat.log2 (Nat.log2 (W_eff * (6 * p')) + 1) + 1)) + 4 * W_eff * (6 * p'))
      ≤ t1 * numBlocks * (W_eff * (360 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)))) :=
        Nat.mul_le_mul_left (t1 * numBlocks) hblock_inner
    _ = t1 * (numBlocks * W_eff) * (360 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) := by ring
    _ ≤ t1 * (2 * r) * (360 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left t1 hnumW)
    _ = (t1 * r) * (720 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) := by ring

/-- For any `t1, r : ℕ` and `p' ≤ P`,
`twistAndSolverStepBitCost t1 r p' ≤ (t1 * r) * (640 * subMulRate P)`. -/
theorem twistAndSolverStepBitCost_le (t1 r p' P : ℕ) (hp' : p' ≤ P) :
    twistAndSolverStepBitCost t1 r p' ≤
      (t1 * r) * (640 * subMulRate P) := by
  unfold twistAndSolverStepBitCost
  have hmul := mulBitCost_four_mul_le p' P hp'
  have hadd := addBitCost_four_mul_le p' P hp'
  have hinner : 16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p') ≤ 640 * subMulRate P := by
    calc 16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')
        ≤ 16 * (36 * subMulRate P) + 16 * (4 * subMulRate P) :=
          Nat.add_le_add (Nat.mul_le_mul_left 16 hmul) (Nat.mul_le_mul_left 16 hadd)
      _ = 640 * subMulRate P := by ring
  exact Nat.mul_le_mul_left (t1 * r) hinner

/-- Exact closed form for `recursiveTransposeTapeCost r p' m`:
`recursiveTransposeTapeCost r p' m = sequentialTransposeBitCost (2 ^ m) r p'`. -/
theorem recursiveTransposeTapeCost_eq (r p' m : ℕ) :
    recursiveTransposeTapeCost r p' m = sequentialTransposeBitCost (2 ^ m) r p' := by
  unfold sequentialTransposeBitCost sequentialPassBitCost addBitCost
  rw [nat_log2_two_pow m, sequentialTapeTransposeWithPasses_snd]
  induction m with
  | zero =>
    dsimp [recursiveTransposeTapeCost]
    ring
  | succ m ih =>
    dsimp [recursiveTransposeTapeCost, sequentialPassBitCost, addBitCost]
    rw [ih]
    ring

/-- Exact closed form for `recursiveMergeSortTapeCost r p' m`:
`recursiveMergeSortTapeCost r p' m = sequentialColumnMergeSortBitCost (2 ^ m) r p'`. -/
theorem recursiveMergeSortTapeCost_eq (r p' m : ℕ) :
    recursiveMergeSortTapeCost r p' m = sequentialColumnMergeSortBitCost (2 ^ m) r p' := by
  unfold sequentialColumnMergeSortBitCost sequentialPassBitCost addBitCost
  rw [nat_log2_two_pow m, sequentialAffineOddRouteWithPasses_snd]
  induction m with
  | zero =>
    dsimp [recursiveMergeSortTapeCost]
    ring
  | succ m ih =>
    dsimp [recursiveMergeSortTapeCost, sequentialPassBitCost, addBitCost]
    rw [ih]
    ring

/-- For any `K : ℕ` and `p' ≤ P`, with `t1 = 2 ^ (K / 2)` and `r = 2 ^ (K - K / 2)`,
`routingAndStreamingStepBitCost t1 r p' ≤ 2 ^ K * (32 * K * P) + 2 ^ K * (64 * subMulRate P)`. -/
theorem routingAndStreamingStepBitCost_le (K p' P : ℕ) (hp' : p' ≤ P) :
    routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ (K - K / 2)) p' ≤
      2 ^ K * (32 * K * P) + 2 ^ K * (64 * subMulRate P) := by
  set t1 := 2 ^ (K / 2)
  set r := 2 ^ (K - K / 2)
  have h_rec_eq :
      routingAndStreamingStepBitCost t1 r p' =
        2 * recursiveTransposeTapeCost r p' (K / 2) +
          recursiveTransposeTapeCost t1 p' (K - K / 2) +
          recursiveMergeSortTapeCost r p' (K / 2) +
          sequentialLinearScanBitCost t1 r p' := by
    dsimp [routingAndStreamingStepBitCost, t1, r]
    rw [recursiveTransposeTapeCost_eq, recursiveTransposeTapeCost_eq, recursiveMergeSortTapeCost_eq]
  rw [h_rec_eq, recursiveTransposeTapeCost_eq, recursiveTransposeTapeCost_eq, recursiveMergeSortTapeCost_eq]
  unfold sequentialTransposeBitCost sequentialColumnMergeSortBitCost
    sequentialLinearScanBitCost sequentialPassBitCost addBitCost
  rw [sequentialTapeTransposeWithPasses_snd, sequentialTapeTransposeWithPasses_snd,
      sequentialAffineOddRouteWithPasses_snd]
  have hpow_split : t1 * r = 2 ^ K := by
    dsimp [t1, r]
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]
  have hpow_split_comm : r * t1 = 2 ^ K := by
    rw [mul_comm, hpow_split]
  have hlog_t1 : Nat.log2 (2 ^ (K / 2)) = K / 2 := nat_log2_two_pow (K / 2)
  have hlog_r : Nat.log2 (2 ^ (K - K / 2)) = K - K / 2 := nat_log2_two_pow (K - K / 2)
  have hpass1 :
      2 * (2 * Nat.log2 (2 ^ (K / 2)) * (2 ^ (K / 2) * r * (8 * p'))) +
        2 * Nat.log2 (2 ^ (K - K / 2)) * (2 ^ (K - K / 2) * t1 * (8 * p')) +
        2 * Nat.log2 (2 ^ (K / 2)) * (2 ^ (K / 2) * r * (8 * p')) ≤
        2 ^ K * (32 * K * P) := by
    rw [hlog_t1, hlog_r]
    change 2 * (2 * (K / 2) * (t1 * r * (8 * p'))) +
        2 * (K - K / 2) * (r * t1 * (8 * p')) +
        2 * (K / 2) * (t1 * r * (8 * p')) ≤
      2 ^ K * (32 * K * P)
    rw [hpow_split, hpow_split_comm]
    have hlog_comb : 3 * (K / 2) + (K - K / 2) ≤ 2 * K := by
      have h1 : K / 2 + (K - K / 2) = K := Nat.add_sub_of_le (Nat.div_le_self K 2)
      have h2 : 2 * (K / 2) ≤ K := Nat.mul_div_le K 2
      omega
    have h16p : 16 * p' ≤ 16 * P := by omega
    calc 2 * (2 * (K / 2) * (2 ^ K * (8 * p'))) +
          2 * (K - K / 2) * (2 ^ K * (8 * p')) +
          2 * (K / 2) * (2 ^ K * (8 * p'))
        = (3 * (K / 2) + (K - K / 2)) * 2 ^ K * (16 * p') := by ring
      _ ≤ (2 * K) * 2 ^ K * (16 * P) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ K) hlog_comb) h16p
      _ = 2 ^ K * (32 * K * P) := by ring
  have hpass2 :
      8 * (t1 * r * (8 * p')) ≤ 2 ^ K * (64 * subMulRate P) := by
    rw [hpow_split]
    unfold subMulRate
    have h64 : 64 * p' ≤ 64 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)) := by
      calc 64 * p' = 64 * (p' * 1 * 1) := by ring
        _ ≤ 64 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)) :=
            Nat.mul_le_mul_left 64 (Nat.mul_le_mul (Nat.mul_le_mul hp' (by omega)) (by omega))
    calc 8 * (2 ^ K * (8 * p'))
        = 2 ^ K * (64 * p') := by ring
      _ ≤ 2 ^ K * (64 * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))) :=
          Nat.mul_le_mul_left (2 ^ K) h64
  exact Nat.add_le_add hpass1 hpass2

/-- For any `K : ℕ` and `p' ≤ P`, with `t1 = 2 ^ (K / 2)` and `r = 2 ^ (K - K / 2)`,
`precomputeStepBitCost t1 r p' ≤ 2 ^ K * (184 * subMulRate P)`. -/
theorem precomputeStepBitCost_le (K p' P : ℕ) (hp' : p' ≤ P) :
    precomputeStepBitCost (2 ^ (K / 2)) (2 ^ (K - K / 2)) p' ≤
      2 ^ K * (184 * subMulRate P) := by
  unfold precomputeStepBitCost
  dsimp only
  set t1 := 2 ^ (K / 2)
  set r := 2 ^ (K - K / 2)
  set W_eff := effectiveFilterWidth (2 * p') r
  have hpow_split : t1 * r = 2 ^ K := by
    dsimp [t1, r]
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]
  have hW_le_r : W_eff ≤ r := effectiveFilterWidth_le_r (2 * p') r
  have ht1W_le : t1 * W_eff ≤ 2 ^ K := by
    rw [← hpow_split]
    exact Nat.mul_le_mul_left t1 hW_le_r
  have hr_le : r ≤ 2 ^ K :=
    Nat.pow_le_pow_right zero_lt_two (Nat.sub_le K (K / 2))
  have hcount_mul : t1 * W_eff + 4 * r ≤ 5 * 2 ^ K := by omega
  have hmul := mulBitCost_four_mul_le p' P hp'
  have hadd := addBitCost_four_mul_le p' P hp'
  have hpart1 :
      (t1 * W_eff + 4 * r) * mulBitCost (4 * p') ≤ 2 ^ K * (180 * subMulRate P) := by
    calc (t1 * W_eff + 4 * r) * mulBitCost (4 * p')
        ≤ (5 * 2 ^ K) * (36 * subMulRate P) := Nat.mul_le_mul hcount_mul hmul
      _ = 2 ^ K * (180 * subMulRate P) := by ring
  have hpart2 :
      t1 * W_eff * addBitCost (4 * p') ≤ 2 ^ K * (4 * subMulRate P) :=
    Nat.mul_le_mul ht1W_le hadd
  calc (t1 * W_eff + 4 * r) * mulBitCost (4 * p') + t1 * W_eff * addBitCost (4 * p')
      ≤ 2 ^ K * (180 * subMulRate P) + 2 ^ K * (4 * subMulRate P) :=
        Nat.add_le_add hpart1 hpart2
    _ = 2 ^ K * (184 * subMulRate P) := by ring

/-- **Three-Term Intrinsic Cost Upper Bound for `buildQuantizedSpec` (`[MS]` §7.2)**:
For any depth `L`, root precision `p`, and root log-length `K`, with `P = leafPrecision L p K`,
the intrinsic cost `(buildQuantizedSpec L p K).intrinsicCost` (including Synthetic-FFT butterflies,
Kronecker-spread sub-multiplications, twist & bidiagonal solver arithmetic, and multitape-TM
routing/streaming passes) is bounded above by:
`2 ^ K * (36 * sumLogLen L K * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K) * P)`. -/
theorem buildQuantizedSpec_intrinsicCost_le (L p K : ℕ) :
    let P := leafPrecision L p K
    (buildQuantizedSpec L p K).intrinsicCost ≤
      ((2 ^ K * (36 * sumLogLen L K * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K) * P) : ℕ) : ℝ) := by
  induction L generalizing p K with
  | zero =>
    dsimp [buildQuantizedSpec, QuantizedFastDFTSpec.intrinsicCost, addBitCost,
      leafPrecision, sumLogLen, leafLogLen]
    have heq : 2 ^ K * 2 ^ K * p = 2 ^ K * (36 * 0 * p + 1424 * 0 * subMulRate p + 2 ^ K * p) := by ring
    exact_mod_cast heq.le
  | succ L ih =>
    dsimp only [buildQuantizedSpec, quantizedBoxGaussianStepSpec,
      QuantizedFastDFTSpec.intrinsicCost, leafPrecision, sumLogLen, leafLogLen]
    set P := leafPrecision L (pChild p K) (K - K / 2)
    set p' := pChild p K
    set K' := K - K / 2
    have hp'_le : p' ≤ P := le_leafPrecision L p' K'
    have hpow_split : 2 ^ (K / 2) * 2 ^ K' = 2 ^ K := by
      dsimp [K']
      rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]
    have hsyn_nat :
        syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' ≤
          2 ^ K * (4 * K * P) := by
      unfold syntheticFFTStepBitCost addBitCost
      rw [(syntheticFFTRadix2Ops_closed_form (2 ^ K') (Nat.log2 (2 ^ (K / 2)))).2.2,
          nat_log2_two_pow (K / 2), hpow_split]
      have h2K : 2 * (K / 2) ≤ K := Nat.mul_div_le K 2
      have h4p' : 4 * p' ≤ 4 * P := by omega
      calc 2 * (K / 2) * 2 ^ K * (4 * p')
          ≤ K * 2 ^ K * (4 * P) := Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ K) h2K) h4p'
        _ = 2 ^ K * (4 * K * P) := by ring
    have hovh_nat :
        kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
          twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
          routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p' ≤
          2 ^ K * (32 * K * P) + 2 ^ K * (1424 * subMulRate P) := by
      have h1 := kroneckerSpreadStepBitCost_le (2 ^ (K / 2)) (2 ^ K') p' P hp'_le
      have h2 := twistAndSolverStepBitCost_le (2 ^ (K / 2)) (2 ^ K') p' P hp'_le
      have h3 := routingAndStreamingStepBitCost_le K p' P hp'_le
      rw [hpow_split] at h1 h2
      calc kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p'
          ≤ 2 ^ K * (720 * subMulRate P) + 2 ^ K * (640 * subMulRate P) +
            (2 ^ K * (32 * K * P) + 2 ^ K * (64 * subMulRate P)) :=
            Nat.add_le_add (Nat.add_le_add h1 h2) h3
        _ = 2 ^ K * (32 * K * P) + 2 ^ K * (1424 * subMulRate P) := by ring
    have hstep_nat :
        syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
          kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
          twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
          routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p' ≤
          2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P) := by
      calc syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p'
          = syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            (kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
              twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
              routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p') := by ring
        _ ≤ 2 ^ K * (4 * K * P) + (2 ^ K * (32 * K * P) + 2 ^ K * (1424 * subMulRate P)) :=
            Nat.add_le_add hsyn_nat hovh_nat
        _ = 2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P) := by ring
    have hstep_real :
        ((syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) +
          ((kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) +
          ((twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) +
          ((routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) ≤
          ((2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P) : ℕ) : ℝ) := by
      rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
      exact_mod_cast hstep_nat
    have hchild_real :
        ((2 ^ (K / 2) : ℕ) : ℝ) * (buildQuantizedSpec L p' K').intrinsicCost ≤
          ((2 ^ K * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K') * P) : ℕ) : ℝ) := by
      calc ((2 ^ (K / 2) : ℕ) : ℝ) * (buildQuantizedSpec L p' K').intrinsicCost
          ≤ ((2 ^ (K / 2) : ℕ) : ℝ) *
              ((2 ^ K' * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K') * P) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (ih p' K') (by positivity)
        _ = ((2 ^ K * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K') * P) : ℕ) : ℝ) := by
            rw [← Nat.cast_mul, ← mul_assoc, hpow_split]
    have hcomb_nat :
        (2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P)) +
          2 ^ K * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K') * P) =
        2 ^ K * (36 * (K + sumLogLen L K') * P + 1424 * (L + 1) * subMulRate P + 2 ^ (leafLogLen L K') * P) := by
      ring
    have hcomb_real :
        ((2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P) : ℕ) : ℝ) +
          ((2 ^ K * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K') * P) : ℕ) : ℝ) =
        ((2 ^ K * (36 * (K + sumLogLen L K') * P + 1424 * (L + 1) * subMulRate P + 2 ^ (leafLogLen L K') * P) : ℕ) : ℝ) := by
      rw [← Nat.cast_add, hcomb_nat]
    linarith

/-- **Compact `38704 * 2^K * P^2` Intrinsic Cost Bound for `buildQuantizedSpec` when `2^L ≤ K ≤ 2^(L+1)`**:
When `1 ≤ p` and `2 ^ L ≤ K ≤ 2 ^ (L + 1)`, with `P = leafPrecision L p K`:
- `sumLogLen L K ≤ 2 * K + L ≤ 7 * P`, so `36 * sumLogLen L K * P ≤ 252 * P * P`,
- `1424 * L * subMulRate P ≤ 1424 * (27 * P * P) = 38448 * P * P` (via `subMulRate_mul_le_27_sq`), and
- `2 ^ (leafLogLen L K) ≤ 4 ≤ 4 * P` (via `leafLogLen_le_two`),
so `(buildQuantizedSpec L p K).intrinsicCost ≤ 38704 * 2 ^ K * P ^ 2`. -/
theorem buildQuantizedSpec_intrinsicCost_le_quad_leafPrecision
    (L p K : ℕ) (hp : 1 ≤ p) (hK_low : 2 ^ L ≤ K) (hK_high : K ≤ 2 ^ (L + 1)) :
    let P := leafPrecision L p K
    (buildQuantizedSpec L p K).intrinsicCost ≤ ((38704 * 2 ^ K * P * P : ℕ) : ℝ) := by
  dsimp only
  set P := leafPrecision L p K
  have hP_eq : P = p + 2 * sumLogLen L K + 12 * L := leafPrecision_eq L p K
  have h1_le_P : 1 ≤ P := by omega
  have hK_le_P2 : K ≤ P + 2 := by
    cases L with
    | zero =>
      dsimp [sumLogLen] at hP_eq
      omega
    | succ L =>
      dsimp [sumLogLen] at hP_eq
      omega
  have h2L_le_P : 2 ^ L ≤ P := by
    cases L with
    | zero =>
      dsimp [sumLogLen] at hP_eq
      omega
    | succ L =>
      dsimp [sumLogLen] at hP_eq
      omega
  have hL_le_log2 : L ≤ Nat.log2 P := (Nat.le_log2 (by omega)).mpr h2L_le_P
  have hL_le_P : L ≤ P := by omega
  have hsum_le : sumLogLen L K ≤ 7 * P := by
    have := sumLogLen_le L K
    omega
  have hsub_le : L * subMulRate P ≤ 27 * P * P :=
    subMulRate_mul_le_27_sq L P h1_le_P hL_le_log2
  have hleaf_le : 2 ^ (leafLogLen L K) ≤ 4 * P := by
    have hle2 := leafLogLen_le_two L K hK_high
    have hpow : 2 ^ (leafLogLen L K) ≤ 2 ^ 2 := Nat.pow_le_pow_right zero_lt_two hle2
    omega
  have hinner :
      36 * sumLogLen L K * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K) * P ≤
        38704 * P * P := by
    have h1 : 36 * sumLogLen L K * P ≤ 252 * P * P := by
      calc 36 * sumLogLen L K * P = 36 * (sumLogLen L K * P) := by ring
        _ ≤ 36 * ((7 * P) * P) := Nat.mul_le_mul_left 36 (Nat.mul_le_mul_right P hsum_le)
        _ = 252 * P * P := by ring
    have h2 : 1424 * L * subMulRate P ≤ 38448 * P * P := by
      calc 1424 * L * subMulRate P
          = 1424 * (L * subMulRate P) := by ring
        _ ≤ 1424 * (27 * P * P) := Nat.mul_le_mul_left 1424 hsub_le
        _ = 38448 * P * P := by ring
    have h3 : 2 ^ (leafLogLen L K) * P ≤ (4 * P) * P :=
      Nat.mul_le_mul_right P hleaf_le
    calc 36 * sumLogLen L K * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K) * P
        ≤ 252 * P * P + 38448 * P * P + (4 * P) * P :=
          Nat.add_le_add (Nat.add_le_add h1 h2) h3
      _ = 38704 * P * P := by ring
  have htotal :
      2 ^ K * (36 * sumLogLen L K * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K) * P) ≤
        38704 * 2 ^ K * P * P := by
    calc 2 ^ K * (36 * sumLogLen L K * P + 1424 * L * subMulRate P + 2 ^ (leafLogLen L K) * P)
        ≤ 2 ^ K * (38704 * P * P) := Nat.mul_le_mul_left (2 ^ K) hinner
      _ = 38704 * 2 ^ K * P * P := by ring
  exact (buildQuantizedSpec_intrinsicCost_le L p K).trans (by exact_mod_cast htotal)

/-- **Schedule-Level Precomputation Cost Upper Bound for `buildQuantizedSpec`**:
For any depth `L`, root precision `p`, and root log-length `K`, with `P = leafPrecision L p K`,
`(buildQuantizedSpec L p K).precomputeCost ≤ ((2 ^ K * (184 * L * subMulRate P) : ℕ) : ℝ)`. -/
theorem buildQuantizedSpec_precomputeCost_le (L p K : ℕ) :
    let P := leafPrecision L p K
    (buildQuantizedSpec L p K).precomputeCost ≤
      ((2 ^ K * (184 * L * subMulRate P) : ℕ) : ℝ) := by
  induction L generalizing p K with
  | zero =>
    dsimp [buildQuantizedSpec, QuantizedFastDFTSpec.precomputeCost, leafPrecision]
    positivity
  | succ L ih =>
    dsimp only [buildQuantizedSpec, quantizedBoxGaussianStepSpec,
      QuantizedFastDFTSpec.precomputeCost, leafPrecision]
    set P := leafPrecision L (pChild p K) (K - K / 2)
    set p' := pChild p K
    set K' := K - K / 2
    have hp'_le : p' ≤ P := le_leafPrecision L p' K'
    have hr_le : 2 ^ K' ≤ 2 ^ K :=
      Nat.pow_le_pow_right zero_lt_two (Nat.sub_le K (K / 2))
    have hstep_nat :
        precomputeStepBitCost (2 ^ (K / 2)) (2 ^ K') p' ≤
          2 ^ K * (184 * subMulRate P) :=
      precomputeStepBitCost_le K p' P hp'_le
    have hstep_real :
        ((precomputeStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) ≤
          ((2 ^ K * (184 * subMulRate P) : ℕ) : ℝ) := by exact_mod_cast hstep_nat
    have hchild_nat :
        2 ^ K' * (184 * L * subMulRate P) ≤
          2 ^ K * (184 * L * subMulRate P) :=
      Nat.mul_le_mul_right _ hr_le
    have hchild_real :
        (buildQuantizedSpec L p' K').precomputeCost ≤
          ((2 ^ K * (184 * L * subMulRate P) : ℕ) : ℝ) :=
      (ih p' K').trans (by exact_mod_cast hchild_nat)
    have hcomb_nat :
        2 ^ K * (184 * subMulRate P) +
          2 ^ K * (184 * L * subMulRate P) =
        2 ^ K * (184 * (L + 1) * subMulRate P) := by ring
    have hcomb_real :
        ((2 ^ K * (184 * subMulRate P) : ℕ) : ℝ) +
          ((2 ^ K * (184 * L * subMulRate P) : ℕ) : ℝ) =
        ((2 ^ K * (184 * (L + 1) * subMulRate P) : ℕ) : ℝ) := by
      rw [← Nat.cast_add, hcomb_nat]
    linarith

/-- **Quadratic `4968 * 2^K * P^2` Precomputation Cost Bound for `buildQuantizedSpec` when `2^L ≤ K`**:
When `1 ≤ p` and `2 ^ L ≤ K`, with `P = leafPrecision L p K`, since `L * subMulRate P ≤ 27 * P * P`,
`(buildQuantizedSpec L p K).precomputeCost ≤ ((4968 * 2 ^ K * P * P : ℕ) : ℝ)`. -/
theorem buildQuantizedSpec_precomputeCost_le_quad_leafPrecision
    (L p K : ℕ) (hp : 1 ≤ p) (hK_low : 2 ^ L ≤ K) :
    let P := leafPrecision L p K
    (buildQuantizedSpec L p K).precomputeCost ≤ ((4968 * 2 ^ K * P * P : ℕ) : ℝ) := by
  dsimp only
  set P := leafPrecision L p K
  have hP_eq : P = p + 2 * sumLogLen L K + 12 * L := leafPrecision_eq L p K
  have h1_le_P : 1 ≤ P := by omega
  have h2L_le_P : 2 ^ L ≤ P := by
    cases L with
    | zero =>
      dsimp [sumLogLen] at hP_eq
      omega
    | succ L =>
      dsimp [sumLogLen] at hP_eq
      omega
  have hL_le_log2 : L ≤ Nat.log2 P := (Nat.le_log2 (by omega)).mpr h2L_le_P
  have hsub_le : L * subMulRate P ≤ 27 * P * P :=
    subMulRate_mul_le_27_sq L P h1_le_P hL_le_log2
  have htotal :
      2 ^ K * (184 * L * subMulRate P) ≤ 4968 * 2 ^ K * P * P := by
    calc 2 ^ K * (184 * L * subMulRate P)
        = (2 ^ K * 184) * (L * subMulRate P) := by ring
      _ ≤ (2 ^ K * 184) * (27 * P * P) := Nat.mul_le_mul_left _ hsub_le
      _ = 4968 * 2 ^ K * P * P := by ring
  exact (buildQuantizedSpec_precomputeCost_le L p K).trans (by exact_mod_cast htotal)

/-- Step bound for `precomputeStepRawTapBitCost` at `t1 = 2 ^ (K / 2)` and `r = 2 ^ (K - K / 2)`:
for `p' ≤ P` and `1 ≤ P`, since `t1 ≤ r = 2 ^ (K - K / 2)`,
`precomputeStepRawTapBitCost (2 ^ (K / 2)) (2 ^ (K - K / 2)) p' ≤ 2 ^ (K - K / 2) * (1820 * P * P * subMulRate P)`. -/
theorem precomputeStepRawTapBitCost_le (K p' P : ℕ) (hp' : p' ≤ P) (hP : 1 ≤ P) :
    precomputeStepRawTapBitCost (2 ^ (K / 2)) (2 ^ (K - K / 2)) p' ≤
      2 ^ (K - K / 2) * (1820 * P * P * subMulRate P) := by
  unfold precomputeStepRawTapBitCost
  dsimp only
  set t1 := 2 ^ (K / 2)
  set r := 2 ^ (K - K / 2)
  have ht1_le_r : t1 ≤ r := Nat.pow_le_pow_right zero_lt_two (by omega)
  have h4p1_le : 4 * p' + 1 ≤ 5 * P := by omega
  have hraw_le : t1 * (4 * p' + 1) ≤ r * (5 * P) := Nat.mul_le_mul ht1_le_r h4p1_le
  have hsum_taps : t1 * (4 * p' + 1) + 4 * r ≤ r * (9 * P) := by
    have h4r : 4 * r ≤ r * (4 * P) := by nlinarith
    linarith
  have hprod_taps : (t1 * (4 * p' + 1) + 4 * r) * (4 * p' + 1) ≤ r * (45 * P * P) := by
    calc (t1 * (4 * p' + 1) + 4 * r) * (4 * p' + 1)
        ≤ (r * (9 * P)) * (5 * P) := Nat.mul_le_mul hsum_taps h4p1_le
      _ = r * (45 * P * P) := by ring
  have hmul := mulBitCost_four_mul_le p' P hp'
  have hadd := addBitCost_four_mul_le p' P hp'
  have hmul_add : mulBitCost (4 * p') + addBitCost (4 * p') ≤ 40 * subMulRate P := by omega
  have hpart1 :
      (t1 * (4 * p' + 1) + 4 * r) * (4 * p' + 1) *
        (mulBitCost (4 * p') + addBitCost (4 * p')) ≤
        r * (1800 * P * P * subMulRate P) := by
    calc (t1 * (4 * p' + 1) + 4 * r) * (4 * p' + 1) *
          (mulBitCost (4 * p') + addBitCost (4 * p'))
        ≤ (r * (45 * P * P)) * (40 * subMulRate P) := Nat.mul_le_mul hprod_taps hmul_add
      _ = r * (1800 * P * P * subMulRate P) := by ring
  have hpart2 :
      t1 * (4 * p' + 1) * addBitCost (4 * p') ≤
        r * (20 * P * P * subMulRate P) := by
    have h5P_le : 5 * P ≤ 5 * P * P := by nlinarith
    calc t1 * (4 * p' + 1) * addBitCost (4 * p')
        ≤ (r * (5 * P)) * (4 * subMulRate P) := Nat.mul_le_mul hraw_le hadd
      _ ≤ (r * (5 * P * P)) * (4 * subMulRate P) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left r h5P_le)
      _ = r * (20 * P * P * subMulRate P) := by ring
  calc (t1 * (4 * p' + 1) + 4 * r) * (4 * p' + 1) *
        (mulBitCost (4 * p') + addBitCost (4 * p')) +
        t1 * (4 * p' + 1) * addBitCost (4 * p')
      ≤ r * (1800 * P * P * subMulRate P) + r * (20 * P * P * subMulRate P) :=
        Nat.add_le_add hpart1 hpart2
    _ = r * (1820 * P * P * subMulRate P) := by ring

/-- Multi-level raw-tap precomputation bound for `buildQuantizedSpec L p K`:
`(buildQuantizedSpec L p K).precomputeRawTapCost ≤ 2 ^ (K - K / 2) * (1820 * L * P * P * subMulRate P)`. -/
theorem buildQuantizedSpec_precomputeRawTapCost_le (L p K : ℕ) (hp : 1 ≤ p) :
    let P := leafPrecision L p K
    (buildQuantizedSpec L p K).precomputeRawTapCost ≤
      ((2 ^ (K - K / 2) * (1820 * L * P * P * subMulRate P) : ℕ) : ℝ) := by
  induction L generalizing p K with
  | zero =>
    dsimp [buildQuantizedSpec, QuantizedFastDFTSpec.precomputeRawTapCost, leafPrecision]
    positivity
  | succ L ih =>
    dsimp only [buildQuantizedSpec, quantizedBoxGaussianStepSpec,
      QuantizedFastDFTSpec.precomputeRawTapCost, leafPrecision]
    set P := leafPrecision L (pChild p K) (K - K / 2)
    set p' := pChild p K
    set K' := K - K / 2
    have hp'_pos : 1 ≤ p' := by
      dsimp [p']
      rw [pChild_eq_additive]
      omega
    have hp'_le : p' ≤ P := le_leafPrecision L p' K'
    have hP_pos : 1 ≤ P := hp'_pos.trans hp'_le
    have hstep_nat :
        precomputeStepRawTapBitCost (2 ^ (K / 2)) (2 ^ K') p' ≤
          2 ^ K' * (1820 * P * P * subMulRate P) :=
      precomputeStepRawTapBitCost_le K p' P hp'_le hP_pos
    have hstep_real :
        ((precomputeStepRawTapBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) ≤
          ((2 ^ K' * (1820 * P * P * subMulRate P) : ℕ) : ℝ) := by
      exact_mod_cast hstep_nat
    have hK'_sub_le : K' - K' / 2 ≤ K' := Nat.sub_le K' (K' / 2)
    have hpow_le : 2 ^ (K' - K' / 2) ≤ 2 ^ K' :=
      Nat.pow_le_pow_right zero_lt_two hK'_sub_le
    have hchild_nat :
        2 ^ (K' - K' / 2) * (1820 * L * P * P * subMulRate P) ≤
          2 ^ K' * (1820 * L * P * P * subMulRate P) :=
      Nat.mul_le_mul_right _ hpow_le
    have hchild_real :
        (buildQuantizedSpec L p' K').precomputeRawTapCost ≤
          ((2 ^ K' * (1820 * L * P * P * subMulRate P) : ℕ) : ℝ) :=
      (ih p' K' hp'_pos).trans (by exact_mod_cast hchild_nat)
    have hcomb_nat :
        2 ^ K' * (1820 * P * P * subMulRate P) +
          2 ^ K' * (1820 * L * P * P * subMulRate P) =
        2 ^ K' * (1820 * (L + 1) * P * P * subMulRate P) := by ring
    have hcomb_real :
        ((2 ^ K' * (1820 * P * P * subMulRate P) : ℕ) : ℝ) +
          ((2 ^ K' * (1820 * L * P * P * subMulRate P) : ℕ) : ℝ) =
        ((2 ^ K' * (1820 * (L + 1) * P * P * subMulRate P) : ℕ) : ℝ) := by
      rw [← Nat.cast_add, hcomb_nat]
    linarith

/-- **Quadratic Raw-Tap Precomputation Bound (`buildQuantizedSpec_precomputeRawTapCost_le_quad_of_sq_le_sqrt`, `[MS]` §7.2)**:
Whenever `1 ≤ p`, `2 ^ L ≤ K`, and `P * P ≤ 2 ^ (K / 2)` (`P = leafPrecision L p K`), the sub-linear
`2 ^ (K - K / 2) = √(2 ^ K)` factor in `buildQuantizedSpec_precomputeRawTapCost_le` absorbs `P^2`,
yielding `(buildQuantizedSpec L p K).precomputeRawTapCost ≤ 49140 * 2 ^ K * P * P`. -/
theorem buildQuantizedSpec_precomputeRawTapCost_le_quad_of_sq_le_sqrt
    (L p K : ℕ) (hp : 1 ≤ p) (_hLK : 2 ^ L ≤ K)
    (hP_sq : leafPrecision L p K * leafPrecision L p K ≤ 2 ^ (K / 2)) :
    let P := leafPrecision L p K
    (buildQuantizedSpec L p K).precomputeRawTapCost ≤
      ((49140 * 2 ^ K * P * P : ℕ) : ℝ) := by
  dsimp only
  set P := leafPrecision L p K
  have h1 := buildQuantizedSpec_precomputeRawTapCost_le L p K hp
  dsimp only at h1
  have hP_eq : P = p + 2 * sumLogLen L K + 12 * L := leafPrecision_eq L p K
  have h1_le_P : 1 ≤ P := by omega
  have h2L_le_P : 2 ^ L ≤ P := by
    cases L with
    | zero =>
      dsimp [sumLogLen] at hP_eq
      omega
    | succ L =>
      dsimp [sumLogLen] at hP_eq
      omega
  have hL_le_log2 : L ≤ Nat.log2 P := (Nat.le_log2 (by omega)).mpr h2L_le_P
  have hsub_le : L * subMulRate P ≤ 27 * P * P :=
    subMulRate_mul_le_27_sq L P h1_le_P hL_le_log2
  have hpow_split : 2 ^ (K - K / 2) * 2 ^ (K / 2) = 2 ^ K := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.div_le_self K 2)]
  have hnat :
      2 ^ (K - K / 2) * (1820 * L * P * P * subMulRate P) ≤
        49140 * 2 ^ K * P * P := by
    calc 2 ^ (K - K / 2) * (1820 * L * P * P * subMulRate P)
        = (2 ^ (K - K / 2) * 1820 * P * P) * (L * subMulRate P) := by ring
      _ ≤ (2 ^ (K - K / 2) * 1820 * P * P) * (27 * P * P) :=
          Nat.mul_le_mul_left _ hsub_le
      _ = 49140 * 2 ^ (K - K / 2) * (P * P) * P * P := by ring
      _ ≤ 49140 * 2 ^ (K - K / 2) * (2 ^ (K / 2)) * P * P :=
          Nat.mul_le_mul_right P (Nat.mul_le_mul_right P (Nat.mul_le_mul_left _ hP_sq))
      _ = 49140 * (2 ^ (K - K / 2) * 2 ^ (K / 2)) * P * P := by ring
      _ = 49140 * 2 ^ K * P * P := by rw [hpow_split]
  exact h1.trans (by exact_mod_cast hnat)

/-- **Unconditional Quartic-to-Quadratic Raw-Tap Precomputation Bound (`buildQuantizedSpec_precomputeRawTapCost_le_mul_quad`)**:
For any bound `M : ℕ` such that `2 ^ (K - K / 2) * (P * P) ≤ M * 2 ^ K` (`P = leafPrecision L p K`),
`(buildQuantizedSpec L p K).precomputeRawTapCost ≤ (49140 * M) * 2 ^ K * P * P`. -/
theorem buildQuantizedSpec_precomputeRawTapCost_le_mul_quad
    (L p K M : ℕ) (hp : 1 ≤ p) (_hLK : 2 ^ L ≤ K)
    (hM : 2 ^ (K - K / 2) * (leafPrecision L p K * leafPrecision L p K) ≤ M * 2 ^ K) :
    let P := leafPrecision L p K
    (buildQuantizedSpec L p K).precomputeRawTapCost ≤
      (((49140 * M) * 2 ^ K * P * P : ℕ) : ℝ) := by
  dsimp only
  set P := leafPrecision L p K
  have h1 := buildQuantizedSpec_precomputeRawTapCost_le L p K hp
  dsimp only at h1
  have hP_eq : P = p + 2 * sumLogLen L K + 12 * L := leafPrecision_eq L p K
  have h1_le_P : 1 ≤ P := by omega
  have h2L_le_P : 2 ^ L ≤ P := by
    cases L with
    | zero =>
      dsimp [sumLogLen] at hP_eq
      omega
    | succ L =>
      dsimp [sumLogLen] at hP_eq
      omega
  have hL_le_log2 : L ≤ Nat.log2 P := (Nat.le_log2 (by omega)).mpr h2L_le_P
  have hsub_le : L * subMulRate P ≤ 27 * P * P :=
    subMulRate_mul_le_27_sq L P h1_le_P hL_le_log2
  have hnat :
      2 ^ (K - K / 2) * (1820 * L * P * P * subMulRate P) ≤
        (49140 * M) * 2 ^ K * P * P := by
    calc 2 ^ (K - K / 2) * (1820 * L * P * P * subMulRate P)
        = (2 ^ (K - K / 2) * 1820 * P * P) * (L * subMulRate P) := by ring
      _ ≤ (2 ^ (K - K / 2) * 1820 * P * P) * (27 * P * P) :=
          Nat.mul_le_mul_left _ hsub_le
      _ = 49140 * (2 ^ (K - K / 2) * (P * P)) * P * P := by ring
      _ ≤ 49140 * (M * 2 ^ K) * P * P :=
          Nat.mul_le_mul_right P (Nat.mul_le_mul_right P (Nat.mul_le_mul_left 49140 hM))
      _ = (49140 * M) * 2 ^ K * P * P := by ring
  exact h1.trans (by exact_mod_cast hnat)

/-- **Discharge of `P^2 ≤ 2^(K0 / 2)` for `quantizedMultiplyOfBitLength` (`quantizedMultiplyOfBitLength_leafPrecision_sq_le_two_pow_half_K0`, `[MS]` §7.2)**:
For every bit-length `n` with `96 ≤ Nat.log2 n` (i.e., `n ≥ 2^96`), the schedule parameters of
`quantizedMultiplyOfBitLength n` (`b = max 1 (Nat.log2 n)`, `k = n / b + 1`,
`K0 = max 4 (Nat.log2 (2 * k) + 2)`, `L = Nat.log2 (K0 - 1)`, `p0 = rootPrecision b K0`,
`P = leafPrecision L p0 K0`) satisfy `P * P ≤ 2 ^ (K0 / 2)`. -/
theorem quantizedMultiplyOfBitLength_leafPrecision_sq_le_two_pow_half_K0
    (n : ℕ) (hb96 : 96 ≤ Nat.log2 n) :
    let b := max 1 (Nat.log2 n)
    let k := n / b + 1
    let K0 := max 4 (Nat.log2 (2 * k) + 2)
    let L := Nat.log2 (K0 - 1)
    let p0 := rootPrecision b K0
    let P := leafPrecision L p0 K0
    P * P ≤ 2 ^ (K0 / 2) := by
  dsimp only
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set P := leafPrecision L p0 K0
  have hb_eq : b = Nat.log2 n := Nat.max_eq_right (by omega)
  have hb_ge96 : 96 ≤ b := by omega
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    simp at hb96
  have h2b_le_n : 2 ^ b ≤ n := by
    rw [hb_eq]
    exact two_pow_log2_le n (by omega)
  have hn_lt_bk : n < b * k := by
    dsimp [k]
    have hdiv := Nat.div_add_mod n b
    have hmod : n % b < b := Nat.mod_lt n (by omega)
    have hmul : b * (n / b + 1) = b * (n / b) + b := by ring
    omega
  have h2b_lt_bk : 2 ^ b < b * k := lt_of_le_of_lt h2b_le_n hn_lt_bk
  have h2k_lt : 2 * k < 2 ^ (Nat.log2 (2 * k) + 1) := lt_two_pow_log2_succ (2 * k)
  have hK0_ge : Nat.log2 (2 * k) + 2 ≤ K0 := le_max_right 4 (Nat.log2 (2 * k) + 2)
  have h4k_lt_2K0 : 4 * k < 2 ^ K0 := by
    have h1 : 4 * k < 2 * 2 ^ (Nat.log2 (2 * k) + 1) := by omega
    have h2 : 2 * 2 ^ (Nat.log2 (2 * k) + 1) = 2 ^ (Nat.log2 (2 * k) + 2) := by ring
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right zero_lt_two hK0_ge)
  have hb8_pow : b / 8 + 1 ≤ 2 ^ (b / 8) := add_one_le_two_pow (b / 8)
  have hb_lt_pow : b < 2 ^ (b / 8 + 3) := by
    have h1 : b < 8 * (b / 8 + 1) := by omega
    have h2 : 8 * (b / 8 + 1) ≤ 8 * 2 ^ (b / 8) := Nat.mul_le_mul_left 8 hb8_pow
    have h3 : 8 * 2 ^ (b / 8) = 2 ^ (b / 8 + 3) := by
      have : (8 : ℕ) = 2 ^ 3 := by decide
      rw [this, ← pow_add]
      congr 1
      omega
    omega
  have hpow_b2_lt : 2 ^ (b + 2) < 2 ^ (b / 8 + 3 + K0) := by
    calc 2 ^ (b + 2) = 4 * 2 ^ b := by ring
      _ < 4 * (b * k) := by omega
      _ = b * (4 * k) := by ring
      _ < 2 ^ (b / 8 + 3) * 2 ^ K0 := Nat.mul_lt_mul_of_lt_of_lt hb_lt_pow h4k_lt_2K0
      _ = 2 ^ (b / 8 + 3 + K0) := by rw [← pow_add]
  have hexp_K0 : b + 2 < b / 8 + 3 + K0 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_b2_lt
  have hK0_lower : b - b / 8 ≤ K0 := by omega
  have hK0_le_2b : K0 ≤ 2 * b := by
    have hk_pos : 0 < k := Nat.succ_pos (n / b)
    have hk_le_n : k ≤ n := by
      dsimp [k]
      have hdiv_le : n / b ≤ n / 4 := Nat.div_le_div_left (by omega) (by decide)
      have hb_le_n : b ≤ n := by
        have := add_one_le_two_pow b
        omega
      omega
    have hn_lt : n < 2 ^ (b + 1) := by
      rw [hb_eq]
      exact lt_two_pow_log2_succ n
    have h2k_lt_b2 : 2 * k < 2 ^ (b + 2) := by
      have hpow_b2 : 2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by ring
      omega
    have hlog_lt : Nat.log2 (2 * k) < b + 2 := (Nat.log2_lt (by omega)).mpr h2k_lt_b2
    dsimp [K0]
    omega
  have hL_le_K0 : L ≤ K0 := by
    have h2L_le_K0 : 2 ^ L ≤ K0 :=
      (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
    have := add_one_le_two_pow L
    omega
  have hp0_eq : p0 = 2 * b + 2 * K0 + 6 := rfl
  have hP_le_44b : P ≤ 44 * b := by
    have h1 : P ≤ p0 + 4 * K0 + 14 * L := leafPrecision_le L p0 K0
    omega
  have h44b_le_pow : 44 * b ≤ 2 ^ (b / 8 + 9) := by
    have h1 : 44 * b ≤ 64 * 2 ^ (b / 8 + 3) := by omega
    have h2 : 64 * 2 ^ (b / 8 + 3) = 2 ^ (b / 8 + 9) := by
      have : (64 : ℕ) = 2 ^ 6 := by decide
      rw [this, ← pow_add]
      congr 1
      omega
    omega
  have hP_le_pow : P ≤ 2 ^ (b / 8 + 9) := hP_le_44b.trans h44b_le_pow
  have hP_sq_le_pow : P * P ≤ 2 ^ (2 * (b / 8) + 18) := by
    calc P * P ≤ 2 ^ (b / 8 + 9) * 2 ^ (b / 8 + 9) := Nat.mul_le_mul hP_le_pow hP_le_pow
      _ = 2 ^ (2 * (b / 8) + 18) := by
          rw [← pow_add]
          congr 1
          omega
  have hexp_le : 2 * (b / 8) + 18 ≤ K0 / 2 := by omega
  exact hP_sq_le_pow.trans (Nat.pow_le_pow_right zero_lt_two hexp_le)

/-- **Parameter-Free Finite-Precision Sinc-Gaussian Integer Multiplier (`quantizedMultiplyOfBitLength n A B`, `[MS]` §7)**:
Given only the bit-length `n : ℕ` (`A, B < 2 ^ n`) and the operands `A, B : ℕ`, automatically
constructs the complete multi-level recursion schedule:
- `b := max 1 (Nat.log2 n)` (chunk bit-width),
- `k := n / b + 1` (radix-`2^b` chunk count),
- `K0 := max 4 (Nat.log2 (2 * k) + 2)` (root log-transform length),
- `L := Nat.log2 (K0 - 1)` (recursion depth with `2 ^ L < K0 ≤ 2 ^ (L + 1)`),
- `p0 := rootPrecision b K0` (root target precision `2 b + 2 K0 + 6 ≥ 16`),
- `spec := buildQuantizedSpec L p0 K0`,
and executes `quantizedFastDFTMultiplyIntrinsicCost spec b K0 k k A B`. -/
noncomputable def quantizedMultiplyOfBitLength (n A B : ℕ) : ℕ × ℝ :=
  let b := max 1 (Nat.log2 n)
  let k := n / b + 1
  let K0 := max 4 (Nat.log2 (2 * k) + 2)
  let L := Nat.log2 (K0 - 1)
  let p0 := rootPrecision b K0
  let spec := buildQuantizedSpec L p0 K0
  quantizedFastDFTMultiplyIntrinsicCost spec b K0 k k A B

/-- **Unconditional Exact Correctness of `quantizedMultiplyOfBitLength` for All `n`-Bit Integers**:
For every bit-length `n : ℕ` and all natural numbers `A < 2 ^ n` and `B < 2 ^ n`,
`(quantizedMultiplyOfBitLength n A B).1 = A * B`. -/
theorem quantizedMultiplyOfBitLength_fst_eq_mul
    (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    (quantizedMultiplyOfBitLength n A B).1 = A * B := by
  dsimp only [quantizedMultiplyOfBitLength]
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set spec := buildQuantizedSpec L p0 K0
  have hb_pos : 1 ≤ b := le_max_left 1 (Nat.log2 n)
  have hK0_ge4 : 4 ≤ K0 := le_max_left 4 (Nat.log2 (2 * k) + 2)
  have hp0 : 8 ≤ p0 := by
    dsimp [p0, rootPrecision]
    omega
  have h2L_le_K0 : 2 ^ L ≤ K0 :=
    (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
  have hvalid : spec.Valid := buildQuantizedSpec_valid L p0 K0 hp0 h2L_le_K0
  have hsize : spec.size = 2 ^ K0 := buildQuantizedSpec_size L p0 K0
  have hp_eq : spec.p = rootPrecision b K0 := buildQuantizedSpec_p L p0 K0
  have hk : k + k ≤ 2 ^ K0 := by
    have hlt := lt_two_pow_log2_succ (2 * k)
    have hle_exp : Nat.log2 (2 * k) + 1 ≤ K0 := by
      have : Nat.log2 (2 * k) + 2 ≤ K0 := le_max_right 4 (Nat.log2 (2 * k) + 2)
      omega
    have hpow_le : 2 ^ (Nat.log2 (2 * k) + 1) ≤ 2 ^ K0 :=
      Nat.pow_le_pow_right zero_lt_two hle_exp
    omega
  have hbk : n ≤ b * k := by
    dsimp [k]
    have hdiv := Nat.div_add_mod n b
    have hmod : n % b < b := Nat.mod_lt n (by omega)
    have hmul : b * (n / b + 1) = b * (n / b) + b := by ring
    omega
  have hpow_bk : 2 ^ n ≤ (2 ^ b) ^ k := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right zero_lt_two hbk
  exact quantizedFastDFTMultiplyIntrinsicCost_fst_eq_mul
    spec hvalid b K0 k k hsize hp_eq hk A B (hA.trans_le hpow_bk) (hB.trans_le hpow_bk)

/-- Non-negativity of `(quantizedMultiplyOfBitLength n A B).2` for all `n, A, B : ℕ`. -/
theorem quantizedMultiplyOfBitLength_snd_nonneg (n A B : ℕ) :
    0 ≤ (quantizedMultiplyOfBitLength n A B).2 := by
  dsimp only [quantizedMultiplyOfBitLength]
  exact quantizedFastDFTMultiplyIntrinsicCost_snd_nonneg _ _ _ _ _ _ _

/-- **Tight Asymptotic `O(n log n)` Upper Bound on `(quantizedMultiplyOfBitLength n A B).2` for `96 ≤ Nat.log2 n`**:
Whenever `96 ≤ Nat.log2 n`, `quantizedMultiplyOfBitLength_leafPrecision_sq_le_two_pow_half_K0`
discharges `P^2 ≤ 2^(K0 / 2)` in `buildQuantizedSpec_precomputeRawTapCost_le_quad_of_sq_le_sqrt`,
yielding `(quantizedMultiplyOfBitLength n A B).2 ≤ 7840335360 * ((n : ℝ) * Real.log (n : ℝ))`. -/
theorem quantizedMultiplyOfBitLength_snd_le_n_log_n_of_log2_ge_96
    (n A B : ℕ) (hb96 : 96 ≤ Nat.log2 n) :
    (quantizedMultiplyOfBitLength n A B).2 ≤
      (7840335360 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
  dsimp only [quantizedMultiplyOfBitLength]
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set spec := buildQuantizedSpec L p0 K0
  set P := leafPrecision L p0 K0
  have hn : 16 ≤ n := by
    have h1 : 2 ^ 96 ≤ 2 ^ (Nat.log2 n) := Nat.pow_le_pow_right zero_lt_two hb96
    have hn_pos : 1 ≤ n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      subst hn0
      simp at hb96
    have h2 : 2 ^ (Nat.log2 n) ≤ n := two_pow_log2_le n hn_pos
    have h3 : 16 ≤ 2 ^ 96 := by decide
    omega
  have hb_eq : b = Nat.log2 n := Nat.max_eq_right (by omega)
  have hb_ge4 : 4 ≤ b := by omega
  have h2b_le_n : 2 ^ b ≤ n := by
    rw [hb_eq]
    exact two_pow_log2_le n (by omega)
  have hb_le_n : b ≤ n := by
    have := add_one_le_two_pow b
    omega
  have hdiv_pos : 1 ≤ n / b := Nat.div_pos hb_le_n (by omega)
  have hk_ge2 : 2 ≤ k := by dsimp [k]; omega
  have hbk_le : b * k ≤ 2 * n := by
    have hk_le : k ≤ 2 * (n / b) := by dsimp [k]; omega
    have hmul_div : b * (n / b) ≤ n := Nat.mul_div_le n b
    calc b * k ≤ b * (2 * (n / b)) := Nat.mul_le_mul_left b hk_le
      _ = 2 * (b * (n / b)) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hmul_div
  have hk_le_n : k ≤ n := by
    dsimp [k]
    have hdiv_le : n / b ≤ n / 4 := Nat.div_le_div_left hb_ge4 (by decide)
    omega
  have hlog_2k_ge2 : 2 ≤ Nat.log2 (2 * k) := by
    refine (Nat.le_log2 (by omega)).mpr ?_
    calc 2 ^ 2 = 4 := by decide
      _ ≤ 2 * k := by omega
  have hK0_eq : K0 = Nat.log2 (2 * k) + 2 := Nat.max_eq_right (by omega)
  have hK0_ge4 : 4 ≤ K0 := by omega
  have h2K0_le : 2 ^ K0 ≤ 8 * k := by
    rw [hK0_eq, pow_add]
    have hpow_2k : 2 ^ (Nat.log2 (2 * k)) ≤ 2 * k := two_pow_log2_le (2 * k) (by omega)
    calc 2 ^ (Nat.log2 (2 * k)) * 2 ^ 2
        ≤ (2 * k) * 4 := Nat.mul_le_mul_right 4 hpow_2k
      _ = 8 * k := by ring
  have hK0_le_2b : K0 ≤ 2 * b := by
    have hn_lt : n < 2 ^ (b + 1) := by
      rw [hb_eq]
      exact lt_two_pow_log2_succ n
    have h2k_lt : 2 * k < 2 ^ (b + 2) := by
      have hpow_b2 : 2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by ring
      omega
    have hlog_lt : Nat.log2 (2 * k) < b + 2 := (Nat.log2_lt (by omega)).mpr h2k_lt
    omega
  have h2L_le_K0 : 2 ^ L ≤ K0 :=
    (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
  have hK0_le_2L1 : K0 ≤ 2 ^ (L + 1) := by
    have h : K0 - 1 < 2 ^ (L + 1) := lt_two_pow_log2_succ (K0 - 1)
    omega
  have hL_le_K0 : L ≤ K0 := by
    have := add_one_le_two_pow L
    omega
  have hp0_eq : p0 = 2 * b + 2 * K0 + 6 := rfl
  have hp0_pos : 1 ≤ p0 := by omega
  have hp0_le_P : p0 ≤ P := le_leafPrecision L p0 K0
  have hP_le : P ≤ 44 * b := by
    have h1 : P ≤ p0 + 4 * K0 + 14 * L := leafPrecision_le L p0 K0
    omega
  have hP_sq : P * P ≤ 2 ^ (K0 / 2) :=
    quantizedMultiplyOfBitLength_leafPrecision_sq_le_two_pow_half_K0 n hb96
  have hcost_spec : spec.intrinsicCost ≤ ((38704 * 2 ^ K0 * P * P : ℕ) : ℝ) :=
    buildQuantizedSpec_intrinsicCost_le_quad_leafPrecision L p0 K0 hp0_pos h2L_le_K0 hK0_le_2L1
  have hpre_spec : spec.precomputeRawTapCost ≤ ((49140 * 2 ^ K0 * P * P : ℕ) : ℝ) :=
    buildQuantizedSpec_precomputeRawTapCost_le_quad_of_sq_le_sqrt L p0 K0 hp0_pos h2L_le_K0 hP_sq
  have hroot_nat : rootPipelineBitCost (2 ^ K0) p0 ≤ 7 * 2 ^ K0 * P * P :=
    rootPipelineBitCost_le_quad (2 ^ K0) p0 P hp0_pos hp0_le_P
  have hroot_real : ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ) ≤ ((7 * 2 ^ K0 * P * P : ℕ) : ℝ) := by
    exact_mod_cast hroot_nat
  have hquad_nat : 126555 * 2 ^ K0 * P * P ≤ 3920167680 * n * b := by
    have h1 : 126555 * 2 ^ K0 * P * P ≤ 126555 * (8 * k) * (44 * b) * (44 * b) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_left 126555 h2K0_le) hP_le)
        hP_le
    calc 126555 * 2 ^ K0 * P * P
        ≤ 126555 * (8 * k) * (44 * b) * (44 * b) := h1
      _ = 1960083840 * (b * k) * b := by ring
      _ ≤ 1960083840 * (2 * n) * b :=
          Nat.mul_le_mul_right b (Nat.mul_le_mul_left 1960083840 hbk_le)
      _ = 3920167680 * n * b := by ring
  have hquad_real :
       2 * (((38704 * 2 ^ K0 * P * P : ℕ) : ℝ)) +
        ((49140 * 2 ^ K0 * P * P : ℕ) : ℝ) +
        ((7 * 2 ^ K0 * P * P : ℕ) : ℝ) ≤
        ((3920167680 * n * b : ℕ) : ℝ) := by
    have hcomb :
        2 * (38704 * 2 ^ K0 * P * P) + 49140 * 2 ^ K0 * P * P + 7 * 2 ^ K0 * P * P =
          126555 * 2 ^ K0 * P * P := by ring
    have hle :
        2 * (38704 * 2 ^ K0 * P * P) + 49140 * 2 ^ K0 * P * P + 7 * 2 ^ K0 * P * P ≤
          3920167680 * n * b := by
      rw [hcomb]
      exact hquad_nat
    exact_mod_cast hle
  have hp0_8 : 8 ≤ p0 := by omega
  have hvalid : spec.Valid := buildQuantizedSpec_valid L p0 K0 hp0_8 h2L_le_K0
  have hsize : spec.size = 2 ^ K0 := buildQuantizedSpec_size L p0 K0
  have hp_spec : spec.p = rootPrecision b K0 := buildQuantizedSpec_p L p0 K0
  have hcost_exec :
      (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k k A B).2 ≤
        2 * spec.intrinsicCost + spec.precomputeRawTapCost +
          ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ) :=
    quantizedFastDFTMultiplyIntrinsicCost_snd_le spec hvalid b K0 k k A B hsize hp_spec
  have htotal_le :
      (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k k A B).2 ≤
        (3920167680 : ℝ) * (n : ℝ) * (b : ℝ) := by
    have hcast : ((3920167680 * n * b : ℕ) : ℝ) = (3920167680 : ℝ) * (n : ℝ) * (b : ℝ) := by
      push_cast
      ring
    linarith
  have hb_real : (b : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    rw [hb_eq]
    exact nat_log2_real_le_two_mul_log n (by omega)
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- **Explicit `O(n log n)` Upper Bound on `(quantizedMultiplyOfBitLength n A B).2` for All `n ≥ 16`**:
For every `n ≥ 16` and all `A, B : ℕ`, the intrinsic bit-operation cost of
`quantizedMultiplyOfBitLength n A B` (including both recursive transforms, `spec.precomputeRawTapCost`,
and `rootPipelineBitCost`) satisfies
`(quantizedMultiplyOfBitLength n A B).2 ≤ 54317320874319360 * ((n : ℝ) * Real.log (n : ℝ))`. -/
theorem quantizedMultiplyOfBitLength_snd_le_n_log_n
    (n A B : ℕ) (hn : 16 ≤ n) :
    (quantizedMultiplyOfBitLength n A B).2 ≤
      (54317320874319360 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
  by_cases hb96 : 96 ≤ Nat.log2 n
  · have h := quantizedMultiplyOfBitLength_snd_le_n_log_n_of_log2_ge_96 n A B hb96
    have hn_real : (3 : ℝ) ≤ (n : ℝ) := by
      have : 3 ≤ n := by omega
      exact_mod_cast this
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_ge_one : 1 ≤ Real.log (n : ℝ) := one_le_log_of_three_le (n : ℝ) hn_real
    have h_nlogn_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
    linarith
  · dsimp only [quantizedMultiplyOfBitLength]
    set b := max 1 (Nat.log2 n)
    set k := n / b + 1
    set K0 := max 4 (Nat.log2 (2 * k) + 2)
    set L := Nat.log2 (K0 - 1)
    set p0 := rootPrecision b K0
    set spec := buildQuantizedSpec L p0 K0
    set P := leafPrecision L p0 K0
    have hlog2_ge4 : 4 ≤ Nat.log2 n := by
      refine (Nat.le_log2 (by omega)).mpr ?_
      calc 2 ^ 4 = 16 := by decide
        _ ≤ n := hn
    have hb_eq : b = Nat.log2 n := Nat.max_eq_right (by omega)
    have hb_ge4 : 4 ≤ b := by omega
    have hb_lt96 : b < 96 := by omega
    have h2b_le_n : 2 ^ b ≤ n := by
      rw [hb_eq]
      exact two_pow_log2_le n (by omega)
    have hb_le_n : b ≤ n := by
      have := add_one_le_two_pow b
      omega
    have hdiv_pos : 1 ≤ n / b := Nat.div_pos hb_le_n (by omega)
    have hk_ge2 : 2 ≤ k := by dsimp [k]; omega
    have hbk_le : b * k ≤ 2 * n := by
      have hk_le : k ≤ 2 * (n / b) := by dsimp [k]; omega
      have hmul_div : b * (n / b) ≤ n := Nat.mul_div_le n b
      calc b * k ≤ b * (2 * (n / b)) := Nat.mul_le_mul_left b hk_le
        _ = 2 * (b * (n / b)) := by ring
        _ ≤ 2 * n := Nat.mul_le_mul_left 2 hmul_div
    have hk_le_n : k ≤ n := by
      dsimp [k]
      have hdiv_le : n / b ≤ n / 4 := Nat.div_le_div_left hb_ge4 (by decide)
      omega
    have hlog_2k_ge2 : 2 ≤ Nat.log2 (2 * k) := by
      refine (Nat.le_log2 (by omega)).mpr ?_
      calc 2 ^ 2 = 4 := by decide
        _ ≤ 2 * k := by omega
    have hK0_eq : K0 = Nat.log2 (2 * k) + 2 := Nat.max_eq_right (by omega)
    have hK0_ge4 : 4 ≤ K0 := by omega
    have h2K0_le : 2 ^ K0 ≤ 8 * k := by
      rw [hK0_eq, pow_add]
      have hpow_2k : 2 ^ (Nat.log2 (2 * k)) ≤ 2 * k := two_pow_log2_le (2 * k) (by omega)
      calc 2 ^ (Nat.log2 (2 * k)) * 2 ^ 2
          ≤ (2 * k) * 4 := Nat.mul_le_mul_right 4 hpow_2k
        _ = 8 * k := by ring
    have hK0_le_2b : K0 ≤ 2 * b := by
      have hn_lt : n < 2 ^ (b + 1) := by
        rw [hb_eq]
        exact lt_two_pow_log2_succ n
      have h2k_lt : 2 * k < 2 ^ (b + 2) := by
        have hpow_b2 : 2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by ring
        omega
      have hlog_lt : Nat.log2 (2 * k) < b + 2 := (Nat.log2_lt (by omega)).mpr h2k_lt
      omega
    have h2L_le_K0 : 2 ^ L ≤ K0 :=
      (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
    have hK0_le_2L1 : K0 ≤ 2 ^ (L + 1) := by
      have h : K0 - 1 < 2 ^ (L + 1) := lt_two_pow_log2_succ (K0 - 1)
      omega
    have hL_le_K0 : L ≤ K0 := by
      have := add_one_le_two_pow L
      omega
    have hp0_eq : p0 = 2 * b + 2 * K0 + 6 := rfl
    have hp0_pos : 1 ≤ p0 := by omega
    have hp0_le_P : p0 ≤ P := le_leafPrecision L p0 K0
    have hP_le : P ≤ 44 * b := by
      have h1 : P ≤ p0 + 4 * K0 + 14 * L := leafPrecision_le L p0 K0
      omega
    have hP_le_4224 : P ≤ 4224 := by omega
    have hM : 2 ^ (K0 - K0 / 2) * (P * P) ≤ 17842176 * 2 ^ K0 := by
      have hpow : 2 ^ (K0 - K0 / 2) ≤ 2 ^ K0 :=
        Nat.pow_le_pow_right zero_lt_two (Nat.sub_le K0 (K0 / 2))
      have hsq : P * P ≤ 17842176 := by
        calc P * P ≤ 4224 * 4224 := Nat.mul_le_mul hP_le_4224 hP_le_4224
          _ = 17842176 := by decide
      calc 2 ^ (K0 - K0 / 2) * (P * P)
          ≤ 2 ^ K0 * 17842176 := Nat.mul_le_mul hpow hsq
        _ = 17842176 * 2 ^ K0 := by ring
    have hcost_spec : spec.intrinsicCost ≤ ((38704 * 2 ^ K0 * P * P : ℕ) : ℝ) :=
      buildQuantizedSpec_intrinsicCost_le_quad_leafPrecision L p0 K0 hp0_pos h2L_le_K0 hK0_le_2L1
    have hpre_spec : spec.precomputeRawTapCost ≤ (((49140 * 17842176) * 2 ^ K0 * P * P : ℕ) : ℝ) :=
      buildQuantizedSpec_precomputeRawTapCost_le_mul_quad L p0 K0 17842176 hp0_pos h2L_le_K0 hM
    have hroot_nat : rootPipelineBitCost (2 ^ K0) p0 ≤ 7 * 2 ^ K0 * P * P :=
      rootPipelineBitCost_le_quad (2 ^ K0) p0 P hp0_pos hp0_le_P
    have hroot_real : ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ) ≤ ((7 * 2 ^ K0 * P * P : ℕ) : ℝ) := by
      exact_mod_cast hroot_nat
    have hquad_nat : 876764606055 * 2 ^ K0 * P * P ≤ 27158660437159680 * n * b := by
      have h1 : 876764606055 * 2 ^ K0 * P * P ≤ 876764606055 * (8 * k) * (44 * b) * (44 * b) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul_left 876764606055 h2K0_le) hP_le)
          hP_le
      calc 876764606055 * 2 ^ K0 * P * P
          ≤ 876764606055 * (8 * k) * (44 * b) * (44 * b) := h1
        _ = 13579330218579840 * (b * k) * b := by ring
        _ ≤ 13579330218579840 * (2 * n) * b :=
            Nat.mul_le_mul_right b (Nat.mul_le_mul_left 13579330218579840 hbk_le)
        _ = 27158660437159680 * n * b := by ring
    have hquad_real :
         2 * (((38704 * 2 ^ K0 * P * P : ℕ) : ℝ)) +
          (((49140 * 17842176) * 2 ^ K0 * P * P : ℕ) : ℝ) +
          ((7 * 2 ^ K0 * P * P : ℕ) : ℝ) ≤
          ((27158660437159680 * n * b : ℕ) : ℝ) := by
      have hcomb :
          2 * (38704 * 2 ^ K0 * P * P) + (49140 * 17842176) * 2 ^ K0 * P * P + 7 * 2 ^ K0 * P * P =
            876764606055 * 2 ^ K0 * P * P := by ring
      have hle :
          2 * (38704 * 2 ^ K0 * P * P) + (49140 * 17842176) * 2 ^ K0 * P * P + 7 * 2 ^ K0 * P * P ≤
            27158660437159680 * n * b := by
        rw [hcomb]
        exact hquad_nat
      exact_mod_cast hle
    have hp0_8 : 8 ≤ p0 := by omega
    have hvalid : spec.Valid := buildQuantizedSpec_valid L p0 K0 hp0_8 h2L_le_K0
    have hsize : spec.size = 2 ^ K0 := buildQuantizedSpec_size L p0 K0
    have hp_spec : spec.p = rootPrecision b K0 := buildQuantizedSpec_p L p0 K0
    have hcost_exec :
        (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k k A B).2 ≤
          2 * spec.intrinsicCost + spec.precomputeRawTapCost +
            ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ) :=
      quantizedFastDFTMultiplyIntrinsicCost_snd_le spec hvalid b K0 k k A B hsize hp_spec
    have htotal_le :
        (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k k A B).2 ≤
          (27158660437159680 : ℝ) * (n : ℝ) * (b : ℝ) := by
      have hcast : ((27158660437159680 * n * b : ℕ) : ℝ) = (27158660437159680 : ℝ) * (n : ℝ) * (b : ℝ) := by
        push_cast
        ring
      linarith
    have hb_real : (b : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      rw [hb_eq]
      exact nat_log2_real_le_two_mul_log n (by omega)
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith

/-- **Unconditional End-to-End `O(n log n)` Bit Complexity of `quantizedMultiplyOfBitLength` (`[MS]` §7)**:
For any operand sequences `A, B : ℕ → ℕ` (with **zero** external cost-function or scaling hypotheses),
the intrinsic bit-operation cost of `quantizedMultiplyOfBitLength` (charging `spec.precomputeRawTapCost`
for all `t_1 (4 p' + 1)` raw Sinc-Gaussian taps) satisfies:
`(fun n => (quantizedMultiplyOfBitLength n (A n) (B n)).2) =O[atTop] (fun n => n * log n)`. -/
theorem quantizedMultiplyOfBitLength_snd_isBigO_n_log_n (A B : ℕ → ℕ) :
    (fun n : ℕ => (quantizedMultiplyOfBitLength n (A n) (B n)).2) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (54317320874319360 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨16, fun n hn => ?_⟩
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by
    have : 3 ≤ n := by omega
    exact_mod_cast this
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_ge_one : 1 ≤ Real.log (n : ℝ) := one_le_log_of_three_le (n : ℝ) hn_real
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by linarith
  have h_nlogn_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hn_nonneg hlog_nonneg
  have h_cost_nonneg : 0 ≤ (quantizedMultiplyOfBitLength n (A n) (B n)).2 :=
    quantizedMultiplyOfBitLength_snd_nonneg n (A n) (B n)
  rw [Real.norm_of_nonneg h_cost_nonneg, Real.norm_of_nonneg h_nlogn_nonneg]
  exact quantizedMultiplyOfBitLength_snd_le_n_log_n n (A n) (B n) hn

end IntMul
