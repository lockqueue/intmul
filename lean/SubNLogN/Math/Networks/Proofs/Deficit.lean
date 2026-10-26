import SubNLogN.Math.Networks.Deficit
import SubNLogN.S1.Params

/-!
# Proofs of the real deficit link (Proposition A.2 (`prop:deficits`))

Proves the four contracts stated in `SubNLogN/Math/Networks/Deficit.lean`:
`LogMLt14Stmt`, `DeficitTestStmt`, `DeficitsH100Stmt`, `DeficitsPrintedH100Stmt`.
No hypotheses are assumed: all four are proved outright.

## Plan (Proposition A.2 (`prop:deficits`), Appendix A.1 (`sec:transfer-premises`))

1. `ln 10⁶ < 14` (`LogMLt14Stmt`). `tripleM 100 = 10⁶` (`SubNLogN.S1.tripleM_100`, by `decide`);
   by `Real.log_lt_iff_lt_exp` it suffices that `10⁶ < e¹⁴ = (e¹)¹⁴` (`Real.exp_nat_mul`).
   Mathlib's certified decimal bound `Real.exp_one_gt_d9 : 2.7182818283 < e` gives `2.7 < e`, the
   rational inequality `10⁶ < 2.7¹⁴` (`2.7¹⁴ = 1094189.89…`) is checked by `norm_num`, and strict
   monotonicity of `x ↦ x¹⁴` on `[0, ∞)` (`pow_lt_pow_left₀`) concludes. (The paper instead uses the
   Taylor partial sum `∑_{j ≤ 11} 7^j/j! > 1000`, i.e. `e⁷ > 10³`; the content is the same.)
2. Deficit test (`DeficitTestStmt`, eq. (`eq:deficit-test`)). For `m > 1`, `u > 0`:
   `m^{1−u} = exp(log m · (1 − u)) = m · exp(−(log m · u))` (`Real.rpow_def_of_pos`, `Real.exp_add`,
   `Real.exp_log`); `exp x > x + 1` for `x = −(log m · u) ≠ 0` (`Real.add_one_lt_exp`; here
   `log m > 0` by `Real.log_pos`); `1 − log m · u ≥ 1 − L u ≥ 1 − η` from `log m ≤ L`, `u ≥ 0` and
   `L u ≤ η`; finally `m (1 − η) = s/W` for `η = (W m − s)/(W m)` (`field_simp`, using `W, m ≠ 0`).
3. `h = 100` (`DeficitsH100Stmt`). Instantiate the test with `m = tripleM 100 = 10⁶`, `L = 14`
   (item 1), `u = 2^{−40}` resp. `u = 2^{−42}`; the remaining hypothesis `14 u ≤ η` is a rational
   comparison of the exact integers `W_b, s_b, W_c, s_c` (`SubNLogN.S1.tripleWb_100`,
   `tripleSb_100`, `tripleWc_100`, `tripleSc_100`), checked by `norm_num`
   (`η_b = 339/22587335000000`, `η_c = 73/19906842167500`).
4. Printed exponent (`DeficitsPrintedH100Stmt`, [OAI26, §3.6, (10)]). The same test with `u = 2^{−50}` (still `L = 14`).
-/

namespace SubNLogN.Math.Networks

/-- `m = tripleM 100 = 10⁶` as a real number. -/
theorem deficit_tripleM_100_cast : ((tripleM 100 : ℕ) : ℝ) = 1000000 := by
  rw [SubNLogN.S1.tripleM_100]
  norm_num

/-- `ln 10⁶ < 14` (Proposition A.2 (`prop:deficits`)), via `10⁶ < 2.7¹⁴ < e¹⁴`. -/
theorem logMLt14_holds : LogMLt14Stmt := by
  unfold LogMLt14Stmt
  rw [deficit_tripleM_100_cast, Real.log_lt_iff_lt_exp (by norm_num)]
  have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h14 : Real.exp 14 = Real.exp 1 ^ 14 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h14]
  calc (1000000 : ℝ) < 2.7 ^ 14 := by norm_num
    _ < Real.exp 1 ^ 14 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)

/-- The deficit test (Proposition A.2 (`prop:deficits`), eq. (`eq:deficit-test`)): for `m > 1`, `W > 0`, `ln m ≤ L`,
`u > 0` and `L u ≤ η = (W m − s)/(W m)`, we have `s/W = m(1 − η) ≤ m(1 − L u) ≤ m(1 − u ln m)
< m e^{−u ln m} = m^{1−u}`. -/
theorem deficitTest_holds : DeficitTestStmt := by
  intro s W m L u hm hW hL hu hη
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hlog : 0 < Real.log m := Real.log_pos hm
  have hW' : W ≠ 0 := hW.ne'
  have hm' : m ≠ 0 := hm0.ne'
  have hpow : m ^ (1 - u) = m * Real.exp (-(Real.log m * u)) := by
    rw [Real.rpow_def_of_pos hm0, mul_sub, mul_one, sub_eq_add_neg, Real.exp_add,
      Real.exp_log hm0]
  have hsW : s / W = m * (1 - (W * m - s) / (W * m)) := by
    field_simp
    ring
  have hlu : 0 < Real.log m * u := mul_pos hlog hu
  have hx : -(Real.log m * u) ≠ 0 := (by linarith : -(Real.log m * u) < 0).ne
  have hexp : -(Real.log m * u) + 1 < Real.exp (-(Real.log m * u)) := Real.add_one_lt_exp hx
  have h1 : 1 - (W * m - s) / (W * m) ≤ 1 - Real.log m * u := by
    have : Real.log m * u ≤ L * u := mul_le_mul_of_nonneg_right hL hu.le
    linarith
  have h2 : 1 - Real.log m * u < Real.exp (-(Real.log m * u)) := by linarith
  rw [hpow, hsW]
  exact mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 h2) hm0

/-- `1 < m` for `m = tripleM 100 = 10⁶`. -/
theorem deficit_one_lt_m100 : (1 : ℝ) < ((tripleM 100 : ℕ) : ℝ) := by
  rw [deficit_tripleM_100_cast]
  norm_num

/-- The deficit test instantiated at `h = 100` with `L = 14` (using `ln 10⁶ < 14`): for naturals
`s`, `W > 0` and a real `u > 0` with `14 u ≤ (W m − s)/(W m)`, where `m = tripleM 100`, we get
`s/W < m^{1−u}`. -/
theorem deficit_h100_of {s W : ℕ} (hW : 0 < W) {u : ℝ} (hu : 0 < u)
    (hη : 14 * u ≤ ((W : ℝ) * ((tripleM 100 : ℕ) : ℝ) - (s : ℝ)) /
      ((W : ℝ) * ((tripleM 100 : ℕ) : ℝ))) :
    (s : ℝ) / (W : ℝ) < ((tripleM 100 : ℕ) : ℝ) ^ (1 - u) :=
  deficitTest_holds s W _ 14 u deficit_one_lt_m100 (by exact_mod_cast hW)
    (le_of_lt logMLt14_holds) hu hη

/-- Proposition A.2 (`prop:deficits`) at `h = 100`: `s_b/W_b < m^{1−2^{−40}}` and
`s_c/W_c < m^{1−2^{−42}}`. Proof: the deficit test with `L = 14`; the hypotheses
`14 · 2^{−40} ≤ η_b` and `14 · 2^{−42} ≤ η_c` are checked by `norm_num` on the exact integers
`W_b, s_b, W_c, s_c` of `SubNLogN/S1/Params.lean`. -/
theorem deficitsH100_holds : DeficitsH100Stmt := by
  unfold DeficitsH100Stmt
  refine ⟨deficit_h100_of ?_ (by positivity) ?_, deficit_h100_of ?_ (by positivity) ?_⟩
  · rw [SubNLogN.S1.tripleWb_100]; norm_num
  · rw [SubNLogN.S1.tripleWb_100, SubNLogN.S1.tripleSb_100, deficit_tripleM_100_cast]; norm_num
  · rw [SubNLogN.S1.tripleWc_100]; norm_num
  · rw [SubNLogN.S1.tripleWc_100, SubNLogN.S1.tripleSc_100, deficit_tripleM_100_cast]; norm_num

/-- The printed exponent ([OAI26, §3.6, (10)], Proposition A.2 (`prop:deficits`)) at `h = 100`: `s_b/W_b < m^{1−2^{−50}}`
and `s_c/W_c < m^{1−2^{−50}}`. Proof: the deficit test with `L = 14` and `u = 2^{−50}`
(`14 · 2^{−50} ≤ η_b, η_c`, checked by `norm_num` on the exact integers). -/
theorem deficitsPrintedH100_holds : DeficitsPrintedH100Stmt := by
  unfold DeficitsPrintedH100Stmt
  refine ⟨deficit_h100_of ?_ (by positivity) ?_, deficit_h100_of ?_ (by positivity) ?_⟩
  · rw [SubNLogN.S1.tripleWb_100]; norm_num
  · rw [SubNLogN.S1.tripleWb_100, SubNLogN.S1.tripleSb_100, deficit_tripleM_100_cast]; norm_num
  · rw [SubNLogN.S1.tripleWc_100]; norm_num
  · rw [SubNLogN.S1.tripleWc_100, SubNLogN.S1.tripleSc_100, deficit_tripleM_100_cast]; norm_num

end SubNLogN.Math.Networks
