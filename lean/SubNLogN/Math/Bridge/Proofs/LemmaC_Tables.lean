import SubNLogN.Math.Bridge.LemmaC_Tables

/-!
# Bridge: proofs of the Lemma 4.6 (bridge Lemma C)(iii) table-entry contracts

Proofs of the four value-level contracts of `SubNLogN/Math/Bridge/LemmaC_Tables.lean`
(Lemma 4.6 (`lem:bridge-C`)(iii) and Lemma B.3 (`lem:phase-tables`); `LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), kept for stability). Throughout `v = gridUnit q = 2^{-q}`.

* `lemmaC_iii_tap`: the exact residue-class sum of at most `2P+1` samples, each within
  `2^{-(q+g+4)}` (`g = lg(2P+2) + 12`), followed by one nearest rounding, is within
  `(2P+1)2^{-q-g-4} + (√2/2)v ≤ v/2^16 + (√2/2)v < 0.71 v` of the truncated folded tap.
* `lemmaC_iii_solver`: `ĉ_max ≥ 0.46`, so `|1/ĉ_max - 1/c_max|` and `|ĉ_min/ĉ_max - c_min/c_max|`
  are `≤ 0.14 v`; with `u_S ≤ v/32` and one nearest rounding (`≤ v/2`) the total is `< 0.68 v`.
  The clamp `max(0,·)` is harmless since `c_min/c_max ≥ 0`.
* `lemmaC_iii_phase`: `|(1-v/8)e_0| ≤ (1-v/8)(1+v/16) < 1`, and
  `|ê - e| < √2 v + v/16 + (v/8)(1+v/16) < 2v` (only `v ≤ 1` is used).
* `lemmaC_iii_phase_mul`: `|Q(ê z)| ≤ |ê z| ≤ |z|`, error `< √2 v + 2v < 4v`.

Only the public rounding lemmas of `SubNLogN/Math/Common/Grid.lean` and, for the tap and solver
entries (stated for every nearest rounding `rr`, `IsNearestRounding rr`), of
`SubNLogN/Math/Common/RoundNearest.lean` (`norm_crnd_sub_le`, `abs_rr_sub_le`) are used.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

/-! ## Elementary helpers -/

/-- `2^{-n} = gridUnit n` (integer exponent form used in the contracts). -/
private theorem two_zpow_neg_natCast_eq_gridUnit (n : ℕ) :
    (2 : ℝ) ^ (-((n : ℕ) : ℤ)) = gridUnit n := by
  rw [zpow_neg, zpow_natCast]; rfl

/-- `gridUnit (a + b) = gridUnit a * gridUnit b`. -/
private theorem gridUnit_add_eq_mul (a b : ℕ) : gridUnit (a + b) = gridUnit a * gridUnit b := by
  unfold gridUnit; rw [pow_add, mul_inv]

/-- `gridUnit q ≤ 1`. -/
private theorem gridUnit_le_one' (q : ℕ) : gridUnit q ≤ 1 := by
  unfold gridUnit
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- `n ≤ 2^{lg n}` (as reals), since `lg n ≥ ⌈log₂ n⌉`. -/
private theorem natCast_le_two_pow_lg (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ lg n := by
  have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  have h2 : 2 ^ Nat.clog 2 n ≤ 2 ^ lg n := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  exact_mod_cast h1.trans h2

/-- `n · 2^{-lg n} ≤ 1`. -/
private theorem natCast_mul_gridUnit_lg_le_one (n : ℕ) : (n : ℝ) * gridUnit (lg n) ≤ 1 := by
  unfold gridUnit
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  exact natCast_le_two_pow_lg n

/-- `√2 < 1.4143`. -/
private theorem sqrt_two_lt_14143 : Real.sqrt 2 < 1.4143 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-! ## Taps -/

/-- Lemma 4.6 (bridge Lemma C)(iii) taps (Lemma B.3 (`lem:phase-tables`)). -/
theorem lemmaC_iii_tap : LemmaC_iii_tapStmt := by
  intro rr hrr P ω α _hC t _ht δ e ghat hg
  set ε : ℝ := (2 : ℝ) ^ (-((P + 2 + (lg (2 * P + 2) + 12) + 4 : ℕ) : ℤ)) with hε
  set S : ℂ := ∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    if s % (t : ℤ) = e % (t : ℤ) then ghat s else 0 with hS
  have hv := gridUnit_pos (P + 2)
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hdiff : ‖S - truncFoldedFilter α t P δ e‖ ≤ ((2 * P + 1 : ℕ) : ℝ) * ε := by
    unfold truncFoldedFilter
    rw [hS, ← Finset.sum_sub_distrib]
    calc ‖∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
          ((if s % (t : ℤ) = e % (t : ℤ) then ghat s else 0) -
            (if s % (t : ℤ) = e % (t : ℤ) then carrier α t ((s : ℝ) + δ) else 0))‖
        ≤ ∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
          ‖(if s % (t : ℤ) = e % (t : ℤ) then ghat s else 0) -
            (if s % (t : ℤ) = e % (t : ℤ) then carrier α t ((s : ℝ) + δ) else 0)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), ε := by
          apply Finset.sum_le_sum
          intro s hs
          split_ifs
          · exact hg s hs
          · simpa using hε0
      _ = ((2 * P + 1 : ℕ) : ℝ) * ε := by
          rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
          congr 2
          omega
  have hkey : ((2 * P + 1 : ℕ) : ℝ) * ε ≤ gridUnit (P + 2) / 65536 := by
    rw [hε, two_zpow_neg_natCast_eq_gridUnit,
      gridUnit_add_eq_mul (P + 2 + (lg (2 * P + 2) + 12)) 4,
      gridUnit_add_eq_mul (P + 2) (lg (2 * P + 2) + 12), gridUnit_add_eq_mul (lg (2 * P + 2)) 12]
    have h1 : ((2 * P + 1 : ℕ) : ℝ) * gridUnit (lg (2 * P + 2)) ≤ 1 := by
      have h2 := natCast_mul_gridUnit_lg_le_one (2 * P + 2)
      have h3 : ((2 * P + 1 : ℕ) : ℝ) ≤ ((2 * P + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * P + 1 ≤ 2 * P + 2)
      have h4 := gridUnit_pos (lg (2 * P + 2))
      nlinarith
    have h12 : gridUnit 12 * gridUnit 4 = 1 / 65536 := by
      unfold gridUnit; norm_num
    have hg0 := gridUnit_pos (lg (2 * P + 2))
    calc ((2 * P + 1 : ℕ) : ℝ) * (gridUnit (P + 2) * (gridUnit (lg (2 * P + 2)) * gridUnit 12) *
          gridUnit 4)
        = (((2 * P + 1 : ℕ) : ℝ) * gridUnit (lg (2 * P + 2))) * gridUnit (P + 2) *
          (gridUnit 12 * gridUnit 4) := by ring
      _ ≤ 1 * gridUnit (P + 2) * (gridUnit 12 * gridUnit 4) := by
          gcongr
      _ = gridUnit (P + 2) / 65536 := by rw [h12]; ring
  have hround := norm_crnd_sub_le hrr (P + 2) S
  have hs2 := sqrt_two_lt_14143
  calc ‖crnd rr (P + 2) S - truncFoldedFilter α t P δ e‖
      ≤ ‖crnd rr (P + 2) S - S‖ + ‖S - truncFoldedFilter α t P δ e‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt 2 / 2 * gridUnit (P + 2) + gridUnit (P + 2) / 65536 :=
        add_le_add hround (hdiff.trans hkey)
    _ < 0.71 * gridUnit (P + 2) := by nlinarith

/-! ## Solver entries -/

/-- `gridUnit` is antitone. -/
private theorem gridUnit_anti {a b : ℕ} (h : a ≤ b) : gridUnit b ≤ gridUnit a := by
  unfold gridUnit
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- Core of `lemmaC_iii_solver` in a fixed orientation (`c_M = c_max > c_m = c_min ≥ 0`), with the
entry errors already expressed in units of `v = gridUnit q`. -/
private theorem solver_oriented (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr)
    (q : ℕ) (cM cm cMh cmh μ' a'' uS : ℝ) (hcm : 0 ≤ cm) (hlt : cm < cM)
    (hM : (0.49999999 : ℝ) < cM) (hMh : |cMh - cM| ≤ gridUnit q / 32)
    (hmh : |cmh - cm| ≤ gridUnit q / 32) (huS : uS ≤ gridUnit q / 32)
    (hμ : |μ' - cMh⁻¹| ≤ uS) (ha : |a'' - cmh / cMh| ≤ uS) :
    |rr q μ' - cM⁻¹| < gridUnit q ∧ |max 0 (rr q a'') - cm / cM| < gridUnit q := by
  have hv : 0 < gridUnit q := gridUnit_pos q
  have hv1 : gridUnit q ≤ 1 := gridUnit_le_one' q
  have hMh' := abs_le.mp hMh
  have hcMh : (0.46 : ℝ) ≤ cMh := by linarith [hMh'.1]
  have hcM0 : 0 < cM := by linarith
  have hcMh0 : 0 < cMh := by linarith
  have hprod : (0.2299 : ℝ) ≤ cMh * cM := by nlinarith
  have hpos : 0 < cMh * cM := mul_pos hcMh0 hcM0
  have hinv : |cMh⁻¹ - cM⁻¹| ≤ 0.14 * gridUnit q := by
    rw [inv_sub_inv hcMh0.ne' hcM0.ne', abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h1 : |cM - cMh| ≤ gridUnit q / 32 := by rw [abs_sub_comm]; exact hMh
    nlinarith
  have hrat : |cmh / cMh - cm / cM| ≤ 0.14 * gridUnit q := by
    rw [div_sub_div _ _ hcMh0.ne' hcM0.ne', abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hnum : cmh * cM - cMh * cm = (cmh - cm) * cM - (cMh - cM) * cm := by ring
    rw [hnum]
    have e1 : |(cmh - cm) * cM| ≤ gridUnit q / 32 * cM := by
      rw [abs_mul, abs_of_pos hcM0]; exact mul_le_mul_of_nonneg_right hmh hcM0.le
    have e2 : |(cMh - cM) * cm| ≤ gridUnit q / 32 * cm := by
      rw [abs_mul, abs_of_nonneg hcm]; exact mul_le_mul_of_nonneg_right hMh hcm
    have e3 := abs_sub ((cmh - cm) * cM) ((cMh - cM) * cm)
    have e4 : gridUnit q / 32 * cm ≤ gridUnit q / 32 * cM :=
      mul_le_mul_of_nonneg_left hlt.le (by positivity)
    have e5 : 0.14 * gridUnit q * (0.46 * cM) ≤ 0.14 * gridUnit q * (cMh * cM) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcMh hcM0.le) (by positivity)
    nlinarith
  have hq1 := abs_rr_sub_le hrr q μ'
  have hq2 := abs_rr_sub_le hrr q a''
  constructor
  · have t1 := abs_sub_le (rr q μ') μ' cM⁻¹
    have t2 := abs_sub_le μ' cMh⁻¹ cM⁻¹
    linarith
  · have hy : 0 ≤ cm / cM := div_nonneg hcm hcM0.le
    have hmax : |max 0 (rr q a'') - cm / cM| ≤ |rr q a'' - cm / cM| := by
      have h := abs_max_sub_max_le_abs (rr q a'') (cm / cM) 0
      rwa [max_comm (rr q a'') 0, max_eq_left hy] at h
    have t1 := abs_sub_le (rr q a'') a'' (cm / cM)
    have t2 := abs_sub_le a'' (cmh / cMh) (cm / cM)
    linarith

/-- Lemma 4.6 (bridge Lemma C)(iii) solver entries (Lemma B.3 (`lem:phase-tables`)). -/
theorem lemmaC_iii_solver : LemmaC_iii_solverStmt := by
  intro rr hrr q c0 c1 c0h c1h μ' a'' uS hc0 hc1 hmax hne h0 h1 huS hμ ha
  have hε : (2 : ℝ) ^ (-(((q + 1) + 4 : ℕ) : ℤ)) = gridUnit q / 32 := by
    rw [two_zpow_neg_natCast_eq_gridUnit, show q + 1 + 4 = q + 5 by ring,
      gridUnit_add_eq_mul q 5]
    have h5 : gridUnit 5 = 1 / 32 := by unfold gridUnit; norm_num
    rw [h5]; ring
  have huS' : uS ≤ gridUnit q / 32 := by
    refine huS.2.trans ?_
    rw [two_zpow_neg_natCast_eq_gridUnit, ← hε, two_zpow_neg_natCast_eq_gridUnit]
    exact gridUnit_anti (by omega)
  rw [hε] at h0 h1
  by_cases h : c1 < c0
  · rw [if_pos h] at hμ ha
    rw [max_eq_left h.le, min_eq_right h.le]
    exact solver_oriented rr hrr q c0 c1 c0h c1h μ' a'' uS hc1 h (by rwa [max_eq_left h.le] at hmax)
      h0 h1 huS' hμ ha
  · rw [if_neg h] at hμ ha
    have h' : c0 < c1 := lt_of_le_of_ne (not_lt.mp h) hne
    rw [max_eq_right h'.le, min_eq_left h'.le]
    exact solver_oriented rr hrr q c1 c0 c1h c0h μ' a'' uS hc0 h' (by rwa [max_eq_right h'.le] at hmax)
      h1 h0 huS' hμ ha

/-! ## Phases -/

/-- Lemma 4.6 (bridge Lemma C)(iii) phases (Lemma B.3 (`lem:phase-tables`)). Only `v ≤ 1` is used. -/
theorem lemmaC_iii_phase : LemmaC_iii_phaseStmt := by
  intro q _hq eph e0 he h0
  have hv : 0 < gridUnit q := gridUnit_pos q
  have hv1 : gridUnit q ≤ 1 := gridUnit_le_one' q
  have hcoef : (1 - (gridUnit q : ℂ) / 8) = ((1 - gridUnit q / 8 : ℝ) : ℂ) := by push_cast; ring
  have hnc : ‖(1 - (gridUnit q : ℂ) / 8)‖ = 1 - gridUnit q / 8 := by
    rw [hcoef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hnv : ‖(gridUnit q : ℂ) / 8‖ = gridUnit q / 8 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]; norm_num
  have he0 : ‖e0‖ < 1 + gridUnit q / 16 := by
    calc ‖e0‖ = ‖(e0 - eph) + eph‖ := by ring_nf
      _ ≤ ‖e0 - eph‖ + ‖eph‖ := norm_add_le _ _
      _ < 1 + gridUnit q / 16 := by rw [he]; linarith
  have hz : ‖(1 - (gridUnit q : ℂ) / 8) * e0‖ < 1 := by
    rw [norm_mul, hnc]
    calc (1 - gridUnit q / 8) * ‖e0‖ ≤ (1 - gridUnit q / 8) * (1 + gridUnit q / 16) :=
          mul_le_mul_of_nonneg_left he0.le (by linarith)
      _ < 1 := by nlinarith
  have hzerr : ‖(1 - (gridUnit q : ℂ) / 8) * e0 - eph‖ ≤
      gridUnit q / 16 + gridUnit q / 8 * (1 + gridUnit q / 16) := by
    have hrw : (1 - (gridUnit q : ℂ) / 8) * e0 - eph = (e0 - eph) - ((gridUnit q : ℂ) / 8) * e0 := by
      ring
    rw [hrw]
    calc ‖(e0 - eph) - ((gridUnit q : ℂ) / 8) * e0‖ ≤ ‖e0 - eph‖ + ‖((gridUnit q : ℂ) / 8) * e0‖ :=
          norm_sub_le _ _
      _ ≤ gridUnit q / 16 + gridUnit q / 8 * (1 + gridUnit q / 16) := by
          rw [norm_mul, hnv]
          have : gridUnit q / 8 * ‖e0‖ ≤ gridUnit q / 8 * (1 + gridUnit q / 16) :=
            mul_le_mul_of_nonneg_left he0.le (by positivity)
          linarith
  have hs2 := sqrt_two_lt_14143
  constructor
  · exact (norm_truncC_le q _).trans hz.le
  · calc ‖truncC q ((1 - (gridUnit q : ℂ) / 8) * e0) - eph‖
        ≤ ‖truncC q ((1 - (gridUnit q : ℂ) / 8) * e0) - (1 - (gridUnit q : ℂ) / 8) * e0‖ +
          ‖(1 - (gridUnit q : ℂ) / 8) * e0 - eph‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < Real.sqrt 2 * gridUnit q + (gridUnit q / 16 + gridUnit q / 8 * (1 + gridUnit q / 16)) :=
          add_lt_add_of_lt_of_le (norm_truncC_sub_lt q _) hzerr
      _ ≤ 2 * gridUnit q := by nlinarith

/-- Lemma 4.6 (bridge Lemma C)(iii) phase multiplication (Lemma B.3 (`lem:phase-tables`)). -/
theorem lemmaC_iii_phase_mul : LemmaC_iii_phase_mulStmt := by
  intro q z eh eph hz heh _heph h
  have hv : 0 < gridUnit q := gridUnit_pos q
  constructor
  · calc ‖truncC q (eh * z)‖ ≤ ‖eh * z‖ := norm_truncC_le q _
      _ = ‖eh‖ * ‖z‖ := norm_mul _ _
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right heh (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  · have h1 : ‖eh * z - eph * z‖ ≤ 2 * gridUnit q := by
      rw [← sub_mul, norm_mul]
      calc ‖eh - eph‖ * ‖z‖ ≤ ‖eh - eph‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        _ ≤ 2 * gridUnit q := by rw [mul_one]; exact h.le
    have hs2 := sqrt_two_lt_14143
    calc ‖truncC q (eh * z) - eph * z‖
        ≤ ‖truncC q (eh * z) - eh * z‖ + ‖eh * z - eph * z‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < Real.sqrt 2 * gridUnit q + 2 * gridUnit q :=
          add_lt_add_of_lt_of_le (norm_truncC_sub_lt q _) h1
      _ ≤ 4 * gridUnit q := by nlinarith

end SubNLogN.Math.Bridge
