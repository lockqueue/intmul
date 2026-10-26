import SubNLogN.Math.Walsh.PhaseTable

/-!
# Proofs of Lemma 6.1 (disk-valued phases) and Lemma 6.2 (disk-preserving products)

Paper: Lemma 6.1 (`lem:phase-table`) and Lemma 6.2 (`lem:disk-product`). Proves `phase_table : PhaseTableStmt` and
`disk_product : DiskProductStmt` (statements in `SubNLogN/Math/Walsh/PhaseTable.lean`).

Proof of Lemma 6.1 for the concrete table `phaseTableNum`: the fourth roots of unity are exact; for
the other entries the certified IntMul evaluation `α` of `θ_j` has error at most
`2 · complexQuantizeMaxErr (P+6) = √2 · 2^{-P}/128`, and `θ̃_j = Q_P((1 - 2^{-P}/8) α)`
(`phaseTable_eq_truncC`); then `|θ̃_j| ≤ (1 - u/8)(1 + e) ≤ 1` and
`|θ̃_j - θ_j| < √2 u + (u/8)(1 + e) + e < 2u` with `u = 2^{-P}`, `e = √2 u/128` (proof of
Lemma 6.1 (`lem:phase-table`)).
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-! ## Lemma 6.2 -/

/-- **Lemma 6.2** (`lem:disk-product`). -/
theorem disk_product : DiskProductStmt := by
  intro P a b ha hb
  refine ⟨ha.1.mul hb.1, truncC_mem_diskGrid P _ ?_, norm_truncC_sub_lt P _⟩
  rw [norm_mul]
  exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2

/-! ## Auxiliary facts -/

private theorem floor_intCast_div_natCast_real (m : ℤ) (d : ℕ) :
    ⌊(m : ℝ) / (d : ℝ)⌋ = m / (d : ℤ) := by
  have h : ((m : ℝ) / (d : ℝ)) = (((m : ℚ) / (d : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h, Rat.floor_cast, Rat.floor_intCast_div_natCast]

/-- Truncation toward zero of `m / d` is `Int.tdiv m d` (`d > 0`). -/
private theorem truncInt_intCast_div (m : ℤ) (d : ℕ) (hd : 0 < d) :
    truncInt ((m : ℝ) / (d : ℝ)) = m.tdiv d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold truncInt
  by_cases hm : 0 ≤ m
  · have hx : (0 : ℝ) ≤ (m : ℝ) / d := div_nonneg (by exact_mod_cast hm) hd'.le
    rw [if_pos hx, floor_intCast_div_natCast_real, Int.tdiv_eq_ediv_of_nonneg hm]
  · replace hm : m < 0 := not_le.mp hm
    have hx : ¬ (0 : ℝ) ≤ (m : ℝ) / d := by
      rw [not_le]; exact div_neg_of_neg_of_pos (by exact_mod_cast hm) hd'
    rw [if_neg hx]
    have h1 : ((m : ℝ) / d) = -(((-m : ℤ) : ℝ) / d) := by push_cast; ring
    rw [h1, Int.ceil_neg, floor_intCast_div_natCast_real,
      ← Int.tdiv_eq_ediv_of_nonneg (a := -m) (b := (d : ℤ)) (by omega), Int.neg_tdiv, neg_neg]

private theorem norm_theta (r j : ℕ) : ‖theta r j‖ = 1 := by
  unfold theta IntMul.stdChar
  exact Complex.norm_exp_ofReal_mul_I _

private theorem onGrid_I_pow (P n : ℕ) : OnGrid P (Complex.I ^ n) := by
  induction n with
  | zero =>
    have h := onGrid_intCast P 1 0
    have e : (⟨((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)⟩ : ℂ) = 1 := by apply Complex.ext <;> simp
    rw [pow_zero, ← e]
    exact h
  | succ n ih => rw [pow_succ]; exact ih.mul_I

private theorem gridUnit_le_one (P : ℕ) : gridUnit P ≤ 1 := by
  unfold gridUnit
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- If `r | 2j` then `θ_j = i^{2j/r}`. -/
private theorem theta_eq_I_pow (ℓ j : ℕ) (h : (2 * j) % 2 ^ ℓ = 0) :
    theta (2 ^ ℓ) j = Complex.I ^ (2 * j / 2 ^ ℓ) := by
  have hq : 2 * j = 2 ^ ℓ * (2 * j / 2 ^ ℓ) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)).symm
  set q := 2 * j / 2 ^ ℓ with hqdef
  have hqR : (2 : ℝ) * j = (2 : ℝ) ^ ℓ * q := by exact_mod_cast hq
  unfold theta IntMul.stdChar
  have hx : (2 * Real.pi * ((j : ℝ) / (2 * ((2 ^ ℓ : ℕ) : ℝ)))) = (q : ℝ) * (Real.pi / 2) := by
    have hj : (j : ℝ) = (2 : ℝ) ^ ℓ * q / 2 := by linarith
    rw [hj]
    push_cast
    field_simp
  rw [hx]
  have e : (((q : ℝ) * (Real.pi / 2) : ℝ) : ℂ) * Complex.I =
      (q : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]

/-- The exact branch of the table returns `θ_j` (fourth roots of unity are exact). -/
private theorem phaseTable_fourth_root (P ℓ j : ℕ) (h : (2 * j) % 2 ^ ℓ = 0) :
    phaseTable P ℓ j = theta (2 ^ ℓ) j := by
  rw [theta_eq_I_pow ℓ j h]
  have hI : Complex.I ^ (2 * j / 2 ^ ℓ) = Complex.I ^ ((2 * j / 2 ^ ℓ) % 4) := by
    conv_lhs => rw [← Nat.div_add_mod (2 * j / 2 ^ ℓ) 4]
    rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [hI]
  have h4 : (2 * j / 2 ^ ℓ) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold phaseTable phaseTableNum
  rw [if_pos h]
  generalize (2 * j / 2 ^ ℓ) % 4 = t at h4 ⊢
  interval_cases t <;> apply Complex.ext <;> simp [gridUnit, pow_succ]

/-- The non-exact branch of the table is `Q_P((1 - 2^{-P}/8) α)` with `α` the IntMul evaluation. -/
private theorem phaseTable_eq_truncC (P ℓ j : ℕ) (h : ¬ (2 * j) % 2 ^ ℓ = 0) :
    phaseTable P ℓ j = truncC P (((1 - gridUnit P / 8 : ℝ) : ℂ) *
      IntMul.toScaledComplex (P + 6)
        (IntMul.computableStdCharWithProgramCost (P + 6) j (2 * 2 ^ ℓ) false).1) := by
  unfold phaseTable phaseTableNum
  rw [if_neg h]
  generalize (IntMul.computableStdCharWithProgramCost (P + 6) j (2 * 2 ^ ℓ) false).1 = a
  have hd : 0 < 2 ^ (P + 11) := Nat.two_pow_pos _
  have key : ∀ c : ℤ, (1 - gridUnit P / 8) * ((c : ℝ) / 2 ^ (P + 6 + 2)) * 2 ^ P =
      ((c * (2 ^ (P + 3) - 1) : ℤ) : ℝ) / ((2 ^ (P + 11) : ℕ) : ℝ) := by
    intro c
    unfold gridUnit
    push_cast
    field_simp
    ring
  apply Complex.ext
  · simp only [truncC_re, truncR, Complex.re_ofReal_mul, IntMul.toScaledComplex]
    rw [key, truncInt_intCast_div _ _ hd]
    push_cast
    ring
  · simp only [truncC_im, truncR, Complex.im_ofReal_mul, IntMul.toScaledComplex]
    rw [key, truncInt_intCast_div _ _ hd]
    push_cast
    ring

/-- The certified error of the IntMul evaluation: `‖α - θ_j‖ ≤ √2 · 2^{-P} / 128`. -/
private theorem norm_alpha_sub_theta (P ℓ j : ℕ) (hj : j < 2 * 2 ^ ℓ) :
    ‖IntMul.toScaledComplex (P + 6)
        (IntMul.computableStdCharWithProgramCost (P + 6) j (2 * 2 ^ ℓ) false).1 -
      theta (2 ^ ℓ) j‖ ≤ Real.sqrt 2 * gridUnit P / 128 := by
  have herr := IntMul.computableStdCharWithProgramCost_error_le (P + 6) j (2 * 2 ^ ℓ) false
    (by positivity) hj.le
  have hth : IntMul.stdChar ((if false = true then -(j : ℝ) else (j : ℝ)) /
      ((2 * 2 ^ ℓ : ℕ) : ℝ)) = theta (2 ^ ℓ) j := by
    unfold theta
    congr 1
    push_cast
    simp
  rw [hth] at herr
  refine herr.trans (le_of_eq ?_)
  unfold IntMul.complexQuantizeMaxErr gridUnit
  rw [show (-(((P + 6 : ℕ) : ℤ) + 2)) = -((P + 8 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast]
  field_simp
  ring

/-- **Lemma 6.1** (`lem:phase-table`) for the concrete table `phaseTable`. -/
theorem phase_table : PhaseTableStmt := by
  intro P ℓ _ _
  refine ⟨fun j hj => ?_, fun j _ h => phaseTable_fourth_root P ℓ j h⟩
  by_cases h : (2 * j) % 2 ^ ℓ = 0
  · rw [phaseTable_fourth_root P ℓ j h]
    refine ⟨?_, (norm_theta _ _).le, ?_⟩
    · rw [theta_eq_I_pow ℓ j h]
      exact onGrid_I_pow P _
    · rw [sub_self, norm_zero]
      exact mul_pos two_pos (gridUnit_pos P)
  · rw [phaseTable_eq_truncC P ℓ j h]
    have hα := norm_alpha_sub_theta P ℓ j hj
    set α := IntMul.toScaledComplex (P + 6)
      (IntMul.computableStdCharWithProgramCost (P + 6) j (2 * 2 ^ ℓ) false).1 with hαdef
    set θ := theta (2 ^ ℓ) j with hθdef
    set u := gridUnit P with hudef
    have hu0 : 0 < u := gridUnit_pos P
    have hu1 : u ≤ 1 := gridUnit_le_one P
    have hs2 : Real.sqrt 2 < 3 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hθ1 : ‖θ‖ = 1 := norm_theta _ _
    have he : ‖α - θ‖ ≤ 3 * u / 256 := by nlinarith
    have hαn : ‖α‖ ≤ 1 + 3 * u / 256 := by
      have := norm_le_insert' α θ
      linarith [norm_sub_rev α θ]
    have hc0 : 0 ≤ 1 - u / 8 := by linarith
    have hβ : ‖((1 - u / 8 : ℝ) : ℂ) * α‖ = (1 - u / 8) * ‖α‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    have hβ1 : ‖((1 - u / 8 : ℝ) : ℂ) * α‖ ≤ 1 := by
      rw [hβ]; nlinarith [norm_nonneg α]
    have hβα : ‖((1 - u / 8 : ℝ) : ℂ) * α - α‖ = u / 8 * ‖α‖ := by
      have e : ((1 - u / 8 : ℝ) : ℂ) * α - α = ((-(u / 8) : ℝ) : ℂ) * α := by
        push_cast; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by linarith)]
    refine ⟨truncC_onGrid P _, (norm_truncC_le P _).trans hβ1, ?_⟩
    have htr := norm_truncC_sub_lt P (((1 - u / 8 : ℝ) : ℂ) * α)
    have htri : ‖truncC P (((1 - u / 8 : ℝ) : ℂ) * α) - θ‖ ≤
        ‖truncC P (((1 - u / 8 : ℝ) : ℂ) * α) - ((1 - u / 8 : ℝ) : ℂ) * α‖ +
          ‖((1 - u / 8 : ℝ) : ℂ) * α - α‖ + ‖α - θ‖ := by
      calc _ = ‖(truncC P (((1 - u / 8 : ℝ) : ℂ) * α) - ((1 - u / 8 : ℝ) : ℂ) * α) +
              (((1 - u / 8 : ℝ) : ℂ) * α - α) + (α - θ)‖ := by congr 1; ring
        _ ≤ _ := norm_add₃_le
    rw [hβα] at htri
    nlinarith [norm_nonneg α]

end SubNLogN.Math.Walsh
