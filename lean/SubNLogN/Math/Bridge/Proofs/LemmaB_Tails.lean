import SubNLogN.Math.Bridge.LemmaB_Scalar

/-!
# Bridge: Lemma 4.4 (bridge Lemma B)(ii) scalar core and Lemma 4.4 (bridge Lemma B)(iii) (`lem:bridge-B`)

Proves the contracts `Omitted_weight_ltStmt` and `LemmaB_iiiStmt` of
`SubNLogN/Math/Bridge/LemmaB_Scalar.lean` directly from the IntMul erf development
(`IntMul/Theorem3BidiagonalAndSchedule.lean`). No pending contract is assumed. (Names `LemmaB*`/`lemmaB*` reflect an earlier draft (bridge Lemma B), now Lemma 4.4 (`lem:bridge-B`), kept for stability.)

Proof plan (all helpers live in the namespace `SubNLogN.Math.Bridge.LemmaBTails`):
1. `kernelG α ξ = IntMul.gHatBox (IntMul.realErfScaled α) ξ` for `α > 0` (substitution
   `t = √π α v` in eq. (`eq:G`)), hence `G(y) = c₀(y)` and `G(y - 1) = G(1 - y) = c₁(y)` in the
   notation `IntMul.c0Coeff`, `IntMul.c1Coeff`.
2. B(ii): `1 - G(y) - G(y-1) = ½erfc(a(y+½)) + ½erfc(a(3/2-y)) ≤ ½φ(y+½) + ½φ(3/2-y)` with the
   Mills-ratio bound `φ(z) = e^{-πα²z²}/(παz)` (`IntMul.theorem3_stopband_alias_le_gaussian_tails`).
   Instead of the paper's convexity argument we use that `φ` is decreasing on `(0,∞)` and that, for
   `y ∈ (0,1)`, one of the two arguments `y+½`, `3/2-y` is `≥ ½` and the other is `≥ 1`; hence
   `Ψ(y) ≤ ½φ(½) + ½φ(1) ≤ 2^{-ω}/(πα) + 2^{-4ω}/(2πα)`, and admissibility gives
   `πα ≥ 2√(πω ln 2) > 8.3334`. (The second term is weaker than the paper's `Ψ(0)` bound,
   `2^{-4ω}` instead of `2^{-9ω}`; this is irrelevant for the constant `0.120`.)
3. B(iii): `max(c₀,c₁) ≥ c₀(½) = ½erf(a) = ½ - ½erfc(a) ≥ ½ - ½φ(1) ≥ ½ - 0.060·2^{-4ω}`.

Only the lower end of the admissible range of `α` is used.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common

namespace LemmaBTails

open IntMul

/-- Eq. (`eq:G`) in erf form: for `α > 0`, `kernelG α ξ = gHatBox (realErfScaled α) ξ`
(substitution `t = √π α v`). -/
theorem kernelG_eq_gHatBox_of_pos (α ξ : ℝ) (hα : 0 < α) :
    kernelG α ξ = gHatBox (realErfScaled α) ξ := by
  rw [(theorem3_concrete_box_gaussian_integral_and_telescoping α ξ 0).1]
  unfold kernelG
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hc : 0 < Real.sqrt Real.pi * α := mul_pos hsqrt hα
  have hsq : ∀ v : ℝ, Real.pi * α ^ 2 * v ^ 2 = (Real.sqrt Real.pi * α * v) ^ 2 := by
    intro v
    rw [mul_pow, mul_pow, Real.sq_sqrt hpi.le]
  simp only [hsq]
  rw [intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_mul_left (a := ξ - 1 / 2) (b := ξ + 1 / 2)
    (fun t : ℝ => Real.exp (-(t ^ 2))) hc.ne'
  rw [hsub, smul_eq_mul, ← mul_assoc]
  congr 1
  field_simp

/-- `G(y) = c₀(y)` for `α > 0`. -/
theorem kernelG_eq_c0 (α y : ℝ) (hα : 0 < α) :
    kernelG α y = c0Coeff (realErfScaled α) y :=
  kernelG_eq_gHatBox_of_pos α y hα

/-- `G(y - 1) = G(1 - y) = c₁(y)` for `α > 0`. -/
theorem kernelG_sub_one_eq_c1 (α y : ℝ) (hα : 0 < α) :
    kernelG α (y - 1) = c1Coeff (realErfScaled α) y := by
  rw [kernelG_eq_gHatBox_of_pos α (y - 1) hα, c1Coeff,
    ← gHatBox_even (realErfScaled α) (realErfScaled_neg α) (1 - y)]
  congr 1
  ring

/-- The Mills-ratio majorant `φ(z) = e^{-πα²z²}/(παz)` of `erfc(√π α z)`:
`erfcScaled (realErfScaled α) z ≤ φ(z)` for `α, z > 0`
(`IntMul.erfcScaled_realErfScaled_le_gaussian_tail`). -/
noncomputable def millsTail (α z : ℝ) : ℝ :=
  Real.exp (-(Real.pi * α ^ 2 * z ^ 2)) / (Real.pi * α * z)

/-- `φ` is antitone on `(0, ∞)`. -/
theorem millsTail_anti (α z₀ z : ℝ) (hα : 0 < α) (hz₀ : 0 < z₀) (hz : z₀ ≤ z) :
    millsTail α z ≤ millsTail α z₀ := by
  unfold millsTail
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc2 : 0 ≤ Real.pi * α ^ 2 := by positivity
  have hc1 : 0 ≤ Real.pi * α := by positivity
  apply div_le_div₀ (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have h1 : z₀ ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hz₀.le hz 2
    have h2 := mul_le_mul_of_nonneg_left h1 hc2
    linarith
  · positivity
  · exact mul_le_mul_of_nonneg_left hz hc1

/-- Omitted weight via the Mills bound, without convexity: for `y ∈ (0,1)`,
`1 - G(y) - G(y-1) ≤ ½φ(½) + ½φ(1)`. -/
theorem omitted_weight_le_mills (α y : ℝ) (hα : 0 < α) (hy : 0 < y ∧ y < 1) :
    1 - kernelG α y - kernelG α (y - 1) ≤
      (1 / 2 : ℝ) * millsTail α (1 / 2) + (1 / 2 : ℝ) * millsTail α 1 := by
  rw [kernelG_sub_one_eq_c1 α y hα, kernelG_eq_c0 α y hα]
  have h := theorem3_stopband_alias_le_gaussian_tails α y hα (by linarith [hy.1])
    (by linarith [hy.2])
  change _ ≤ (1 / 2 : ℝ) * millsTail α (y + 1 / 2) + (1 / 2 : ℝ) * millsTail α (3 / 2 - y) at h
  rcases le_total y (1 / 2) with hy2 | hy2
  · have h1 := millsTail_anti α (1 / 2) (y + 1 / 2) hα (by norm_num) (by linarith [hy.1])
    have h2 := millsTail_anti α 1 (3 / 2 - y) hα one_pos (by linarith)
    linarith
  · have h1 := millsTail_anti α 1 (y + 1 / 2) hα one_pos (by linarith)
    have h2 := millsTail_anti α (1 / 2) (3 / 2 - y) hα (by norm_num) (by linarith [hy.2])
    linarith

/-! ### Numerical consequences of admissibility (`a = √π α ≥ 2√(ω ln 2)`) -/

/-- Admissibility (lower end) gives `πα² ≥ 4ω ln 2`, i.e. `a² ≥ 4ω ln 2`. -/
theorem four_mul_log_le_pi_mul_sq (ω : ℕ) (α : ℝ)
    (hα : 2 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) ≤ α) :
    4 * ((ω : ℝ) * Real.log 2) ≤ Real.pi * α ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrad : 0 ≤ (ω : ℝ) * Real.log 2 / Real.pi :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog.le) hpi.le
  set s := Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (ω : ℝ) * Real.log 2 / Real.pi := Real.sq_sqrt hrad
  have hα2 : (2 * s) ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ (by linarith) hα 2
  have h1 : Real.pi * s ^ 2 = (ω : ℝ) * Real.log 2 := by
    rw [hs2]; field_simp [hpi.ne']
  have h2 := mul_le_mul_of_nonneg_left hα2 hpi.le
  have h3 : Real.pi * (2 * s) ^ 2 = 4 * ((ω : ℝ) * Real.log 2) := by
    rw [← h1]; ring
  linarith

/-- Admissibility (lower end) and `ω ≥ 8` give `πα > 8.345` (`(πα)² ≥ 32π ln 2 > 69.64`). -/
theorem pi_mul_alpha_gt (ω : ℕ) (hω : 8 ≤ ω) (α : ℝ)
    (hα : 2 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) ≤ α) (hα0 : 0 < α) :
    (8.345 : ℝ) < Real.pi * α := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hω' : (8 : ℝ) ≤ ω := by exact_mod_cast hω
  have h := four_mul_log_le_pi_mul_sq ω α hα
  have h8 : 8 * Real.log 2 ≤ (ω : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hω' (by linarith)
  have h1 : (22.18 : ℝ) ≤ Real.pi * α ^ 2 := by linarith
  have h2 : (3.14 : ℝ) * 22.18 ≤ Real.pi * (Real.pi * α ^ 2) :=
    mul_le_mul hpi.le h1 (by norm_num) hpi_pos.le
  have h3 : (Real.pi * α) ^ 2 = Real.pi * (Real.pi * α ^ 2) := by ring
  have hpos : 0 < Real.pi * α := mul_pos hpi_pos hα0
  nlinarith

/-- `e^{-n ln 2} = 2^{-n}`. -/
theorem exp_neg_nat_mul_log_two (n : ℕ) :
    Real.exp (-((n : ℝ) * Real.log 2)) = (2 : ℝ) ^ (-(n : ℤ)) := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log zero_lt_two, zpow_neg, zpow_natCast]

/-- `e^{-a²/4} = e^{-πα²(1/2)²} ≤ 2^{-ω}`. -/
theorem exp_half_le (ω : ℕ) (α : ℝ)
    (hα : 2 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) ≤ α) :
    Real.exp (-(Real.pi * α ^ 2 * (1 / 2) ^ 2)) ≤ (2 : ℝ) ^ (-(ω : ℤ)) := by
  have h := four_mul_log_le_pi_mul_sq ω α hα
  rw [← exp_neg_nat_mul_log_two ω]
  apply Real.exp_le_exp.mpr
  linarith

/-- `e^{-a²} = e^{-πα²·1²} ≤ 2^{-4ω}`. -/
theorem exp_one_le (ω : ℕ) (α : ℝ)
    (hα : 2 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) ≤ α) :
    Real.exp (-(Real.pi * α ^ 2 * 1 ^ 2)) ≤ (2 : ℝ) ^ (-(4 * (ω : ℤ))) := by
  have h := four_mul_log_le_pi_mul_sq ω α hα
  have hcast : (2 : ℝ) ^ (-(4 * (ω : ℤ))) = (2 : ℝ) ^ (-((4 * ω : ℕ) : ℤ)) := by
    have he : -(4 * (ω : ℤ)) = -((4 * ω : ℕ) : ℤ) := by omega
    rw [he]
  rw [hcast, ← exp_neg_nat_mul_log_two (4 * ω)]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

/-- Admissible `α` is positive (for `ω ≥ 8`). -/
theorem alpha_pos_of_admissible (ω : ℕ) (hω : 8 ≤ ω) (α : ℝ)
    (hα : 2 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) ≤ α) : 0 < α := by
  have hω' : (8 : ℝ) ≤ ω := by exact_mod_cast hω
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrad : 0 < (ω : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos (by linarith) hlog) Real.pi_pos
  exact lt_of_lt_of_le (mul_pos two_pos (Real.sqrt_pos.mpr hrad)) hα

end LemmaBTails

open LemmaBTails IntMul in
/-- **Lemma 4.4 (bridge Lemma B)(ii), scalar core** (`lem:bridge-B`): for `ω ≥ 8`, admissible `α` and every
sample `y ∈ (0,1)`, the omitted alias weight satisfies `1 - G(y) - G(y-1) < 0.120·2^{-ω}`.
Proved via `Ψ(y) ≤ ½φ(½) + ½φ(1) ≤ 0.1199·2^{-ω} + 0.06·2^{-4ω}` (see the module docstring). -/
theorem omitted_weight_lt : Omitted_weight_ltStmt := by
  intro ω hω α hα y hy
  obtain ⟨hαlo, -⟩ := hα
  have hα0 : 0 < α := alpha_pos_of_admissible ω hω α hαlo
  have hmain := omitted_weight_le_mills α y hα0 hy
  have hA := pi_mul_alpha_gt ω hω α hαlo hα0
  have hA0 : 0 < Real.pi * α := by linarith
  have he1 := exp_half_le ω α hαlo
  have he2 := exp_one_le ω α hαlo
  have hP : 0 < (2 : ℝ) ^ (-(ω : ℤ)) := zpow_pos (by norm_num) _
  have hQ : 0 < (2 : ℝ) ^ (-(4 * (ω : ℤ))) := zpow_pos (by norm_num) _
  have hz : (2 : ℝ) ^ (-(4 * (ω : ℤ))) ≤ (2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(ω : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  rw [h24] at hz
  have hinv : 1 / (Real.pi * α) ≤ 0.1199 := by
    rw [div_le_iff₀ hA0]; linarith
  have hm1 : (1 / 2 : ℝ) * millsTail α (1 / 2) =
      Real.exp (-(Real.pi * α ^ 2 * (1 / 2) ^ 2)) * (1 / (Real.pi * α)) := by
    unfold millsTail; ring
  have hm2 : (1 / 2 : ℝ) * millsTail α 1 =
      Real.exp (-(Real.pi * α ^ 2 * 1 ^ 2)) * (1 / (Real.pi * α)) / 2 := by
    unfold millsTail; ring
  have hb1 : Real.exp (-(Real.pi * α ^ 2 * (1 / 2) ^ 2)) * (1 / (Real.pi * α)) ≤
      (2 : ℝ) ^ (-(ω : ℤ)) * 0.1199 :=
    mul_le_mul he1 hinv (by positivity) hP.le
  have hb2 : Real.exp (-(Real.pi * α ^ 2 * 1 ^ 2)) * (1 / (Real.pi * α)) ≤
      (2 : ℝ) ^ (-(4 * (ω : ℤ))) * 0.1199 :=
    mul_le_mul he2 hinv (by positivity) hQ.le
  linarith

open LemmaBTails IntMul in
/-- **Lemma 4.4 (bridge Lemma B)(iii)** (`lem:bridge-B`): for `ω ≥ 8`, admissible `α`, `t ≥ 2` and every
frequency digit `u < t`, with `y = (u+½)/t`: `max(G(y), G(y-1)) ≥ G(½) = ½erf(a) ≥
½ - 0.060·2^{-4ω}`, and `½ - 0.060·2^{-4ω} > 0.49999999`. (The power-of-two hypothesis on `t`
is not needed.) -/
theorem lemmaB_iii : LemmaB_iiiStmt := by
  intro ω hω α hα t ht u hu
  obtain ⟨hαlo, -⟩ := hα
  have hα0 : 0 < α := alpha_pos_of_admissible ω hω α hαlo
  have hA := pi_mul_alpha_gt ω hω α hαlo hα0
  have hA0 : 0 < Real.pi * α := by linarith
  have he2 := exp_one_le ω α hαlo
  have hQ : 0 < (2 : ℝ) ^ (-(4 * (ω : ℤ))) := zpow_pos (by norm_num) _
  have hinv : 1 / (Real.pi * α) ≤ 0.12 := by
    rw [div_le_iff₀ hA0]; linarith
  -- `c₀(½) = ½·erf(a) = ½ - ½·erfc(a) ≥ ½ - ½φ(1) ≥ ½ - 0.060·2^{-4ω}`
  have hnyq := (theorem3_nyquist_passband_eq (realErfScaled α) (realErfScaled_zero α)).1
  have herfc := erfcScaled_realErfScaled_le_gaussian_tail α 1 hα0 one_pos
  have hc0half : (1 / 2 : ℝ) - 0.060 * (2 : ℝ) ^ (-(4 * (ω : ℤ))) ≤
      c0Coeff (realErfScaled α) (1 / 2) := by
    rw [hnyq]
    unfold erfcScaled at herfc
    have hb : Real.exp (-(Real.pi * α ^ 2 * 1 ^ 2)) / (Real.pi * α * 1) ≤
        (2 : ℝ) ^ (-(4 * (ω : ℤ))) * 0.12 := by
      have heq : Real.exp (-(Real.pi * α ^ 2 * 1 ^ 2)) / (Real.pi * α * 1) =
          Real.exp (-(Real.pi * α ^ 2 * 1 ^ 2)) * (1 / (Real.pi * α)) := by ring
      rw [heq]
      exact mul_le_mul he2 hinv (by positivity) hQ.le
    linarith
  -- the sample `y = (u + ½)/t` lies in `[0, 1]`
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hut : (u : ℝ) + 1 ≤ t := by exact_mod_cast (show u + 1 ≤ t by omega)
  set y : ℝ := ((u : ℝ) + 1 / 2) / t with hy_def
  have hy0 : 0 ≤ y := by rw [hy_def]; positivity
  have hy1 : y ≤ 1 := by rw [hy_def, div_le_one₀ ht0]; linarith
  refine ⟨?_, ?_⟩
  · rw [kernelG_eq_c0 α y hα0, kernelG_sub_one_eq_c1 α y hα0]
    rcases le_total y (1 / 2) with hy2 | hy2
    · exact le_max_of_le_left (hc0half.trans (c0Coeff_ge_at_half α y hα0 hy0 hy2))
    · have h := c0Coeff_ge_at_half α (1 - y) hα0 (by linarith) (by linarith)
      have hc1 : c1Coeff (realErfScaled α) y = c0Coeff (realErfScaled α) (1 - y) := rfl
      exact le_max_of_le_right (hc0half.trans (h.trans_eq hc1.symm))
  · have hz : (2 : ℝ) ^ (-(4 * (ω : ℤ))) ≤ (2 : ℝ) ^ (-32 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have h32 : (2 : ℝ) ^ (-32 : ℤ) = 1 / 4294967296 := by norm_num
    rw [h32] at hz
    linarith

end SubNLogN.Math.Bridge
