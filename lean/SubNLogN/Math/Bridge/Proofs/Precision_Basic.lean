import SubNLogN.Math.Bridge.Precision

/-!
# Bridge: Theorem 4.7 — constant, master margin, rounding, alias and assembly

Proofs of contracts of `SubNLogN/Math/Bridge/Precision.lean` (Theorem 4.7
(`thm:bridge-precision`)):

* `bridge_constant_lt : Bridge_constant_ltStmt` — `√2/8 + 2^{-12} + 2^{-23} < 0.177021`, from
  `√2 < 1.4142136` (i.e. `1.4142136² > 2`). No hypothesis.
* `master_margin : Master_marginStmt` — eq. (`eq:master-margin`). Proved in `ℕ` with powers of two:
  with `L = ⌈log₂(p+k+2)⌉ = Nat.clog 2 (p+k+2)` (the form used in `schedP`) we have
  `p + k + 2 ≤ 2^L` and `L < 2^L`, hence `P + 1 ≤ 2^{L+9}`; also
  `d ≤ k < 2^k`. So `2^{14} d (P+1) 2^{3k} 2^{p+12} ≤ 2^{4k+L+p+35} ≤ 2^{P+2}`, which is the
  claim after dividing by `2^{P+2} 2^{p+12}`. (This is cruder than, but implies the same bound as,
  the paper's `lg(P+1) ≤ b+6` argument.) No hypothesis.
* `bridge_round_error : Bridge_round_errorStmt` — for any nearest rounding `rr`, one rounding
  `crnd rr (p+2)` per output contributes at most `(√2/2)·2^{-(p+2)} = (√2/8)·2^{-p}`
  (`norm_crnd_sub_le`). No hypothesis.
* `bridge_alias_error_of (hvi : LemmaB_viStmt) : Bridge_alias_errorStmt` — Lemma 4.4 (bridge Lemma B)(vi) applied to
  `x' = x/S` and rescaled by `S` (`F_R` is linear and `S·‖x'‖ = ‖x‖`), then
  `0.120 (d-1) D 2^{-ω} ≤ 0.120·2^{-p-20} < 2^{-p-23}`, using `d - 1 ≤ 2^{lg d}` and
  `D = R/t_1 ≤ R = 2^k`. The side conditions of B(vi) are checked here: `ω ≥ 8`,
  `alphaDefault ω` is admissible (`alphaDefault_admissible`) and the balanced shape satisfies
  `ShapeOK` (`shapeOK_of_balancedShape`).
* `bridge_precision_of (harith) (halias) (hround) (hconst) : Bridge_precisionStmt` — the triangle
  inequality through `bridgePreR rr` and `bridgeExactScaled`, `X ≥ 1`, and `crnd_onGrid`
  (`hconst` is not needed for the statement as written, whose bound is the explicit sum).
  `bridge_precision_of_arith_alias (harith) (halias)` discharges `hround`, `hconst` with the
  theorems above.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

namespace PrecisionBasic

/-- `2^{-n} = (2^n)⁻¹` for natural `n`. -/
theorem two_zpow_neg_natCast (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = ((2 : ℝ) ^ n)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

/-- `n ≤ 2^{lg n}`. -/
theorem le_two_pow_lg (n : ℕ) : n ≤ 2 ^ lg n :=
  (Nat.le_pow_clog (by norm_num) n).trans
    (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

end PrecisionBasic

open PrecisionBasic

/-! ## The numerical constant -/

/-- `√2/8 + 2^{-12} + 2^{-23} < 0.177021` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:bridge-total`)). -/
theorem bridge_constant_lt : Bridge_constant_ltStmt := by
  unfold Bridge_constant_ltStmt
  have hs : Real.sqrt 2 < 1.4142136 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h12 : (2 : ℝ) ^ (-12 : ℤ) = 1 / 4096 := by norm_num
  have h23 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 8388608 := by norm_num
  rw [h12, h23]
  linarith

/-! ## The final rounding -/

/-- One nearest rounding to the `(p+2)`-grid per output (any nearest rounding `rr`):
`‖F̂ - S·Ẑ‖_∞ ≤ (√2/8) 2^{-p}`. -/
theorem bridge_round_error : Bridge_round_errorStmt := by
  intro rr hrr d p P t T run x
  have hb : (0 : ℝ) ≤ Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ)) := by positivity
  refine (pi_norm_le_iff_of_nonneg hb).2 fun f => ?_
  have h := norm_crnd_sub_le hrr (p + 2) (bridgePreR rr P t T run x f)
  have hg : Real.sqrt 2 / 2 * gridUnit (p + 2) = Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [two_zpow_neg_natCast]
    unfold gridUnit
    rw [pow_add, mul_inv]
    ring
  show ‖crnd rr (p + 2) (bridgePreR rr P t T run x f) - bridgePreR rr P t T run x f‖ ≤ _
  exact h.trans_eq hg

/-! ## The master margin -/

/-- Eq. (`eq:master-margin`) (Theorem 4.7 (`thm:bridge-precision`)): for `p ≥ max(8,k)` and `1 ≤ d ≤ k`,
`2^{14} d (P+1) R³ v ≤ 2^{-p-12}` with `P = schedP p k`, `R = 2^k`, `v = 2^{-(P+2)}`. -/
theorem master_margin : Master_marginStmt := by
  intro p k d _hp _hd1 hdk
  -- `L = ⌈log₂(p+k+2)⌉ = Nat.clog 2 (p+k+2)`: `p + k + 2 ≤ 2^L` and `L < 2^L`.
  have hclog : p + k + 2 ≤ 2 ^ Nat.clog 2 (p + k + 2) := Nat.le_pow_clog (by norm_num) _
  have hLlt : Nat.clog 2 (p + k + 2) < 2 ^ Nat.clog 2 (p + k + 2) := Nat.lt_two_pow_self
  have hPdef : schedP p k = 2 * p + 12 * k + 32 * Nat.clog 2 (p + k + 2) + 256 := by
    unfold schedP; rfl
  -- `P + 1 ≤ 2^{L+9}`.
  have hP1 : schedP p k + 1 ≤ 2 ^ (Nat.clog 2 (p + k + 2) + 9) := by
    have h512 : 2 ^ (Nat.clog 2 (p + k + 2) + 9) = 512 * 2 ^ Nat.clog 2 (p + k + 2) := by
      rw [pow_add]; ring
    rw [h512, hPdef]
    generalize 2 ^ Nat.clog 2 (p + k + 2) = M at hclog hLlt ⊢
    generalize Nat.clog 2 (p + k + 2) = L at hclog hLlt ⊢
    omega
  have hdpow : d ≤ 2 ^ k := hdk.trans Nat.lt_two_pow_self.le
  -- The inequality in `ℕ`.
  have hnat : 2 ^ 14 * d * (schedP p k + 1) * (2 ^ k) ^ 3 * 2 ^ (p + 12) ≤ 2 ^ (schedP p k + 2) := by
    calc 2 ^ 14 * d * (schedP p k + 1) * (2 ^ k) ^ 3 * 2 ^ (p + 12)
        ≤ 2 ^ 14 * 2 ^ k * 2 ^ (Nat.clog 2 (p + k + 2) + 9) * (2 ^ k) ^ 3 * 2 ^ (p + 12) := by
          gcongr
      _ = 2 ^ (4 * k + Nat.clog 2 (p + k + 2) + p + 35) := by ring
      _ ≤ 2 ^ (schedP p k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hreal : (2 : ℝ) ^ 14 * (d : ℝ) * ((schedP p k : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 3 *
      (2 : ℝ) ^ (p + 12) ≤ (2 : ℝ) ^ (schedP p k + 2) := by
    exact_mod_cast hnat
  rw [show (-((p : ℤ) + 12)) = -(((p + 12 : ℕ)) : ℤ) by push_cast; ring, two_zpow_neg_natCast]
  unfold gridUnit
  rw [mul_inv_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact hreal

/-! ## Assembly -/

/-- Theorem 4.7 from its three error parts (`thm:bridge-precision`, eq. (`eq:bridge-total`)): the output
lies on the `(p+2)`-grid, and the triangle inequality through `bridgePreR rr` and
`bridgeExactScaled`, with `X ≥ 1` for the rounding term, gives the bound. The hypothesis
`_hconst` is not used (the bound of `Bridge_precisionStmt` is the explicit sum). -/
theorem bridge_precision_of (harith : Bridge_arith_errorStmt) (halias : Bridge_alias_errorStmt)
    (hround : Bridge_round_errorStmt) (_hconst : Bridge_constant_ltStmt) :
    Bridge_precisionStmt := by
  intro rr hrr d t k ℓ p hshape hp x hx hxn T hT Emid δmid run hmid
  refine ⟨fun f => crnd_onGrid hrr (p + 2) _, ?_⟩
  have h1 := hround rr hrr p (schedP p k) t T run x
  have h2 := harith rr hrr t k ℓ p hshape hp x hx hxn T hT Emid δmid run hmid
  have h3 := halias t k ℓ p hshape hp x hx hxn
  set X := max 1 ‖x‖ with hX
  have hX1 : (1 : ℝ) ≤ X := le_max_left _ _
  set F := bridgeFixedR rr p (schedP p k) t T run x with hF
  set B := bridgePreR rr (schedP p k) t T run x with hB
  set E := bridgeExactScaled (alphaDefault (schedOmega p k d)) t x with hE
  set G := dft (totalLen t) x with hG
  have htri : ‖F - G‖ ≤ ‖F - B‖ + ‖B - E‖ + ‖E - G‖ := by
    calc ‖F - G‖ = ‖(F - B) + (B - E) + (E - G)‖ := by congr 1; abel
      _ ≤ ‖(F - B) + (B - E)‖ + ‖E - G‖ := norm_add_le _ _
      _ ≤ ‖F - B‖ + ‖B - E‖ + ‖E - G‖ := by gcongr; exact norm_add_le _ _
  have e12 : (2 : ℝ) ^ (-((p : ℤ) + 12)) = (2 : ℝ) ^ (-12 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  have e23 : (2 : ℝ) ^ (-((p : ℤ) + 23)) = (2 : ℝ) ^ (-23 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [e12] at h2
  rw [e23] at h3
  have hs : 0 ≤ Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ)) := by positivity
  have h1' : ‖F - B‖ ≤ Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ)) * X := by
    calc ‖F - B‖ ≤ Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ)) := h1
      _ = Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ)) * 1 := (mul_one _).symm
      _ ≤ Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ)) * X := mul_le_mul_of_nonneg_left hX1 hs
  calc ‖F - G‖ ≤ ‖F - B‖ + ‖B - E‖ + ‖E - G‖ := htri
    _ < Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ)) * X +
          (2 : ℝ) ^ (-12 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) * X +
          (2 : ℝ) ^ (-23 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) * X :=
        add_lt_add_of_le_of_lt (add_le_add h1' h2) h3
    _ = (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) *
          X := by ring

/-- Theorem 4.7 from the arithmetic and alias parts only (the rounding part and the numerical
constant are proved above). -/
theorem bridge_precision_of_arith_alias (harith : Bridge_arith_errorStmt)
    (halias : Bridge_alias_errorStmt) : Bridge_precisionStmt :=
  bridge_precision_of harith halias bridge_round_error bridge_constant_lt

/-! ## The alias error -/

namespace PrecisionBasic

/-- `α = alphaDefault ω = 2√(ω ln2/π)` is admissible (lower end of eq. (`eq:alpha`)). -/
theorem alphaDefault_admissible (ω : ℕ) : AlphaAdmissible ω (alphaDefault ω) := by
  have h0 : 0 ≤ Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) := Real.sqrt_nonneg _
  unfold AlphaAdmissible alphaDefault IntMul.alphaSchedule
  constructor <;> linarith

/-- The balanced shape satisfies the standing shape assumption of §4: every `t_i ≥ 2` is a power
of two (`t_i ∈ {2^ℓ, 2^{ℓ-1}}`, `ℓ ≥ 2`). -/
theorem shapeOK_of_balancedShape {d : ℕ} {t : Fin d → ℕ} {k ℓ : ℕ} (h : BalancedShape t k ℓ) :
    ShapeOK t := by
  obtain ⟨-, -, hℓ, -, hti⟩ := h
  intro i
  rcases hti i with h1 | h2
  · refine ⟨?_, ℓ, h1⟩
    rw [h1]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h3 : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h4 : t i = 2 ^ (ℓ - 1) := by omega
    refine ⟨?_, ℓ - 1, h4⟩
    rw [h4]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (ℓ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The scalar alias coefficient: for `ω = schedOmega p k d = p + k + lg d + 20`, `R = 2^k` and
`t_1 ≥ 1`, `0.120 (d-1) (R/t_1) 2^{-ω} ≤ 0.120 · 2^{-p-20}` (uses `d - 1 ≤ 2^{lg d}`,
`R/t_1 ≤ 2^k`). -/
theorem alias_coeff_le {d : ℕ} (t : Fin d → ℕ) (k p : ℕ) (hR : totalLen t = 2 ^ k)
    (hd1 : 1 ≤ d) (ht0 : 1 ≤ t ⟨0, hd1⟩) :
    0.120 * ((d : ℝ) - 1) * ((totalLen t : ℝ) / (t ⟨0, hd1⟩ : ℝ)) *
        (2 : ℝ) ^ (-((schedOmega p k d : ℕ) : ℤ)) ≤ 0.120 * ((2 : ℝ) ^ p * 2 ^ 20)⁻¹ := by
  have hd : (d : ℝ) - 1 ≤ (2 : ℝ) ^ lg d := by
    have : (d : ℝ) ≤ (2 : ℝ) ^ lg d := by exact_mod_cast le_two_pow_lg d
    linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    linarith
  have ht0' : (1 : ℝ) ≤ (t ⟨0, hd1⟩ : ℝ) := by exact_mod_cast ht0
  have hRr : (totalLen t : ℝ) = (2 : ℝ) ^ k := by rw [hR]; push_cast; ring
  have hD : (totalLen t : ℝ) / (t ⟨0, hd1⟩ : ℝ) ≤ (2 : ℝ) ^ k := by
    rw [hRr]; exact div_le_self (by positivity) ht0'
  have hD0 : (0 : ℝ) ≤ (totalLen t : ℝ) / (t ⟨0, hd1⟩ : ℝ) := by positivity
  have hω : (2 : ℝ) ^ (-((schedOmega p k d : ℕ) : ℤ)) =
      ((2 : ℝ) ^ p * (2 : ℝ) ^ k * (2 : ℝ) ^ lg d * 2 ^ 20)⁻¹ := by
    rw [two_zpow_neg_natCast]; unfold schedOmega; rw [pow_add, pow_add, pow_add]
  have hW0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((schedOmega p k d : ℕ) : ℤ)) := by positivity
  calc 0.120 * ((d : ℝ) - 1) * ((totalLen t : ℝ) / (t ⟨0, hd1⟩ : ℝ)) *
        (2 : ℝ) ^ (-((schedOmega p k d : ℕ) : ℤ))
      ≤ 0.120 * (2 : ℝ) ^ lg d * (2 : ℝ) ^ k * (2 : ℝ) ^ (-((schedOmega p k d : ℕ) : ℤ)) := by
        apply mul_le_mul_of_nonneg_right _ hW0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hD hD0 (by positivity)
    _ = 0.120 * ((2 : ℝ) ^ p * 2 ^ 20)⁻¹ := by
        rw [hω]; field_simp

end PrecisionBasic

/-- The alias part of Theorem 4.7 (`thm:bridge-precision`), from Lemma 4.4 (bridge Lemma B)(vi)
(eq. (`eq:lemma-B-total`)) applied to `x' = x/S` and rescaled by `S = 2^{preScaleExp t x}`:
`‖S(B_2⋯B_d)^{-1}F_t U' - F_R x‖_∞ ≤ 0.120 (d-1) D 2^{-ω} ‖x‖_∞ ≤ 0.120·2^{-p-20} X < 2^{-p-23} X`. -/
theorem bridge_alias_error_of (hvi : LemmaB_viStmt) : Bridge_alias_errorStmt := by
  intro d t k ℓ p hshape _hp x _hx _hxn
  have hsh : ShapeOK t := shapeOK_of_balancedShape hshape
  obtain ⟨hd2, hR, -, -, -⟩ := hshape
  have hd1 : 1 ≤ d := by omega
  have hω8 : 8 ≤ schedOmega p k d := by unfold schedOmega; omega
  obtain ⟨-, -, hmain⟩ := hvi (schedOmega p k d) hω8 (alphaDefault (schedOmega p k d))
    (alphaDefault_admissible _) t hsh hd1 (preScaled t x)
  have ht0 : 1 ≤ t ⟨0, hd1⟩ := le_trans (by norm_num) (hsh ⟨0, hd1⟩).1
  have hcoef := alias_coeff_le t k p hR hd1 ht0
  -- Rescaling by `S = 2^s`: `x = S • x'`, `F_R x = S • F_R x'`.
  have hc0 : (2 : ℂ) ^ preScaleExp t x ≠ 0 := pow_ne_zero _ two_ne_zero
  have hxc : x = (2 : ℂ) ^ preScaleExp t x • preScaled t x := by
    funext j
    show x j = (2 : ℂ) ^ preScaleExp t x * (x j / (2 : ℂ) ^ preScaleExp t x)
    rw [mul_div_cancel₀ _ hc0]
  have hdft : dft (totalLen t) x =
      (2 : ℂ) ^ preScaleExp t x • dft (totalLen t) (preScaled t x) := by
    rw [← map_smul, ← hxc]
  have hE : bridgeExactScaled (alphaDefault (schedOmega p k d)) t x =
      (2 : ℂ) ^ preScaleExp t x • Matrix.mulVec (truncProd (alphaDefault (schedOmega p k d)) t)⁻¹
        (fun f => dftTensor t (spreadAll (alphaDefault (schedOmega p k d)) t
          (preScaled t x ∘ encIn t)) ((encFreq t).symm f)) := by
    funext f; rfl
  have hxn : ‖x‖ = ‖(2 : ℂ) ^ preScaleExp t x‖ * ‖preScaled t x‖ := by
    have h := congrArg (fun y : Fin (totalLen t) → ℂ => ‖y‖) hxc
    rw [norm_smul] at h
    exact h
  rw [hE, hdft, ← smul_sub, norm_smul]
  set K := 0.120 * ((d : ℝ) - 1) * ((totalLen t : ℝ) / (t ⟨0, hd1⟩ : ℝ)) *
      (2 : ℝ) ^ (-((schedOmega p k d : ℕ) : ℤ)) with hK
  have hc_nn : 0 ≤ ‖(2 : ℂ) ^ preScaleExp t x‖ := norm_nonneg _
  have step1 := mul_le_mul_of_nonneg_left hmain hc_nn
  have step2 : ‖(2 : ℂ) ^ preScaleExp t x‖ * (K * ‖preScaled t x‖) = K * ‖x‖ := by
    rw [hxn]; ring
  rw [step2] at step1
  -- Numerics: `K ≤ 0.120·2^{-p-20} = 0.96·2^{-p-23}`.
  have h23 : (2 : ℝ) ^ (-((p : ℤ) + 23)) = ((2 : ℝ) ^ p * 2 ^ 23)⁻¹ := by
    rw [show (-((p : ℤ) + 23)) = -(((p + 23 : ℕ)) : ℤ) by push_cast; ring,
      two_zpow_neg_natCast, pow_add]
  have h20 : ((2 : ℝ) ^ p * 2 ^ 20)⁻¹ = 8 * ((2 : ℝ) ^ p * 2 ^ 23)⁻¹ := by
    field_simp; norm_num
  rw [h23]
  rw [h20] at hcoef
  have hv0 : 0 < ((2 : ℝ) ^ p * 2 ^ 23)⁻¹ := by positivity
  have hxX : ‖x‖ ≤ max 1 ‖x‖ := le_max_right _ _
  have hX1 : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
  have a1 : K * ‖x‖ ≤ 0.120 * (8 * ((2 : ℝ) ^ p * 2 ^ 23)⁻¹) * ‖x‖ :=
    mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have a2 : ((2 : ℝ) ^ p * 2 ^ 23)⁻¹ * ‖x‖ ≤ ((2 : ℝ) ^ p * 2 ^ 23)⁻¹ * max 1 ‖x‖ :=
    mul_le_mul_of_nonneg_left hxX hv0.le
  have a3 : 0 < ((2 : ℝ) ^ p * 2 ^ 23)⁻¹ * max 1 ‖x‖ := mul_pos hv0 (by linarith)
  have a4 : 0.120 * (8 * ((2 : ℝ) ^ p * 2 ^ 23)⁻¹) * ‖x‖ =
      0.96 * (((2 : ℝ) ^ p * 2 ^ 23)⁻¹ * ‖x‖) := by ring
  linarith

end SubNLogN.Math.Bridge
