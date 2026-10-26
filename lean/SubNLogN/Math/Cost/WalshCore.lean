import Mathlib
import SubNLogN.Math.Cost.Family
import SubNLogN.Math.Cost.AsymK
import SubNLogN.Math.Cost.Absorb
import SubNLogN.Math.Cost.Abstract
import SubNLogN.Math.Cost.Row46

/-!
# Cost: family-generic core of the Walsh-route cost theorem

Paper: Section 7 (`sec:main`): Table 5 (`tab:cost-walsh`), eq. (`eq:root-cost`),
eq. (`eq:cost-W`), eq. (`eq:setup`), and the cost part of the proof of Theorem 1 (`thm:main`)
in Section 7.6 (`sec:main-thm`).

This file works with the `(b, k)`-level parameters of `Family.lean`, so that the cost theorem holds
for any root-parameter family `n ↦ (b n, k n)` satisfying `FamFacts` (the paper family of
`Params.lean` and the W8 family of the machine are both instances).

* `RowExps.Admissible.*`: numeric consequences of admissibility (`0 < ε < 1/14`, `0 < c ≤ 1`, ...).
* Pointwise forms of the five normalized costs of Table 5, from the bands `BandsK ρ P' k` (and
  `2 ≤ d`, `2 ≤ P'`): `dK ≤ P'^{ε(1+c)}`, `ℓd^λ ≤ P'^{1-ε(1-λ)}`,
  `ℓ m(P') ≤ |A_m| P'^{1-ε} (lg 2P')^{j_m}`, `d(1 + ℓ^τ) ≤ 2P'^{1-(1-ε)(1-τ)}`,
  `d(m(P') + m(P'²)) ≤ |A_m|(1 + 2^{j_m}) P'^ε (lg 2P')^{j_m}`.
* `walshCostBK`: the Walsh-route cost expression at `(b, k)` (the same expression as
  `Walsh46.walshCost`, which is `walshCostBK` at `(bOf n, kOf n)`).

This file proves no machine bound: the cost function `T` in the cost theorems is arbitrary and the
bound `T n ≤ A · walshCostBK …` is a hypothesis.
-/

namespace SubNLogN.Math.Cost

open Filter
open SubNLogN.S5 (HeadlineCost)

/-! ## Numeric consequences of admissibility -/

namespace RowExps.Admissible

variable {ρ : RowExps}

/-- Admissibility gives `0 < e₂`. -/
theorem e₂_pos (hρ : ρ.Admissible) : 0 < ρ.e₂ := by
  obtain ⟨h1, h2, -, -⟩ := hρ
  omega

/-- Admissibility gives `0 < c₂`. -/
theorem c₂_pos (hρ : ρ.Admissible) : 0 < ρ.c₂ := by
  obtain ⟨-, -, h3, h4⟩ := hρ
  omega

/-- Admissibility gives `0 < ε`. -/
theorem eps_pos (hρ : ρ.Admissible) : 0 < ρ.eps :=
  div_pos (by exact_mod_cast hρ.1) (by exact_mod_cast hρ.e₂_pos)

/-- Admissibility gives `ε < 1/14`. -/
theorem eps_lt (hρ : ρ.Admissible) : ρ.eps < 1 / 14 := by
  unfold RowExps.eps
  rw [div_lt_div_iff₀ (by exact_mod_cast hρ.e₂_pos) (by norm_num)]
  have h : ((14 * ρ.e₁ : ℕ) : ℝ) < ρ.e₂ := by exact_mod_cast hρ.2.1
  push_cast at h
  linarith

/-- Admissibility gives `0 < c`. -/
theorem c_pos (hρ : ρ.Admissible) : 0 < ρ.c :=
  div_pos (by exact_mod_cast hρ.2.2.1) (by exact_mod_cast hρ.c₂_pos)

/-- Admissibility gives `c ≤ 1`. -/
theorem c_le_one (hρ : ρ.Admissible) : ρ.c ≤ 1 := by
  unfold RowExps.c
  rw [div_le_one (by exact_mod_cast hρ.c₂_pos)]
  exact_mod_cast hρ.2.2.2

end RowExps.Admissible

variable {ρ : RowExps}

/-! ## The normalized costs of Table 5, pointwise from the bands -/

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 1, prefix butterfly rounds `dK`, gap `g_pre = 1 - ε(1+c)`):
if the bands `BandsK ρ P' k` hold, then `dK ≤ P'^{ε(1+c)}`. -/
theorem prefix_le_of_bandsK (hρ : ρ.Admissible) {P' k : ℕ} (hB : BandsK ρ P' k) :
    (dK ρ k : ℝ) * KK ρ k ≤ (P' : ℝ) ^ (ρ.eps * (1 + ρ.c)) := by
  obtain ⟨-, hdP, -, -, -, -⟩ := hB
  have hc0 := hρ.c_pos
  have hd0 : (0 : ℝ) ≤ dK ρ k := Nat.cast_nonneg _
  have hK : (KK ρ k : ℝ) ≤ (dK ρ k : ℝ) ^ ρ.c := by
    rw [KK, floorRatPow_eq_floor_rpow hρ.c₂_pos]
    exact Nat.floor_le (Real.rpow_nonneg hd0 _)
  calc (dK ρ k : ℝ) * KK ρ k ≤ (dK ρ k : ℝ) * (dK ρ k : ℝ) ^ ρ.c :=
        mul_le_mul_of_nonneg_left hK hd0
    _ = (dK ρ k : ℝ) ^ (1 + ρ.c) := by
        rw [Real.rpow_add' hd0 (by linarith), Real.rpow_one]
    _ ≤ ((P' : ℝ) ^ ρ.eps) ^ (1 + ρ.c) := Real.rpow_le_rpow hd0 hdP (by linarith)
    _ = (P' : ℝ) ^ (ρ.eps * (1 + ρ.c)) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg _)]

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 2, butterfly layers and both positional maps `ℓd^{λ'}`, gap
`g_lay = ε(1-λ')`): if `BandsK ρ P' k`, `2 ≤ d`, `2 ≤ P'` and `0 ≤ λ ≤ 1`, then
`ℓ d^λ ≤ P'^{1-ε(1-λ)}`. -/
theorem layer_le_of_bandsK (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {P' k : ℕ}
    (hB : BandsK ρ P' k) (hd2 : 2 ≤ dK ρ k) (hP2 : 2 ≤ P') :
    (lK ρ k : ℝ) * (dK ρ k : ℝ) ^ lam ≤ (P' : ℝ) ^ (1 - ρ.eps * (1 - lam)) := by
  obtain ⟨hdlo, -, -, hlP, -, -⟩ := hB
  have hP2' : (2 : ℝ) ≤ P' := by exact_mod_cast hP2
  have hP0 : (0 : ℝ) < P' := by linarith
  have hd2' : (2 : ℝ) ≤ dK ρ k := by exact_mod_cast hd2
  have hd : (0 : ℝ) < dK ρ k := by linarith
  have hPe : (0 : ℝ) < (P' : ℝ) ^ ρ.eps := Real.rpow_pos_of_pos hP0 _
  have hld : (lK ρ k : ℝ) * dK ρ k ≤ (P' : ℝ) / 8 := by
    have h := hlP
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hq : 0 < (1 / 4 : ℝ) * (P' : ℝ) ^ ρ.eps := by positivity
  have h4 : (1 / 4 : ℝ) ^ (lam - 1) ≤ 4 := by
    calc (1 / 4 : ℝ) ^ (lam - 1) ≤ (1 / 4 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 4 := by rw [Real.rpow_neg_one]; norm_num
  have hdpow : (dK ρ k : ℝ) ^ (lam - 1) ≤ 4 * (P' : ℝ) ^ (-(ρ.eps * (1 - lam))) := by
    calc (dK ρ k : ℝ) ^ (lam - 1) ≤ ((1 / 4 : ℝ) * (P' : ℝ) ^ ρ.eps) ^ (lam - 1) :=
          Real.rpow_le_rpow_of_nonpos hq hdlo (by linarith)
      _ = (1 / 4 : ℝ) ^ (lam - 1) * (P' : ℝ) ^ (-(ρ.eps * (1 - lam))) := by
          rw [Real.mul_rpow (by norm_num) hPe.le, ← Real.rpow_mul hP0.le]
          congr 2
          ring
      _ ≤ 4 * (P' : ℝ) ^ (-(ρ.eps * (1 - lam))) :=
          mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hP0.le _)
  have hsplit : (dK ρ k : ℝ) ^ lam = (dK ρ k : ℝ) * (dK ρ k : ℝ) ^ (lam - 1) := by
    conv_lhs => rw [show lam = 1 + (lam - 1) by ring]
    rw [Real.rpow_add hd, Real.rpow_one]
  calc (lK ρ k : ℝ) * (dK ρ k : ℝ) ^ lam
      = ((lK ρ k : ℝ) * dK ρ k) * (dK ρ k : ℝ) ^ (lam - 1) := by rw [hsplit]; ring
    _ ≤ ((P' : ℝ) / 8) * (4 * (P' : ℝ) ^ (-(ρ.eps * (1 - lam)))) :=
        mul_le_mul hld hdpow (Real.rpow_nonneg hd.le _) (by positivity)
    _ = (1 / 2) * ((P' : ℝ) * (P' : ℝ) ^ (-(ρ.eps * (1 - lam)))) := by ring
    _ = (1 / 2) * (P' : ℝ) ^ (1 - ρ.eps * (1 - lam)) := by
        rw [show (1 : ℝ) - ρ.eps * (1 - lam) = 1 + (-(ρ.eps * (1 - lam))) by ring,
          Real.rpow_add hP0, Real.rpow_one]
    _ ≤ (P' : ℝ) ^ (1 - ρ.eps * (1 - lam)) := by
        have := Real.rpow_nonneg hP0.le (1 - ρ.eps * (1 - lam))
        linarith

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 3, complex twiddles and last-axis FFT `ℓ m(P)`, gap
`g_last = ε` up to logarithms): if `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`, `BandsK ρ P' k`,
`2 ≤ d` and `2 ≤ P'`, then `ℓ m(P') ≤ |A_m| P'^{1-ε} (lg 2P')^{j_m}`. -/
theorem last_le_of_bandsK (m : ℕ → ℝ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm) {P' k : ℕ}
    (hB : BandsK ρ P' k) (hd2 : 2 ≤ dK ρ k) (hP2 : 2 ≤ P') :
    (lK ρ k : ℝ) * m P' ≤ |Am| * (P' : ℝ) ^ (1 - ρ.eps) * Real.logb 2 (2 * P') ^ jm := by
  obtain ⟨hdlo, -, -, hlP, -, -⟩ := hB
  have hP2' : (2 : ℝ) ≤ P' := by exact_mod_cast hP2
  have hP0 : (0 : ℝ) < P' := by linarith
  have hd2' : (2 : ℝ) ≤ dK ρ k := by exact_mod_cast hd2
  have hd : (0 : ℝ) < dK ρ k := by linarith
  have hl0 : (0 : ℝ) ≤ lK ρ k := Nat.cast_nonneg _
  have hL0 : 0 ≤ Real.logb 2 (2 * (P' : ℝ)) := Real.logb_nonneg (by norm_num) (by linarith)
  have hPe : 0 < (P' : ℝ) ^ ρ.eps := Real.rpow_pos_of_pos hP0 _
  have hl : (lK ρ k : ℝ) ≤ (P' : ℝ) ^ (1 - ρ.eps) := by
    calc (lK ρ k : ℝ) ≤ (P' : ℝ) / (8 * dK ρ k) := hlP
      _ ≤ (P' : ℝ) / (8 * ((1 / 4) * (P' : ℝ) ^ ρ.eps)) :=
          div_le_div_of_nonneg_left hP0.le (by positivity) (by linarith)
      _ = (1 / 2) * ((P' : ℝ) / (P' : ℝ) ^ ρ.eps) := by
          field_simp
          ring
      _ = (1 / 2) * (P' : ℝ) ^ (1 - ρ.eps) := by rw [Real.rpow_sub hP0, Real.rpow_one]
      _ ≤ (P' : ℝ) ^ (1 - ρ.eps) := by
          have := Real.rpow_nonneg hP0.le (1 - ρ.eps)
          linarith
  have hmP := hm P' hP2
  calc (lK ρ k : ℝ) * m P' ≤ (lK ρ k : ℝ) * (|Am| * Real.logb 2 (2 * P') ^ jm) := by
        apply mul_le_mul_of_nonneg_left _ hl0
        exact le_trans hmP (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hL0 _))
    _ ≤ (P' : ℝ) ^ (1 - ρ.eps) * (|Am| * Real.logb 2 (2 * P') ^ jm) :=
        mul_le_mul_of_nonneg_right hl (by positivity)
    _ = |Am| * (P' : ℝ) ^ (1 - ρ.eps) * Real.logb 2 (2 * P') ^ jm := by ring

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 4, axis exposures and restorations `d(1 + ℓ^τ)`, gap
`g_axis = (1-ε)(1-τ)`): if `BandsK ρ P' k`, `2 ≤ d`, `2 ≤ P'` and `0 ≤ τ ≤ 1`, then
`d(1 + ℓ^τ) ≤ 2 P'^{1-(1-ε)(1-τ)}`. -/
theorem axis_le_of_bandsK (hρ : ρ.Admissible) (tau : ℝ) (h0 : 0 ≤ tau) (h1 : tau ≤ 1)
    {P' k : ℕ} (hB : BandsK ρ P' k) (hd2 : 2 ≤ dK ρ k) (hP2 : 2 ≤ P') :
    (dK ρ k : ℝ) * (1 + (lK ρ k : ℝ) ^ tau) ≤ 2 * (P' : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) := by
  have heps0 := hρ.eps_pos
  have heps1 := hρ.eps_lt
  obtain ⟨-, hdP, -, hlP, -, -⟩ := hB
  have hP2' : (2 : ℝ) ≤ P' := by exact_mod_cast hP2
  have hP1 : (1 : ℝ) ≤ P' := by linarith
  have hP0 : (0 : ℝ) < P' := by linarith
  have hd2' : (2 : ℝ) ≤ dK ρ k := by exact_mod_cast hd2
  have hd : (0 : ℝ) < dK ρ k := by linarith
  have hl0 : (0 : ℝ) ≤ lK ρ k := Nat.cast_nonneg _
  have hld : (dK ρ k : ℝ) * lK ρ k ≤ P' := by
    have h := hlP
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hd_le : (dK ρ k : ℝ) ≤ (P' : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) := by
    calc (dK ρ k : ℝ) ≤ (P' : ℝ) ^ ρ.eps := hdP
      _ ≤ (P' : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) :=
          Real.rpow_le_rpow_of_exponent_le hP1 (by nlinarith)
  have hsplit : (dK ρ k : ℝ) * (lK ρ k : ℝ) ^ tau =
      (dK ρ k : ℝ) ^ (1 - tau) * ((dK ρ k : ℝ) * lK ρ k) ^ tau := by
    rw [Real.mul_rpow hd.le hl0, ← mul_assoc, ← Real.rpow_add hd,
      show 1 - tau + tau = 1 by ring, Real.rpow_one]
  have hdl : (dK ρ k : ℝ) * (lK ρ k : ℝ) ^ tau ≤ (P' : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) := by
    rw [hsplit]
    calc (dK ρ k : ℝ) ^ (1 - tau) * ((dK ρ k : ℝ) * lK ρ k) ^ tau
        ≤ ((P' : ℝ) ^ ρ.eps) ^ (1 - tau) * (P' : ℝ) ^ tau := by
          apply mul_le_mul (Real.rpow_le_rpow hd.le hdP (by linarith))
            (Real.rpow_le_rpow (by positivity) hld h0) (by positivity) (by positivity)
      _ = (P' : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) := by
          rw [← Real.rpow_mul hP0.le, ← Real.rpow_add hP0]
          congr 1
          ring
  calc (dK ρ k : ℝ) * (1 + (lK ρ k : ℝ) ^ tau)
      = (dK ρ k : ℝ) + (dK ρ k : ℝ) * (lK ρ k : ℝ) ^ tau := by ring
    _ ≤ (P' : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) + (P' : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) :=
        add_le_add hd_le hdl
    _ = 2 * (P' : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) := by ring

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 5, spreading and cyclic solves `d(m(P) + m(P²))`, gap
`g_short = 1 - ε` up to logarithms): if `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`,
`BandsK ρ P' k` and `2 ≤ P'`, then `d(m(P') + m(P'²)) ≤ |A_m|(1 + 2^{j_m}) P'^ε (lg 2P')^{j_m}`. -/
theorem short_le_of_bandsK (m : ℕ → ℝ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm) {P' k : ℕ}
    (hB : BandsK ρ P' k) (hP2 : 2 ≤ P') :
    (dK ρ k : ℝ) * (m P' + m (P' ^ 2)) ≤
      |Am| * (1 + 2 ^ jm) * (P' : ℝ) ^ ρ.eps * Real.logb 2 (2 * P') ^ jm := by
  obtain ⟨-, hdP, -, -, -, -⟩ := hB
  have hP2' : (2 : ℝ) ≤ P' := by exact_mod_cast hP2
  have hP1 : (1 : ℝ) ≤ P' := by linarith
  have hd0 : (0 : ℝ) ≤ dK ρ k := Nat.cast_nonneg _
  have hL0 : 0 ≤ Real.logb 2 (2 * (P' : ℝ)) := Real.logb_nonneg (by norm_num) (by linarith)
  have hm1 : m P' ≤ |Am| * Real.logb 2 (2 * (P' : ℝ)) ^ jm :=
    le_trans (hm P' hP2) (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hL0 _))
  have hsq2 : 2 ≤ P' ^ 2 := le_trans hP2 (Nat.le_self_pow two_ne_zero _)
  have hm2 : m (P' ^ 2) ≤ |Am| * (2 ^ jm * Real.logb 2 (2 * (P' : ℝ)) ^ jm) := by
    have h := hm (P' ^ 2) hsq2
    have hsq : Real.logb 2 (2 * ((P' ^ 2 : ℕ) : ℝ)) ≤ 2 * Real.logb 2 (2 * (P' : ℝ)) := by
      push_cast
      exact logb_two_mul_sq_le hP1
    have hsq0 : 0 ≤ Real.logb 2 (2 * ((P' ^ 2 : ℕ) : ℝ)) := by
      apply Real.logb_nonneg (by norm_num)
      have : (2 : ℝ) ≤ ((P' ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsq2
      linarith
    calc m (P' ^ 2) ≤ Am * Real.logb 2 (2 * ((P' ^ 2 : ℕ) : ℝ)) ^ jm := h
      _ ≤ |Am| * Real.logb 2 (2 * ((P' ^ 2 : ℕ) : ℝ)) ^ jm :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hsq0 _)
      _ ≤ |Am| * (2 * Real.logb 2 (2 * (P' : ℝ))) ^ jm :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsq0 hsq _) (abs_nonneg _)
      _ = |Am| * (2 ^ jm * Real.logb 2 (2 * (P' : ℝ)) ^ jm) := by rw [mul_pow]
  calc (dK ρ k : ℝ) * (m P' + m (P' ^ 2))
      ≤ (dK ρ k : ℝ) * (|Am| * Real.logb 2 (2 * (P' : ℝ)) ^ jm +
          |Am| * (2 ^ jm * Real.logb 2 (2 * (P' : ℝ)) ^ jm)) :=
        mul_le_mul_of_nonneg_left (add_le_add hm1 hm2) hd0
    _ ≤ (P' : ℝ) ^ ρ.eps * (|Am| * Real.logb 2 (2 * (P' : ℝ)) ^ jm +
          |Am| * (2 ^ jm * Real.logb 2 (2 * (P' : ℝ)) ^ jm)) :=
        mul_le_mul_of_nonneg_right hdP (by positivity)
    _ = |Am| * (1 + 2 ^ jm) * (P' : ℝ) ^ ρ.eps * Real.logb 2 (2 * P') ^ jm := by ring

/-! ## The Walsh-route cost expression at `(b, k)` -/

/-- The Walsh-route cost expression at digit width `b`, transform exponent `k` and input length
`n` (Section 7.2, eq. (`eq:root-cost`) with `R·M(P) = RP·m(P)`, Section 7.3, eq. (`eq:cost-W`), Section 7.3
eq. (`eq:setup`)), with `R = 2^k`, `P = PBK b k`, `V = VBK b k = RP`, `d = dK ρ k`, `ℓ = lK ρ k`,
`r = rK ρ k`, `K = KK ρ k`:
`RP·[dK + ℓd^{λ'} + ℓ·m(P) + d(1 + ℓ^τ) + d(m(P) + m(P²))] + RP·m(P) + n
  + (R/r)P^{D_set} + r·P^{D_set} + P^{D_set}` (real powers `d^{λ'}`, `ℓ^τ`). -/
noncomputable def walshCostBK (ρ : RowExps) (lam' tau : ℝ) (m : ℕ → ℝ) (Dset b k n : ℕ) : ℝ :=
  (VBK b k : ℝ) * ((dK ρ k : ℝ) * KK ρ k + (lK ρ k : ℝ) * (dK ρ k : ℝ) ^ lam'
      + (lK ρ k : ℝ) * m (PBK b k) + (dK ρ k : ℝ) * (1 + (lK ρ k : ℝ) ^ tau)
      + (dK ρ k : ℝ) * (m (PBK b k) + m (PBK b k ^ 2)))
    + (VBK b k : ℝ) * m (PBK b k) + n
    + (((2 ^ k / rK ρ k : ℕ) : ℝ) * (PBK b k : ℝ) ^ Dset + (rK ρ k : ℝ) * (PBK b k : ℝ) ^ Dset
      + (PBK b k : ℝ) ^ Dset)


/-! ## The family-generic cost theorem -/

/-- CONTRACT (cost part of the proof of Theorem 1 (`thm:main`), Section 7.6 (`sec:main-thm`), for any root-parameter family with `FamFacts`
and any admissible row with the needed gaps). Let `n ↦ (b n, k n)` satisfy `FamFacts b k`, `ρ` be
admissible, `0 ≤ λ' ≤ 1`, `0 ≤ τ ≤ 1`, with `2^{-46} < ε(1-λ')`, `2^{-46} < (1-ε)(1-τ)` and
`2^{-46} < ε` (the gaps `g_pre`, `g_short` and the root-packing gap `1` exceed `2^{-46}`
automatically). Let `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`, `0 ≤ A`, and
`T n ≤ A · walshCostBK ρ λ' τ m D_set (b n) (k n) n` for all `n ≥ N₀`. Then
`HeadlineCost (monoEnv T) C N` for some natural `C, N`. -/
theorem headlineCost_walshBK (b k : ℕ → ℕ) (hF : FamFacts b k) (ρ : RowExps)
    (hρ : ρ.Admissible) (lam' tau : ℝ)
    (hlam'0 : 0 ≤ lam') (hlam'1 : lam' ≤ 1) (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    (hgLay : ((2 : ℝ) ^ 46)⁻¹ < ρ.eps * (1 - lam'))
    (hgAxis : ((2 : ℝ) ^ 46)⁻¹ < (1 - ρ.eps) * (1 - tau))
    (hgLast : ((2 : ℝ) ^ 46)⁻¹ < ρ.eps)
    (T : ℕ → ℕ) (m : ℕ → ℝ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm)
    (A : ℝ) (hA : 0 ≤ A) (Dset N₀ : ℕ)
    (hT : ∀ n ≥ N₀, (T n : ℝ) ≤ A * walshCostBK ρ lam' tau m Dset (b n) (k n) n) :
    ∃ C N : ℕ, HeadlineCost (monoEnv T) C N := by
  have heps0 := hρ.eps_pos
  have heps1 := hρ.eps_lt
  have hc0 := hρ.c_pos
  have hc1 := hρ.c_le_one
  obtain ⟨cV, hcV⟩ := hF.V_le
  obtain ⟨cP, hcP⟩ := hF.P_log
  have hev : ∀ᶠ n in atTop, (VBK (b n) (k n) : ℝ) ≤ cV * n ∧
      (PBK (b n) (k n) : ℝ) ≤ cP * (Nat.log2 n : ℝ) ∧ BandsK ρ (PBK (b n) (k n)) (k n) ∧
      2 ≤ dK ρ (k n) ∧
      1 * (2 ^ k n / rK ρ (k n) * PBK (b n) (k n) ^ Dset + rK ρ (k n) * PBK (b n) (k n) ^ Dset
        + PBK (b n) (k n) ^ Dset) ≤ 2 ^ k n * PBK (b n) (k n) := by
    filter_upwards [hcV, hcP, hF.P_band, hF.tendsto_k.eventually (eventually_bandsK hρ),
      hF.tendsto_k.eventually ((tendsto_dK hρ).eventually_ge_atTop 2),
      hF.tendsto_k.eventually (eventually_setupK hρ 1 Dset)] with n h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h4 _ h3.1 h3.2, h5, h6 _ h3.1 h3.2⟩
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
  have hk : ((2 : ℝ) ^ 46)⁻¹ < 1 / 1000 := by norm_num
  refine headlineCost_of_stageTerms T (fun n => (VBK (b n) (k n) : ℝ))
    (fun n => (PBK (b n) (k n) : ℝ))
    [⟨A, 1 - ρ.eps * (1 + ρ.c), 0⟩, ⟨A, ρ.eps * (1 - lam'), 0⟩, ⟨A * |Am|, ρ.eps, jm⟩,
      ⟨2 * A, (1 - ρ.eps) * (1 - tau), 0⟩, ⟨A * (|Am| * (1 + 2 ^ jm)), 1 - ρ.eps, jm⟩,
      ⟨A * |Am|, 1, jm⟩]
    cV cP (A * (1 + |cV|)) (max N₀ N₁) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    have hec : ρ.eps * (1 + ρ.c) ≤ 2 * ρ.eps := by nlinarith
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · show ((2 : ℝ) ^ 46)⁻¹ < 1 - ρ.eps * (1 + ρ.c)
      linarith
    · exact hgLay
    · exact hgLast
    · exact hgAxis
    · show ((2 : ℝ) ^ 46)⁻¹ < 1 - ρ.eps
      linarith
    · show ((2 : ℝ) ^ 46)⁻¹ < 1
      linarith
  · intro n hn
    exact ⟨Nat.cast_nonneg _, (hN₁ n (le_of_max_le_right hn)).1⟩
  · intro n hn
    refine ⟨?_, (hN₁ n (le_of_max_le_right hn)).2.1⟩
    have h := le_PBK (b n) (k n)
    show (2 : ℝ) ≤ (PBK (b n) (k n) : ℝ)
    exact_mod_cast (by omega : 2 ≤ PBK (b n) (k n))
  · intro n hn
    obtain ⟨hV, -, hB, hd2, b8⟩ := hN₁ n (le_of_max_le_right hn)
    have hTn := hT n (le_of_max_le_left hn)
    have hP2n : 2 ≤ PBK (b n) (k n) := le_trans (by norm_num) (le_PBK (b n) (k n))
    have hP2 : (2 : ℝ) ≤ PBK (b n) (k n) := by exact_mod_cast hP2n
    have hV0 : (0 : ℝ) ≤ VBK (b n) (k n) := Nat.cast_nonneg _
    have hL0 : 0 ≤ Real.logb 2 (2 * (PBK (b n) (k n) : ℝ)) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have b1 := prefix_le_of_bandsK hρ hB
    have b2 := layer_le_of_bandsK lam' hlam'0 hlam'1 hB hd2 hP2n
    have b3 := last_le_of_bandsK m Am jm hm hB hd2 hP2n
    have b4 := axis_le_of_bandsK hρ tau htau0 htau1 hB hd2 hP2n
    have b5 := short_le_of_bandsK m Am jm hm hB hP2n
    have b6 : m (PBK (b n) (k n)) ≤ |Am| * Real.logb 2 (2 * (PBK (b n) (k n) : ℝ)) ^ jm :=
      le_trans (hm _ hP2n) (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hL0 _))
    have b7 : ((2 ^ k n / rK ρ (k n) : ℕ) : ℝ) * (PBK (b n) (k n) : ℝ) ^ Dset
        + (rK ρ (k n) : ℝ) * (PBK (b n) (k n) : ℝ) ^ Dset + (PBK (b n) (k n) : ℝ) ^ Dset
        ≤ (VBK (b n) (k n) : ℝ) := by
      rw [one_mul] at b8
      have b8' : 2 ^ k n / rK ρ (k n) * PBK (b n) (k n) ^ Dset
          + rK ρ (k n) * PBK (b n) (k n) ^ Dset + PBK (b n) (k n) ^ Dset ≤ VBK (b n) (k n) := b8
      exact_mod_cast b8'
    have b9 : (VBK (b n) (k n) : ℝ) ≤ |cV| * n :=
      le_trans hV (mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _))
    have hX : walshCostBK ρ lam' tau m Dset (b n) (k n) n ≤
        (VBK (b n) (k n) : ℝ) * ((PBK (b n) (k n) : ℝ) ^ (ρ.eps * (1 + ρ.c))
          + (PBK (b n) (k n) : ℝ) ^ (1 - ρ.eps * (1 - lam'))
          + |Am| * (PBK (b n) (k n) : ℝ) ^ (1 - ρ.eps)
              * Real.logb 2 (2 * (PBK (b n) (k n) : ℝ)) ^ jm
          + 2 * (PBK (b n) (k n) : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau))
          + |Am| * (1 + 2 ^ jm) * (PBK (b n) (k n) : ℝ) ^ ρ.eps
              * Real.logb 2 (2 * (PBK (b n) (k n) : ℝ)) ^ jm)
        + (VBK (b n) (k n) : ℝ) * (|Am| * Real.logb 2 (2 * (PBK (b n) (k n) : ℝ)) ^ jm)
        + n + |cV| * n := by
      unfold walshCostBK
      have h1 := mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5) hV0
      have h2 := mul_le_mul_of_nonneg_left b6 hV0
      linarith
    show (T n : ℝ) ≤ stageSum _ (VBK (b n) (k n) : ℝ) (PBK (b n) (k n) : ℝ) + A * (1 + |cV|) * n
    calc (T n : ℝ) ≤ A * walshCostBK ρ lam' tau m Dset (b n) (k n) n := hTn
      _ ≤ A * ((VBK (b n) (k n) : ℝ) * ((PBK (b n) (k n) : ℝ) ^ (ρ.eps * (1 + ρ.c))
          + (PBK (b n) (k n) : ℝ) ^ (1 - ρ.eps * (1 - lam'))
          + |Am| * (PBK (b n) (k n) : ℝ) ^ (1 - ρ.eps)
              * Real.logb 2 (2 * (PBK (b n) (k n) : ℝ)) ^ jm
          + 2 * (PBK (b n) (k n) : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau))
          + |Am| * (1 + 2 ^ jm) * (PBK (b n) (k n) : ℝ) ^ ρ.eps
              * Real.logb 2 (2 * (PBK (b n) (k n) : ℝ)) ^ jm)
        + (VBK (b n) (k n) : ℝ) * (|Am| * Real.logb 2 (2 * (PBK (b n) (k n) : ℝ)) ^ jm)
        + n + |cV| * n) := mul_le_mul_of_nonneg_left hX hA
      _ = stageSum [⟨A, 1 - ρ.eps * (1 + ρ.c), 0⟩, ⟨A, ρ.eps * (1 - lam'), 0⟩,
            ⟨A * |Am|, ρ.eps, jm⟩, ⟨2 * A, (1 - ρ.eps) * (1 - tau), 0⟩,
            ⟨A * (|Am| * (1 + 2 ^ jm)), 1 - ρ.eps, jm⟩, ⟨A * |Am|, 1, jm⟩]
            (VBK (b n) (k n) : ℝ) (PBK (b n) (k n) : ℝ) + A * (1 + |cV|) * n := by
          simp only [stageSum_cons, stageSum_nil, StageTerm.eval, pow_zero, mul_one, add_zero]
          rw [show (1 : ℝ) - (1 - ρ.eps * (1 + ρ.c)) = ρ.eps * (1 + ρ.c) by ring,
            show (1 : ℝ) - (1 - ρ.eps) = ρ.eps by ring, show (1 : ℝ) - 1 = 0 by ring,
            Real.rpow_zero]
          ring

/-- CONTRACT (Theorem 1 (`thm:main`), cost conclusion at `κ = 2^{-46}`, Section 7.6 (`sec:main-thm`), proof of Theorem 1 (`thm:main`), for any
root-parameter family with `FamFacts`): for the `C₁ = 14` row (`ε = 1/15`, `c = 2^{-50}`,
`λ' = 1 - 31ξ/32`, `τ = 1 - 4ξ`, `ξ = 2^{-42}`), if `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`,
`0 ≤ A`, and `T n ≤ A · walshCostBK row46 λ' τ m D_set (b n) (k n) n` for all `n ≥ N₀`, then
`HeadlineCost (monoEnv T) C N` for some natural `C, N`. -/
theorem headlineCost_walsh46BK (b k : ℕ → ℕ) (hF : FamFacts b k) (T : ℕ → ℕ) (m : ℕ → ℝ)
    (Am : ℝ) (jm : ℕ) (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm)
    (A : ℝ) (hA : 0 ≤ A) (Dset N₀ : ℕ)
    (hT : ∀ n ≥ N₀, (T n : ℝ) ≤
      A * walshCostBK row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset (b n) (k n) n) :
    ∃ C N : ℕ, HeadlineCost (monoEnv T) C N := by
  refine headlineCost_walshBK b k hF row46 row46_admissible ((Row46.lam' : ℚ) : ℝ)
    ((Row46.tau : ℚ) : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ T m Am jm hm A hA Dset N₀ hT
  · norm_num [Row46.lam', Row46.xi]
  · norm_num [Row46.lam', Row46.xi]
  · norm_num [Row46.tau, Row46.xi]
  · norm_num [Row46.tau, Row46.xi]
  · rw [row46_eps]
    norm_num [Row46.lam', Row46.xi]
  · rw [row46_eps]
    norm_num [Row46.tau, Row46.xi]
  · rw [row46_eps]
    norm_num

end SubNLogN.Math.Cost
