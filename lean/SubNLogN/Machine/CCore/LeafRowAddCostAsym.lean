/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A polynomial is eventually below a stretched exponential (`CCore/LeafRowAddCostAsym.lean`)

`poly_le_two_rpow`: for real `α, β > 0`, any `κ` and `n`, there is `P₀` with
`κ (P+1)^n ≤ 2^(β P^α)` for every natural `P ≥ P₀`. This is pure real analysis (Mathlib
only). It is the one asymptotic fact behind the Lemma A.9 (`lem:transfer13`) cost absorption of
`CCore/LeafRowAddCost.lean`: the record length `r ≥ 2^((a_r/b_d) P^(1-ε))` and
`2^K ≥ 2^(a_d^c P^(εc)) / 2` both beat every polynomial in `P`.
-/

namespace SubNLogN.Machine.CCore.LeafRowAddCostAux

open Filter Asymptotics

/-- **A polynomial is eventually below a stretched exponential.** For `α, β > 0` and any `κ`,
`n`, there is `P₀` such that `κ (P+1)^n ≤ 2^(β P^α)` for all natural `P ≥ P₀`. -/
theorem poly_le_two_rpow (α β κ : ℝ) (n : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → κ * ((P : ℝ) + 1) ^ n ≤ (2 : ℝ) ^ (β * (P : ℝ) ^ α) := by
  have hb : 0 < β * Real.log 2 := mul_pos hβ (Real.log_pos one_lt_two)
  have h1 := (isLittleO_rpow_exp_pos_mul_atTop ((n : ℝ) / α) hb).comp_tendsto
    (tendsto_rpow_atTop hα)
  have h2 := h1.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hκ'0 : 0 < |κ| * 2 ^ n + 1 := by positivity
  have h3 := h2.def (c := 1 / (|κ| * 2 ^ n + 1)) (by positivity)
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp (h3.and (eventually_ge_atTop 1))
  refine ⟨P₀, fun P hP => ?_⟩
  obtain ⟨hle, hP1⟩ := hP₀ P hP
  have hPpos : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hP1' : (1 : ℝ) ≤ P := by exact_mod_cast hP1
  have hPn : ((P : ℝ) ^ α) ^ ((n : ℝ) / α) = (P : ℝ) ^ n := by
    rw [← Real.rpow_mul hPpos, mul_div_cancel₀ _ hα.ne', Real.rpow_natCast]
  have hexp : Real.exp (β * Real.log 2 * (P : ℝ) ^ α) = (2 : ℝ) ^ (β * (P : ℝ) ^ α) := by
    rw [Real.rpow_def_of_pos two_pos]
    congr 1
    ring
  simp only [Function.comp_apply, hPn, hexp] at hle
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hle
  have hA : ((P : ℝ) + 1) ^ n ≤ 2 ^ n * (P : ℝ) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) n
  have hT : (0 : ℝ) < (2 : ℝ) ^ (β * (P : ℝ) ^ α) := by positivity
  have hq : |κ| * 2 ^ n / (|κ| * 2 ^ n + 1) ≤ 1 := by
    rw [div_le_one hκ'0]
    linarith
  calc κ * ((P : ℝ) + 1) ^ n ≤ |κ| * ((P : ℝ) + 1) ^ n :=
        mul_le_mul_of_nonneg_right (le_abs_self κ) (by positivity)
    _ ≤ |κ| * (2 ^ n * (P : ℝ) ^ n) := mul_le_mul_of_nonneg_left hA (abs_nonneg κ)
    _ ≤ |κ| * (2 ^ n * (1 / (|κ| * 2 ^ n + 1) * (2 : ℝ) ^ (β * (P : ℝ) ^ α))) := by
        gcongr
    _ = (|κ| * 2 ^ n / (|κ| * 2 ^ n + 1)) * (2 : ℝ) ^ (β * (P : ℝ) ^ α) := by ring
    _ ≤ 1 * (2 : ℝ) ^ (β * (P : ℝ) ^ α) := mul_le_mul_of_nonneg_right hq hT.le
    _ = (2 : ℝ) ^ (β * (P : ℝ) ^ α) := one_mul _

end SubNLogN.Machine.CCore.LeafRowAddCostAux
