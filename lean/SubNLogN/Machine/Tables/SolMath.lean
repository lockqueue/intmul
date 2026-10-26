/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Tables
import SubNLogN.Math.Bridge.IntForms.Tables
import SubNLogN.Math.Bridge.IntForms.Solver

/-!
# K6 (`Machine/Tables/SolMath.lean`): integer targets of the solver table entries

**Scope (honest summary).** Pure definitions and read-back lemmas. For the concrete entries at
the machine rounding (`muConcreteR`, `ahatConcreteR`, `gamConcreteR` with `rr := roundHalfUpR`,
`SubNLogN/Math/Bridge/TablesConcrete.lean`), the stored numerators `realInt (P+2) ·`
(`SubNLogN/Machine/Contracts/Bridge.lean`) are the integers
* `muN = rhuDiv (2^(pC+2+q)) cmax`, `ahN = max 0 (rhuDiv (cmin·2^q) cmax)`,
* `gamN = rhuDiv (2^(Q+q)) (2^Q - X)` with `X = powTruncInt Q q ahN A` (truncated binary powering of
  the stored `â`, `Q = closurePrec q A t`),

where `cmax`/`cmin` are the two outputs of IntMul's `computableC0C1WithProgramCost ω pC (2t) (2u+1)`
oriented by `2u < t` (`q = P+2`, `pC = coeffPrec P`). `rhuDiv n d = ⌊n/d + 1/2⌋` (`0` for `d = 0`).
-/

namespace SubNLogN.Machine.Tables

open SubNLogN.Math.Common SubNLogN.Math.Common.GridInt SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Machine

/-- Numerator of `ĉ_max` (orientation `2u < t`). -/
def cmaxN (ω P t u : ℕ) : ℤ := if 2 * u < t then c0Int ω P t u else c1Int ω P t u

/-- Numerator of `ĉ_min`. -/
def cminN (ω P t u : ℕ) : ℤ := if 2 * u < t then c1Int ω P t u else c0Int ω P t u

/-- Stored numerator of `μ̂`. -/
def muN (ω P t u : ℕ) : ℤ := rhuDiv (2 ^ (coeffPrec P + 2 + (P + 2))) (cmaxN ω P t u)

/-- Stored numerator of `â`. -/
def ahN (ω P t u : ℕ) : ℤ := max 0 (rhuDiv (cminN ω P t u * 2 ^ (P + 2)) (cmaxN ω P t u))

/-- Stored numerator of `γ̂`. -/
def gamN (ω P t A u : ℕ) : ℤ :=
  closureFixedInt (P + 2) (closurePrec (P + 2) A t) (P + 2) (ahN ω P t u) A

theorem realInt_gridValR (F : ℕ) (a : ℤ) : realInt F (gridValR F a) = a := by
  unfold realInt
  rw [gridValR_mul_two_pow, round_intCast]

theorem muConcreteR_eq (ω P t u : ℕ) :
    muConcreteR roundHalfUpR ω P t u = gridValR (P + 2) (muN ω P t u) := by
  have key : ∀ n : ℤ, ((n : ℝ) * gridUnit (coeffPrec P + 2))⁻¹ =
      ((2 ^ (coeffPrec P + 2) : ℤ) : ℝ) / (n : ℝ) := by
    intro n
    rw [gridUnit, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
    push_cast
    ring
  have hpow : (2 : ℤ) ^ (coeffPrec P + 2) * 2 ^ (P + 2) = 2 ^ (coeffPrec P + 2 + (P + 2)) := by
    rw [← pow_add]
  unfold muConcreteR muN cmaxN
  split_ifs
  · rw [c0Hat_eq, key, roundHalfUpR_intCast_div, hpow]
  · rw [c1Hat_eq, key, roundHalfUpR_intCast_div, hpow]

theorem ahatConcreteR_eq (ω P t u : ℕ) :
    ahatConcreteR roundHalfUpR ω P t u = gridValR (P + 2) (ahN ω P t u) := by
  have key : ∀ m n : ℤ, ((m : ℝ) * gridUnit (coeffPrec P + 2)) /
      ((n : ℝ) * gridUnit (coeffPrec P + 2)) = (m : ℝ) / (n : ℝ) :=
    fun m n => mul_div_mul_right _ _ (gridUnit_pos _).ne'
  have hmax : ∀ k : ℤ, max 0 (gridValR (P + 2) k) = gridValR (P + 2) (max 0 k) := by
    intro k
    unfold gridValR
    rw [Int.cast_max, Int.cast_zero, max_mul_of_nonneg _ _ (gridUnit_pos _).le, zero_mul]
  unfold ahatConcreteR ahN cminN cmaxN
  split_ifs
  · rw [c0Hat_eq, c1Hat_eq, key, roundHalfUpR_intCast_div, hmax]
  · rw [c0Hat_eq, c1Hat_eq, key, roundHalfUpR_intCast_div, hmax]

theorem gamConcreteR_eq (ω P t A u : ℕ) :
    gamConcreteR roundHalfUpR ω P t A u = gridValR (P + 2) (gamN ω P t A u) := by
  unfold gamConcreteR gamN
  rw [ahatConcreteR_eq, gridValR, ← closureFixedInt_spec]
  rfl

theorem realInt_muConcreteR (ω P t u : ℕ) :
    realInt (P + 2) (muConcreteR roundHalfUpR ω P t u) = muN ω P t u := by
  rw [muConcreteR_eq, realInt_gridValR]

theorem realInt_ahatConcreteR (ω P t u : ℕ) :
    realInt (P + 2) (ahatConcreteR roundHalfUpR ω P t u) = ahN ω P t u := by
  rw [ahatConcreteR_eq, realInt_gridValR]

theorem realInt_gamConcreteR (ω P t A u : ℕ) :
    realInt (P + 2) (gamConcreteR roundHalfUpR ω P t A u) = gamN ω P t A u := by
  rw [gamConcreteR_eq, realInt_gridValR]

/-- The solver record of `tabOf` as integers. -/
theorem solRec_tabOf {d : ℕ} (ω P : ℕ) (t : Fin d → ℕ) (i : Fin d) (u : ℕ) :
    solRec P (tabOf ω P t) i u =
      [(muN ω P (t i) u, 0), (ahN ω P (t i) u, 0), (gamN ω P (t i) (prefixProd t i) u, 0)] := by
  simp only [solRec, tabOf, realInt_muConcreteR, realInt_ahatConcreteR, realInt_gamConcreteR]

end SubNLogN.Machine.Tables
