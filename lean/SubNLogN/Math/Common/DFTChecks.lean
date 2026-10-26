import SubNLogN.Math.Common.DFT

namespace SubNLogN.Math.Common.DFTChecks

open SubNLogN.Math.Common

/-!
# Common: regression checks for the mixed-radix index maps (Section 4.1 (`sec:bridge-conventions`), eq. (`eq:freq-digits`))

Convention (recorded once, proved in `DFT.lean`): `encIn t = finPiFinEquiv`, coordinate (axis) `0`
least significant: `encIn t j = ∑_i j_i A_i` with `A_i = prefixProd t i` (`encIn_val`), i.e. the
paper's `j = ∑ j_h A_h` with `j_1` least significant; `encFreq t u = ∑_i u_i · suffixProd t i`
(`encFreq_val`), `suffixProd t i = R/A_{i+1}`, i.e. `f(u) = ∑ u_h R/A_{h+1}` with `u_d` least
significant. Digit extraction: `encIn_symm_apply`, `encFreq_symm_apply`. The examples below check
both orders by `decide` on `t = (2, 3)`.
-/

/-- Shape `t = (2, 3)`: `R = 6`, `A_1 = 1`, `A_2 = 2`. -/
abbrev t23 : Fin 2 → ℕ := ![2, 3]

/-- The digit tuple `(j_1, j_2) = (1, 2)`. -/
def j12 : Idx t23 := Fin.cons (1 : Fin 2) (Fin.cons (2 : Fin 3) finZeroElim)

/-- Input order: `j = j_1·A_1 + j_2·A_2 = 1 + 2·2 = 5` (axis 0 least significant). -/
example : ((encIn t23 j12 : Fin (totalLen t23)) : ℕ) = 5 := by decide

/-- Frequency order: `f(u) = u_1·R/A_2 + u_2·R/A_3 = 1·3 + 2·1 = 5` (last axis least significant). -/
example : ((encFreq t23 j12 : Fin (totalLen t23)) : ℕ) = 5 := by decide

/-- A tuple distinguishing the two orders: `(j_1, j_2) = (1, 0)` gives input index `1` but
frequency index `3`. -/
def j10 : Idx t23 := Fin.cons (1 : Fin 2) (Fin.cons (0 : Fin 3) finZeroElim)

example : ((encIn t23 j10 : Fin (totalLen t23)) : ℕ) = 1 := by decide
example : ((encFreq t23 j10 : Fin (totalLen t23)) : ℕ) = 3 := by decide

/-- Digit extraction agrees: frequency index `3` has digits `(1, 0)`. -/
example : (((encFreq t23).symm ⟨3, by decide⟩ 0 : Fin 2) : ℕ) = 1 := by decide
example : (((encFreq t23).symm ⟨3, by decide⟩ 1 : Fin 3) : ℕ) = 0 := by decide

/-- The proved closed forms give the same numbers. -/
example : ((encIn t23 j10 : Fin (totalLen t23)) : ℕ) = ∑ i, ((j10 i : Fin (t23 i)) : ℕ) * prefixProd t23 i :=
  encIn_val t23 j10

example : ((encFreq t23 j10 : Fin (totalLen t23)) : ℕ) = ∑ i, ((j10 i : Fin (t23 i)) : ℕ) * suffixProd t23 i :=
  encFreq_val t23 j10

end SubNLogN.Math.Common.DFTChecks
