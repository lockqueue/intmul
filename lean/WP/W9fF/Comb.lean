import WP.W9fF.SL
import Contracts.W6

/-!
# WP.W9fF.Comb — one output combine step as a straight-line block

`pComb` computes `gCombineQuantize q (Z1,Z2) (W1,W2) (G1,G2)` (zPart, boundary value `Z0`, zHom)
into `T7, T8`, as a rounding shift by `q + 2` (`W8_gCombineQuantize_shift_holds`):
`T7 = (Z1·S + (W1·G1 − W2·G2) + 2^(q+1)) >>> (q+2)`,
`T8 = (Z2·S + (W1·G2 + W2·G1) + 2^(q+1)) >>> (q+2)` with `S = SS = 2^(q+2)`, `HALF = 2^(q+1)`,
`S2 = q + 2`: 6 products, 6 additions/subtractions, 2 arithmetic shifts; only `T1 T2 T3 T7 T8`
are written.
-/

namespace WP.W9fF

open IntMul

/-- `gCombineQuantize q (Z1,Z2) (W1,W2) (G1,G2)` into `T7, T8`. -/
def pComb : SL :=
  block (op .T1 .mul .Z1 .SS)
    [op .T2 .mul .W1 .G1, op .T3 .mul .W2 .G2, op .T2 .sub .T2 .T3, op .T1 .add .T1 .T2,
     op .T1 .add .T1 .HALF, op .T7 .sar .T1 .S2,
     op .T1 .mul .Z2 .SS, op .T2 .mul .W1 .G2, op .T3 .mul .W2 .G1, op .T2 .add .T2 .T3,
     op .T1 .add .T1 .T2, op .T1 .add .T1 .HALF, op .T8 .sar .T1 .S2]

/-- Rounding division by `2^(q+2)` as an arithmetic shift. -/
theorem sar_half_eq_divRoundPow2 (x : ℤ) (q : ℕ) :
    (x + ((2 ^ (q + 1) : ℕ) : ℤ)) >>> (q + 2) = divRoundPow2 x (q + 2) := by
  rw [Int.shiftRight_eq_div_pow, divRoundPow2, if_neg (by omega),
    show q + 2 - 1 = q + 1 by omega]

/-- **The combine block**: value `gCombineQuantize` in `T7, T8`; only `T1 T2 T3 T7 T8` change. -/
theorem ev_pComb (env : V → ℤ) {q H : ℕ} {μ a c : ℤ} (hp : Prm env q H μ a c) :
    (ev pComb env .T7, ev pComb env .T8) =
      gCombineQuantize q (env .Z1, env .Z2) (env .W1, env .W2) (env .G1, env .G2) ∧
    ∀ v, v ∉ [V.T1, .T2, .T3, .T7, .T8] → ev pComb env v = env v := by
  refine ⟨?_, fun v hv => ev_of_not_mem pComb env v ?_⟩
  · have hs2 : (env .S2).natAbs = q + 2 := by
      rw [hp.s2]
      rfl
    rw [IntMulTM.Contracts.W8_gCombineQuantize_shift_holds, ← sar_half_eq_divRoundPow2,
      ← sar_half_eq_divRoundPow2]
    simp only [pComb, ev_block_cons, ev_block_nil, ev_op, Function.update_apply, reduceCtorEq,
      ↓reduceIte, sem_mul, sem_add, sem_sub, sem_sar, hp.ss, hp.half, hs2]
  · revert hv
    cases v <;> simp [pComb]

#assert_std_axioms sar_half_eq_divRoundPow2 ev_pComb

end WP.W9fF
