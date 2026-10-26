import WP.W9fF.SL
import IntMul.MaterializedAndComputable.ComputableExactSolvers

/-!
# WP.W9fF.Bnd — the class-B boundary value `Z0` as a straight-line block

`pBnd` computes `Z0 = gRatioQuantize q Y0 (c,0) zPart (a,0) (c,0) zHom` into `W1, W2` from
`Y01 Y02` (first input), `Z1 Z2` (zPart), `G1 G2` (zHom) and the parameters `DA = a`, `MC = c`,
`SS = 2^(q+2)`: 15 products, 6 additions/subtractions, 2 rounded divisions (`divRoundRatInt`);
only the temporaries `T1 … T8` and `W1, W2` are written.

* `N = (Y01·S − c·Z1, Y02·S − c·Z2)` in `T1, T2`; `D = (a·S + c·G1, c·G2)` in `T3, T4`;
* `numRe = (N₁D₁ + N₂D₂)·S` in `T5`, `numIm = (N₂D₁ − N₁D₂)·S` in `T6`, `den = D₁² + D₂²` in `T7`;
* `W1 = divRoundRatInt numRe den`, `W2 = divRoundRatInt numIm den`.

`ev_pBnd`: value (the imaginary parts of `(c,0)`, `(a,0)` vanish, so the snapshot's `gMulUnit`
products agree with the program's up to `ring`) and frame.
-/

namespace WP.W9fF

open IntMul

/-- `Z0 = gRatioQuantize q (Y01,Y02) (c,0) (Z1,Z2) (a,0) (c,0) (G1,G2)` into `W1, W2`. -/
def pBnd : SL :=
  block (op .T1 .mul .Y01 .SS)
    [op .T2 .mul .MC .Z1, op .T1 .sub .T1 .T2,
     op .T2 .mul .Y02 .SS, op .T3 .mul .MC .Z2, op .T2 .sub .T2 .T3,
     op .T3 .mul .DA .SS, op .T4 .mul .MC .G1, op .T3 .add .T3 .T4,
     op .T4 .mul .MC .G2,
     op .T5 .mul .T1 .T3, op .T6 .mul .T2 .T4, op .T5 .add .T5 .T6, op .T5 .mul .T5 .SS,
     op .T6 .mul .T2 .T3, op .T7 .mul .T1 .T4, op .T6 .sub .T6 .T7, op .T6 .mul .T6 .SS,
     op .T7 .mul .T3 .T3, op .T8 .mul .T4 .T4, op .T7 .add .T7 .T8,
     op .W1 .divR .T5 .T7, op .W2 .divR .T6 .T7]

/-- **The boundary block**: value `Z0` in `W1, W2`; only `W1 W2 T1 … T8` change. -/
theorem ev_pBnd (env : V → ℤ) {q H : ℕ} {μ a c : ℤ} (hp : Prm env q H μ a c) :
    (ev pBnd env .W1, ev pBnd env .W2) =
      gRatioQuantize q (env .Y01, env .Y02) (c, 0) (env .Z1, env .Z2) (a, 0) (c, 0)
        (env .G1, env .G2) ∧
    ∀ v, v ∉ [V.W1, .W2, .T1, .T2, .T3, .T4, .T5, .T6, .T7, .T8] → ev pBnd env v = env v := by
  refine ⟨?_, fun v hv => ev_of_not_mem pBnd env v ?_⟩
  · refine Prod.ext ?_ ?_
    · simp only [pBnd, ev_block_cons, ev_block_nil, ev_op, Function.update_apply, reduceCtorEq,
        ↓reduceIte, sem_mul, sem_add, sem_sub, sem_divR, hp.ss, hp.mc, hp.da, gRatioQuantize,
        gDivQuantizeUnscaled, gQuantizeRat, gSub, gAdd, gMulUnit]
      congr 1 <;> ring
    · simp only [pBnd, ev_block_cons, ev_block_nil, ev_op, Function.update_apply, reduceCtorEq,
        ↓reduceIte, sem_mul, sem_add, sem_sub, sem_divR, hp.ss, hp.mc, hp.da, gRatioQuantize,
        gDivQuantizeUnscaled, gQuantizeRat, gSub, gAdd, gMulUnit]
      congr 1 <;> ring
  · revert hv
    cases v <;> simp [pBnd]

#assert_std_axioms ev_pBnd

end WP.W9fF
