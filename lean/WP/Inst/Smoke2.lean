import WP.Inst.W7k1
import WP.Inst.Smoke

/-!
# WP.Inst.Smoke2 — the W6a and W7k1 instances run through `machine p σ0`

Same harness as `WP.Inst.Smoke` (exact named stacks, all scratch stacks empty again). The expected values
are the contracts' post-states: `a / b`, `a % b` (`W6a_divModNat`), `divRoundRatInt` (`W6a_divRound`),
`Nat.sqrt` (`W7_isqrt`), and the snapshot's `computableLog2ScaledWithCost` / `computablePiScaledWithCost`
(`W7_log2Scaled`, `W7_piScaled`).
-/

namespace WP.Inst.Smoke2

open TMFw TMFw.Lib TMFw.Contracts IntMulTM.Exec WP.Inst WP.Inst.Smoke

#guard [(0, 1), (1, 1), (7, 2), (255, 16), (1000, 7), (2 ^ 64 - 1, 3), (2 ^ 100 + 5, 2 ^ 40 + 1)].all
  fun (a, b) => check divModNat.prog divModNat.r0 [natSyms a, natSyms b, [], []]
    [natSyms a, natSyms b, natSyms (a / b), natSyms (a % b)]

#guard [((5 : ℤ), 2), (-5, 2), (7, 3), (-7, 3), (0, 1), (2 ^ 70 + 3, 1000), (-(2 ^ 70) - 3, 999)].all
  fun (num, den) => check divRound.prog divRound.r0 [intSyms num, natSyms den, []]
    [intSyms num, natSyms den, intSyms (divRoundRatInt num den)]

#guard [0, 1, 2, 3, 15, 16, 17, 255, 4095, 2 ^ 64 - 1].all fun a =>
  check isqrt.prog isqrt.r0 [natSyms a, []] [natSyms a, natSyms (Nat.sqrt a)]

#guard [0, 1, 2, 3].all fun B =>
  check log2Scaled.prog log2Scaled.r0 [natSyms B, []]
    [natSyms B, intSyms (IntMul.computableLog2ScaledWithCost B).1]

#guard [0, 1, 2].all fun B =>
  check piScaled.prog piScaled.r0 [natSyms B, []]
    [natSyms B, intSyms (IntMul.computablePiScaledWithCost B).1]

-- `(B, ln steps, ln value)`; π steps (measured once): 46377, 75083, 113650, 163920 for B = 0..3
#eval [0, 1, 2, 3].map fun B =>
  (B, (run log2Scaled.prog log2Scaled.r0 [natSyms B, []]).map Prod.fst,
    (IntMul.computableLog2ScaledWithCost B).1)

end WP.Inst.Smoke2
