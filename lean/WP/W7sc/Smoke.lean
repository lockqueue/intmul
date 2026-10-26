import WP.W7sc.Math

/-!
# WP.W7sc.Smoke — evaluated checks of the kernel's value formulas

The machine run itself needs concrete instances of every called contract (W3, W5, W6a, W7k1's
`π`, W7k3's series), which are hypotheses here, so it is not executed. These checks evaluate the
per-operation value formulas the program computes (`reV`, `imV`, built from `ntv … imP`) at the
snapshot's own `π` and compare them with `computableStdCharWithProgramCost` (tiny inputs).
-/

namespace WP.W7sc

-- `stdChar(1/4) = i` on the `2^(6+2)` grid, both signs.
#guard (reV 6 (IntMul.computablePiScaledWithCost (6 + 2 + 4)).1.toNat 1 4,
    imV 6 (IntMul.computablePiScaledWithCost (6 + 2 + 4)).1.toNat 1 4 false) ==
  (IntMul.computableStdCharWithProgramCost 6 1 4 false).1
#guard (reV 6 (IntMul.computablePiScaledWithCost (6 + 2 + 4)).1.toNat 1 4,
    imV 6 (IntMul.computablePiScaledWithCost (6 + 2 + 4)).1.toNat 1 4 true) ==
  (IntMul.computableStdCharWithProgramCost 6 1 4 true).1
-- `stdChar(3/8)` at `q = 6`.
#guard (reV 6 (IntMul.computablePiScaledWithCost (6 + 2 + 4)).1.toNat 3 8,
    imV 6 (IntMul.computablePiScaledWithCost (6 + 2 + 4)).1.toNat 3 8 false) ==
  (IntMul.computableStdCharWithProgramCost 6 3 8 false).1
-- The values themselves: `stdChar(1/4) ≈ (0, 256)`, `stdChar(-1/4) ≈ (0, -256)`.
#guard (let z := (reV 6 (IntMul.computablePiScaledWithCost (6 + 2 + 4)).1.toNat 1 4,
    imV 6 (IntMul.computablePiScaledWithCost (6 + 2 + 4)).1.toNat 1 4 true);
  -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -258 ≤ z.2 ∧ z.2 ≤ -254)
-- The snapshot width at `q = 6`, `den = 4`: `w = 9·6 + 238 + 2·log₂ 4 = 296`.
#guard wv 6 4 == 296

end WP.W7sc
