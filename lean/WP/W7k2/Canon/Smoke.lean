import WP.W7k2.Canon.Kernels
import WP.W7k2.Canon.Tape

/-!
# WP.W7k2.Canon.Smoke — evaluated checks of the canonical forms

The equalities are proved (`stdCharC_eq`, `tapC_eq`, `c0c1C_eq`, `tape_ref_eq`); these `#guard`
lines evaluate both sides at small inputs as an independent bit-exactness check.
-/

namespace WP.W7k2

open IntMul TMFw.Contracts

-- `stdChar(1/4) = i` on the `2^8` grid, both ways.
#guard stdCharC 6 1 4 false (computablePiScaledWithCost (6 + 2 + 4)).1.toNat ==
  (computableStdCharWithProgramCost 6 1 4 false).1
#guard stdCharC 5 3 8 true (computablePiScaledWithCost (5 + 2 + 4)).1.toNat ==
  (computableStdCharWithProgramCost 5 3 8 true).1

-- A tap with `s < pSub` (signed offset) and one past the threshold.
#guard tapC 3 2 2 1 0 (computablePiScaledWithCost (W7.tapPrec 2)).1.toNat
    (computableLog2ScaledWithCost (W7.tapPrec 2)).1.toNat ==
  (computableSincGaussianTapWithProgramCost 3 2 2 1 0).1
#guard tapC 3 2 2 1 2 (computablePiScaledWithCost (W7.tapPrec 2)).1.toNat
    (computableLog2ScaledWithCost (W7.tapPrec 2)).1.toNat ==
  (computableSincGaussianTapWithProgramCost 3 2 2 1 2).1

-- `c0`, `c1` in the three regimes `2u2 < r`, `2u2 = r`, `2u2 > r`.
#guard c0c1C 1 2 4 1 (computablePiScaledWithCost (2 * c0c1S 1 2)).1.toNat
    (computableLog2ScaledWithCost (2 * c0c1S 1 2)).1.toNat ==
  ((computableC0C1WithProgramCost 1 2 4 1).1.1.1, (computableC0C1WithProgramCost 1 2 4 1).1.2.1)
#guard c0c1C 1 2 4 2 (computablePiScaledWithCost (2 * c0c1S 1 2)).1.toNat
    (computableLog2ScaledWithCost (2 * c0c1S 1 2)).1.toNat ==
  ((computableC0C1WithProgramCost 1 2 4 2).1.1.1, (computableC0C1WithProgramCost 1 2 4 2).1.2.1)
#guard c0c1C 1 2 4 3 (computablePiScaledWithCost (2 * c0c1S 1 2)).1.toNat
    (computableLog2ScaledWithCost (2 * c0c1S 1 2)).1.toNat ==
  ((computableC0C1WithProgramCost 1 2 4 3).1.1.1, (computableC0C1WithProgramCost 1 2 4 3).1.2.1)

-- The leaf-only tape (`L = 0`), canonical vs. reference.
#guard tapeFromC 0 0 8 3 ==
  W7.tape W7.snapshotFormat (buildComputablePaperTables (buildQuantizedSpecPaperStop 0 8 3))

end WP.W7k2
