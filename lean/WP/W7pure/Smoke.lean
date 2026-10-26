import WP.W7pure.TableCost
import WP.W7pure.TapeBound

/-!
# WP.W7pure.Smoke — numeric sanity checks of the W7 pure bounds

W7-pure has no machine program, so there is nothing to run on the framework harness. Instead:
1. along the headline schedule `W8.hSpec n`, `n = 2^j`, evaluate the table budget
   `precomputeSeriesTableCost` and the structural tape bound `specTapeBound … 0 (W8.hSpec n)`
   (`= W7.tapeBound` of every faithful hierarchy, `tapeBoundFrom_eq_spec`), next to the proved closed
   forms `tableCostConst·(√n+1)·(log₂n+1)^8` and `tapeBoundConst·(√n+1)·(log₂n+1)^3`;
2. build the snapshot's reference tables for a leaf-only schedule (`L = 1, p = 8, K = 4`: `2^4 ≤ 4·8²`)
   and compare the actual tape length with `W7.tapeBound` (`W7_tapeSize`).
-/

namespace WP.W7pure.Smoke

open TMFw.Contracts IntMul

/-- `(j, cost, cost / ((√n+1)(ℓ)^8), tape bound, bound / ((√n+1)(ℓ)^3))` for `n = 2^j`,
`ℓ = log₂ n + 1`. The proved constants are `tableCostConst = 2^72·88^6 ≈ 2^110.75` and
`tapeBoundConst = 377831700`. -/
def row (j : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let n := 2 ^ j
  let c := (IntMulTM.Contracts.W8.hSpec n).precomputeSeriesTableCost
  let t := specTapeBound W7.snapshotFormat 0 (IntMulTM.Contracts.W8.hSpec n)
  (j, c, c / ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8), t,
    t / ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3))

#guard tableCostConst = 2 ^ 72 * 88 ^ 6
#guard tapeBoundConst = 377831700

#eval [10, 20, 40, 64, 100, 200, 400].map row

/-- Both proved closed forms hold at `n = 2^1, …, 2^300` and at every `n ∈ [0, 2000]`. -/
def boundsHold : Bool :=
  let ok (n : ℕ) : Bool :=
    decide ((IntMulTM.Contracts.W8.hSpec n).precomputeSeriesTableCost ≤
        tableCostConst * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8) &&
      decide (specTapeBound W7.snapshotFormat 0 (IntMulTM.Contracts.W8.hSpec n) ≤
        tapeBoundConst * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3)
  ((List.range 300).all fun j => ok (2 ^ (j + 1))) && ((List.range 2001).all ok)

#guard boundsHold

/-- Reference tables (the snapshot's `buildComputablePaperTables`) of a leaf-only schedule. -/
def leafTables : ComputablePaperFastDFTSpec :=
  buildComputablePaperTables (buildQuantizedSpecPaperStop 1 8 4)

-- `(tape length, W7.tapeBound)` of the leaf-only reference tables.
#eval ((W7.tape W7.snapshotFormat leafTables).length, W7.tapeBound W7.snapshotFormat leafTables)

#guard (W7.tape W7.snapshotFormat leafTables).length ≤ W7.tapeBound W7.snapshotFormat leafTables

end WP.W7pure.Smoke
