import WP.Top.Main
import WP.Top.CostShape
import WP.W0m.Main
import WP.W6a.DivMod
import WP.W7pure.TableCost
import WP.W7pure.TapeBound
import WP.W5.Bound

/-!
# WP.Top.Remaining2 — the tracking theorem with W9's cost shape discharged

`intMul_TM2_nlogn_of_remaining2` is the integrator's `intMul_TM2_nlogn_of_remaining`
(`IntMulTM.Remaining`) with the hypothesis `hshape : W9CostShape wdF wdI wR` (W10b)
replaced by the width bound `hw`, owned by W11b:
`∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ, wdI n ℓ, wR n ≤ cw·(log₂ n + 1)`.

The cost shape comes from `W9CostShape_of_W10b hconv hw` (WP.Top.CostShape), which uses W10b's
`w9_bounds`, `w9_cost_le` and `w7_tape_le` together with TapeConv's size clause.

| remaining hypothesis | owner |
|---|---|
| `W3_addNat`, `W3_subNat` | W3 |
| `W7_buildTables W7.snapshotSchedule` | W7k1 + W7k2 |
| `W5_toom3Mul` | W5 |
| `∀ Mul, W5_mulAt Mul → W9_multiply Mul` | W9a..h + W9comp |
| `TapeConv` | the converter author |
| `W9RootOK wdF wdI wR` | W11b |
| width bound `hw` | W11b |

The following are plugged in as proved:
* W0m and W6a (divMod);
* W7pure (table cost, tape bound) and W5 (`W5_T3_bound`);
* W10, W10b (via CostShape), W11 (W9's value), W12, and Top.
-/

namespace WP.Top

open TMFw TMFw.Contracts IntMulTM.Contracts.Top

/-- **The headline from the remaining stage contracts**, with W9's cost shape discharged by W10b. -/
theorem intMul_TM2_nlogn_of_remaining2
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h3add : W3_addNat)
    (h3sub : W3_subNat)
    (h7 : W7_buildTables W7.snapshotSchedule)
    (h5 : W5_toom3Mul)
    (h9 : ∀ Mul, W5_mulAt Mul → W9_multiply Mul)
    (hconv : TapeConv)
    (hroot : W9RootOK wdF wdI wR)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_of_stages wdF wdI wR
    (WP.W0m.W0m_inputStage_holds h3add (WP.W6a.W6a_divModNat_holds h3sub))
    h7 WP.W7pure.W7_tableCost_sqrt_holds WP.W7pure.W7_tapeBound_sqrt_holds
    h5 WP.W5.W5_T3_bound_holds h9 hconv hroot (W9CostShape_of_W10b hconv hw)

#assert_std_axioms intMul_TM2_nlogn_of_remaining2

end WP.Top
