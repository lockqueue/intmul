import WP.W9c.MainOf
import WP.W9c.RowCost
import WP.W9cS.Main

/-!
# WP.W9c.Main — `W9_spreadRow` and `W9_spread` in the binding shape

`∀ Mul, W5_mulAt Mul → W3_all → W9_spreadRow Mul` (and `W9_spread Mul`). One shared
multiplication cost `Mul`; the W3 arithmetic contracts are taken as explicit hypotheses. Everything
else is proved in this package, with `wp/W9cS` for the all-rows driver.
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9

/-- **W9.spreadRow** (P3, one row). -/
theorem W9_spreadRow_holds (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul) (h3 : W3_all) :
    W9_spreadRow Mul :=
  W9_spreadRow_of_cost Mul h5 h3 rowCostLe_holds

/-- **W9.spread** (P3, all rows). -/
theorem W9_spread_holds (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul) (h3 : W3_all) : W9_spread Mul :=
  W9_spread_of_spreadRow Mul (W9_spreadRow_holds Mul h5 h3)

/-- `W9_spread` in the field shape of `WP.W9comp.W9StageThms.spread` (W4/W6a unused). -/
theorem W9_spread_stage : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul :=
  fun Mul h5 h3 _ _ => W9_spread_holds Mul h5 h3

#assert_std_axioms W9_spreadRow_holds W9_spread_holds W9_spread_stage

end WP.W9c
