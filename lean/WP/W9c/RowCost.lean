import WP.W9c.RowCostBC
import WP.W9c.RowCostAD

/-!
# WP.W9c.RowCost — the row driver's cost inequality `RowCostLe`

`costB + costC` and the assembly are `rowCostLe_of_AD` (`RowCostBC`); `costA + costD` is
`rowCostAD_holds` (`RowCostAD`).
-/

namespace WP.W9c

/-- **Cost obligation of the row driver** (`RowCostDefs.RowCostLe`), discharged. -/
theorem rowCostLe_holds : RowCostLe := rowCostLe_of_AD rowCostAD_holds

#assert_std_axioms rowCostLe_holds

end WP.W9c
