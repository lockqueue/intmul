import WP.W9fDiv.Spec
import WP.W9fDiv.Proof

/-!
# WP.W9fDiv.Holds — `W9fDiv_divRound` from `W6a_divRound`

This module is standalone: it depends on the frozen contracts and the snapshot only. `OfSub`
derives the variant whose hypothesis is `W3_subNat`, through W6a's proved `divRound`.
-/

namespace WP.W9fDiv

open TMFw TMFw.Contracts

/-- **W9fDiv**, from the W6a rounding-division contract. -/
theorem W9fDiv_holds (h : W6a_divRound) : W9fDiv_divRound := by
  unfold W9fDiv_divRound
  rw [divRound_bridge]
  exact W9fDivCore_of_divRound h

#assert_std_axioms W9fDiv_holds

end WP.W9fDiv
