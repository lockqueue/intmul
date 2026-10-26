import WP.W9fDiv.Holds
import WP.W6a.DivRound

/-!
# WP.W9fDiv.OfSub — `W9fDiv_divRound` from `W3_subNat`

This goes through W6a's proved `W6a_divRound_holds : W3_subNat → W6a_divRound`, so it is the only
core-side module that depends on the W6a package.
-/

namespace WP.W9fDiv

open TMFw TMFw.Contracts

/-- **W9fDiv**, from W3's subtraction contract. -/
theorem W9fDiv_holds_of_sub (h : W3_subNat) : W9fDiv_divRound :=
  W9fDiv_holds (WP.W6a.W6a_divRound_holds h)

#assert_std_axioms W9fDiv_holds_of_sub

end WP.W9fDiv
