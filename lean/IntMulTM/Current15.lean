import IntMulTM.Current14
import WP.W9c.Main
import WP.W9fBind.Plug

/-!
# Integrator's tracking theorem, version 15

`intMul_TM2_nlogn_current14` with, in addition:
* `WP.W9c.W9_spread_stage` (spread; packages wp/W9c, wp/W9cS);
* `WP.W9fBind.W9_columns_holds_final` (column solvers; packages wp/W9f, wp/W9fF, wp/W9fN,
  wp/W9fNF, wp/W9fM, wp/W9fC, wp/W9fOps, wp/W9fDiv, wp/W9fW, wp/W9fBind).
Remaining: W7 c0c1 only.
-/

namespace IntMulTM.Final

open TMFw TMFw.Contracts WP.Top

theorem intMul_TM2_nlogn_current15
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current14 h7c01 WP.W9c.W9_spread_stage WP.W9fBind.W9_columns_holds_final

#assert_std_axioms intMul_TM2_nlogn_current15

end IntMulTM.Final
