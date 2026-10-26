import WP.W9fM.Move
import Contracts.W9.Pipeline

/-!
# WP.W9fM.Holds — `W9f_moveEntries` in the binding shape `W3_all → W4_all → …`

The proof is `WP.W9fM.moveEntries_holds` (`Move.lean`). It is a direct loop over `Loc 2 1` and uses
neither hypothesis: no W3 or W4 subroutine is called, so this binding is a restatement.
-/

namespace WP.W9fM

open TMFw.Contracts TMFw.Contracts.W9 WP.W9f

/-- **W9f.moveEntries** (sub-kernel S4) in the requested shape; the hypotheses are unused. -/
theorem W9f_moveEntries_holds (_h3 : W3_all) (_h4 : W4_all) : W9f_moveEntries :=
  moveEntries_holds

#assert_std_axioms W9f_moveEntries_holds

end WP.W9fM
