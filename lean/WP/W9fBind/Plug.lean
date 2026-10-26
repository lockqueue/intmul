import WP.W9fBind.Final
import WP.W9fC.Main
import WP.W9fNF.Holds

/-!
# WP.W9fBind.Plug — `W9_columns` with every sub-kernel plugged in

* S3 `WP.W9fC.W9_columns_of_columnSolve` (`WP.W9fC`);
* the Nyquist finish `WP.W9fNF.W9f_nyqFinish_holds : W3_all → W9f_nyqFinish` (`WP.W9fNF`;
  its interface is the single copy `WP/W9fN/FinishSpec.lean`).

With S1 (W9fF), S2 (W9fN) and S4 (W9fM) already in `W9_columns_final`, no hypothesis is left beyond
the binding shape: `W9_columns_holds_final`.
-/

namespace WP.W9fBind

open TMFw.Contracts

/-- **`W9_columnSolve`** from the machine contracts. -/
theorem W9_columnSolve_all :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columnSolve Mul :=
  W9_columnSolve_final WP.W9fNF.W9f_nyqFinish_holds

/-- **`W9_columns`** from the machine contracts (no hypotheses beyond the binding shape). -/
theorem W9_columns_holds_final : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul :=
  W9_columns_final WP.W9fNF.W9f_nyqFinish_holds WP.W9fC.W9_columns_of_columnSolve

#assert_std_axioms W9_columnSolve_all W9_columns_holds_final

end WP.W9fBind
