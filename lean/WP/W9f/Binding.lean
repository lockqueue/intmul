import WP.W9f.Final
import Contracts.W9.Pipeline

/-!
# WP.W9f.Binding — the column solvers in the integrator's binding shape

The four column-solver sub-kernels are taken as explicit contract hypotheses:
* S1 `W9f_fwdCore` (wp/W9fF), S2 `W9f_nyqCore` (wp/W9fN), S4 `W9f_moveEntries` (wp/W9fM);
* S3 the column driver `W9_columns_of_columnSolve` (wp/W9fC).

Both conclusions use ONE shared `Mul` (`∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → …`).
-/

namespace WP.W9f

open TMFw.Contracts

/-- **`W9_columnSolve`** in the binding shape, from the sub-kernel theorems. -/
theorem W9_columnSolve_holds
    (hF : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9f_fwdCore Mul)
    (hN : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9f_nyqCore Mul)
    (hM : W3_all → W4_all → W9f_moveEntries) :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columnSolve Mul :=
  fun Mul h5 h3 h4 h6 =>
    W9_columnSolve_of_cores Mul (hF Mul h5 h3 h4 h6) (hN Mul h5 h3 h4 h6) (hM h3 h4)

/-- **`W9_columns`** in the binding shape, from the column driver and `W9_columnSolve_holds`. -/
theorem W9_columns_holds
    (hF : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9f_fwdCore Mul)
    (hN : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9f_nyqCore Mul)
    (hM : W3_all → W4_all → W9f_moveEntries)
    (hC : ∀ Mul, W3_all → W4_all → W9_columnSolve Mul → W9_columns Mul) :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul :=
  fun Mul h5 h3 h4 h6 => hC Mul h3 h4 (W9_columnSolve_holds hF hN hM Mul h5 h3 h4 h6)

#assert_std_axioms W9_columnSolve_holds W9_columns_holds

end WP.W9f
