import WP.W9f.Binding
import WP.W9fF.Main
import WP.W9fN.MainW3
import WP.W9fM.Holds

/-!
# WP.W9fBind.Final — the W9 column solvers from their sub-kernels

`W9_columns_final : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul` is W9f's
composition `WP.W9f.W9_columns_holds` applied to the proved sub-kernels:
* S1 `WP.W9fF.W9f_fwdCore_holds` (forward core),
* S2 `WP.W9fN.W9f_nyqCore_of_finish` (Nyquist core, given the Nyquist finish),
* S4 `WP.W9fM.W9f_moveEntries_holds` (entry mover).

Two remaining sub-kernels are taken as explicit hypotheses (discharged in `WP.W9fBind.Plug`):
* `hNF : W3_all → WP.W9f.W9f_nyqFinish` (interface `WP/W9fN/FinishSpec.lean`);
* `hC : ∀ Mul, W3_all → W4_all → W9_columnSolve Mul → W9_columns Mul` (S3, `WP.W9fC`; both Props
  are frozen in `Contracts/W9/Post.lean`).
-/

namespace WP.W9fBind

open TMFw.Contracts

/-- **`W9_columnSolve`** in the binding shape (needs only the Nyquist finish). -/
theorem W9_columnSolve_final (hNF : W3_all → WP.W9f.W9f_nyqFinish) :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columnSolve Mul :=
  WP.W9f.W9_columnSolve_holds WP.W9fF.W9f_fwdCore_holds
    (fun Mul h5 h3 h4 h6 => WP.W9fN.W9f_nyqCore_of_finish (hNF h3) Mul h5 h3 h4 h6)
    WP.W9fM.W9f_moveEntries_holds

/-- **`W9_columns`** in the binding shape. -/
theorem W9_columns_final (hNF : W3_all → WP.W9f.W9f_nyqFinish)
    (hC : ∀ Mul, W3_all → W4_all → W9_columnSolve Mul → W9_columns Mul) :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul :=
  WP.W9f.W9_columns_holds WP.W9fF.W9f_fwdCore_holds
    (fun Mul h5 h3 h4 h6 => WP.W9fN.W9f_nyqCore_of_finish (hNF h3) Mul h5 h3 h4 h6)
    WP.W9fM.W9f_moveEntries_holds hC

#assert_std_axioms W9_columnSolve_final W9_columns_final

end WP.W9fBind
