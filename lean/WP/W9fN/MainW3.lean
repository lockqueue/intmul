import WP.W9fN.Main
import WP.W9fN.KitW3

/-!
# WP.W9fN.MainW3 — `W9f_nyqCore` with only the Nyquist finish as an extra hypothesis

`OpsHyp` is discharged from `W3_all` through W9fOps (`opsHyp_of_W3`, KitW3.lean). The remaining
hypothesis `W9f_nyqFinish` is proved in `WP.W9fNF`; with `W9f_nyqFinish_holds : W3_all → …`,
`W9f_nyqCore_holds Mul h5 h3 h4 h6 := W9f_nyqCore_of_finish (W9f_nyqFinish_holds h3) Mul h5 h3 h4 h6`.
-/

namespace WP.W9fN

open TMFw TMFw.Contracts

theorem W9f_nyqCore_of_finish (hF : WP.W9f.W9f_nyqFinish) :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → WP.W9f.W9f_nyqCore Mul :=
  fun Mul h5 h3 h4 h6 => W9f_nyqCore_of hF (opsHyp_of_W3 h3) Mul h5 h3 h4 h6

#assert_std_axioms W9f_nyqCore_of_finish

end WP.W9fN
