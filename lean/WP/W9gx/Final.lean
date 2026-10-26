import WP.W9gx.Main
import WP.W9gx.CostLeaf

/-!
# WP.W9gx.Final — `W9_leafFFT_holds`

W9g's leaf program `leafProg X` (WP.W9g.Top), its spec `leaf_rs`, the cost bound `leafCost_le`,
the Bridge and the embedding (`W9_leafFFT_of_top`) give the LEAF kernel contract from the W5/W3
contracts it calls (`W5_mulAt Mul`, `W3_addInt`, `W3_subInt`, `W3_shlVar`, `W3_shrVar`).
-/

namespace WP.W9gx

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W9g

/-- **W9.leafFFT** (the LEAF node kernel), with constant `1500·(CM+CA+CS+CL+CR+31)`. -/
theorem W9_leafFFT_holds (Mul : ℕ → ℕ) (hM : W5_mulAt Mul) (hA : W3_addInt) (hS : W3_subInt)
    (hL : W3_shlVar) (hR : W3_shrVar) : W9_leafFFT Mul :=
  W9_leafFFT_of_top Mul hM hA hS hL hR leafProg leafProg_closed leafCost (fun hok => leaf_rs hok)
    (fun CM CA CS CL CR => ⟨_, fun w pin p K => leafCost_le CM CA CS CL CR Mul w pin p K⟩)

#assert_std_axioms W9_leafFFT_holds

end WP.W9gx
