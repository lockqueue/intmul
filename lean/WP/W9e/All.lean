import WP.W9e.Routes
import Contracts.W9.Pipeline

/-!
# WP.W9e.All — the three POST routing phases from the bundled machine contracts

`W9e_holds`: from `W3_all` and `W4_all` (Contracts.W9.Pipeline) the phases Q2, Q3+Q4 and Q6 hold.

Of these bundles only the following are used:
* `W4_transpose .down .down`, `W4_oddStrideFactor`, `W4_oddRoute .down .down`;
* `W3_cmpNat`, `W3_subNat`, `W3_shlVar`, `W3_splitAt`.

`W4_moveRecord` is not used: the record moves of Q3 use the proved `moveRec` macro (Macros).
-/

namespace WP.W9e

open TMFw TMFw.Contracts TMFw.Contracts.W9

/-- Q2 from `W4_all`. -/
theorem W9_postTranspose_of_all (h4 : W4_all) : W9_postTranspose :=
  W9_postTranspose_holds h4.1

/-- Q3+Q4 from `W3_all` and `W4_all`. -/
theorem W9_columnRoutes_of_all (h3 : W3_all) (h4 : W4_all) : W9_columnRoutes := by
  obtain ⟨-, -, -, -, hcmp, -, hsub, -, -, hshl, -, hsplit, -⟩ := h3
  obtain ⟨-, hF, hR, -⟩ := h4
  exact W9_columnRoutes_holds hF hR hshl hsplit hsub hcmp

/-- Q6 from `W3_all` and `W4_all`. -/
theorem W9_postOutput_of_all (h3 : W3_all) (h4 : W4_all) : W9_postOutput := by
  obtain ⟨-, -, -, -, hcmp, -, hsub, -, -, hshl, -, hsplit, -⟩ := h3
  exact W9_postOutput_holds h4.1 hshl hsplit hsub hcmp

/-- **W9e**: the POST routing phases Q2, Q3+Q4 and Q6 from the frozen W3 and W4 contracts. -/
theorem W9e_holds (h3 : W3_all) (h4 : W4_all) :
    W9_postTranspose ∧ W9_columnRoutes ∧ W9_postOutput :=
  ⟨W9_postTranspose_of_all h4, W9_columnRoutes_of_all h3 h4, W9_postOutput_of_all h3 h4⟩

#assert_std_axioms W9_postTranspose_of_all W9_columnRoutes_of_all W9_postOutput_of_all W9e_holds

end WP.W9e
