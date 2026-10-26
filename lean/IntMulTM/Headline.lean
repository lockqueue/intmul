import IntMulTM.Current15
import WP.W7k3c.Final

/-!
# The headline theorem: integer multiplication in O(n log n) on a multitape Turing machine

`IntMulTM.IntMulNLogN` is the top-level specification statement defined in
`IntMulTM.Spec`. This module proves it unconditionally with no hypotheses.

Proof chain (`IntMulTM.Current5`–`Current15` and
`WP.Top.Current3`–`Current6`): the Top composition (input stage W0m, table builder W7, table-tape
converter, the level-synchronous multiplier W9, output stage) is instantiated with every stage and
kernel contract proved on the machine:
* W3 (all 25 integer-arithmetic contracts), W4 (transpose, odd-stride factor, odd routing),
  W5 (Toom-3 multiplication), W6a (long division);
* W7: integer sqrt, π, ln 2, the series sub-kernel, stdChar, sinc-Gaussian tap, c0/c1,
  and the table builder `W7_buildTablesRef`;
* W9: every PRE/LEAF/POST phase kernel, the level programs and pipeline, and the root stages;
* W10/W10b (cost), W11b (width profiles and `W9RootOK`), W12 (assembly).
-/

namespace IntMulTM

/-- **Headline.** Integer multiplication is computable in time `O(n log n)` by a finite
multitape Turing machine (Mathlib `Turing.TM2`, packaged as `FinTM2`), in the exact sense of
`IntMulTM.IntMulNLogN`. -/
theorem intMul_TM2_nlogn : IntMulNLogN :=
  Final.intMul_TM2_nlogn_current15 WP.W7k3c.W7_c0c1_bind

#assert_std_axioms intMul_TM2_nlogn

#print axioms intMul_TM2_nlogn

end IntMulTM
