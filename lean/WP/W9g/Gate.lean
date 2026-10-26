import WP.W9g.Top
import IntMulTM.Gate

/-!
# WP.W9g.Gate — G1 trust gate for the W9g work package

* Module mode: every constant of every `WP.W9g.*` module.
* Declaration mode: the cones of the main theorems: the LEAF kernel on the machine stacks
  (`leaf_rs`, with `leafProg_closed`) and the recursive FFT (`fft_rs`).

`leaf_rs` takes the contract programs as a `Prims` bundle with `X.OK Mul CM CA CS CL CR`, i.e. the
`W5_mulAt Mul`, `W3_addInt`, `W3_subInt`, `W3_shlVar`, `W3_shrVar` bodies (`prims_of`), as hypotheses
(discharged at assembly). The `BContract` statement `W9_leafFFT_holds` is assembled in `WP.W9gx`.
-/

#intmul_gate_modules WP.W9g

#intmul_gate_check [WP.W9g.leaf_rs, WP.W9g.leafProg_closed, WP.W9g.fft_rs, WP.W9g.prims_of]
