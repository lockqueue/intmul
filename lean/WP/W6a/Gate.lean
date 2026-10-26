import WP.W6a.DivRound
import WP.W6a.Smoke
import IntMulTM.Gate

/-!
# WP.W6a.Gate — G1 trust gate for the W6a work package

* Module mode: every constant of every `WP.W6a.*` module.
* Declaration mode: the cones of the main theorems.

`W6a_divModNat_holds` and `W6a_divRound_holds` take `W3_subNat` as an explicit hypothesis.
-/

#intmul_gate_modules WP.W6a

#intmul_gate_check [WP.W6a.W6a_divModNat_holds, WP.W6a.W6a_divRound_holds, WP.W6a.W6a_holds]
