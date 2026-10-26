import IntMulTM.Gate
import IntMulTM.Headline

/-!
# G1 gate for the headline

Checks the full dependency cone of `IntMulTM.intMul_TM2_nlogn`, and every constant of every
project module family in that cone (the framework `TMFw` namespace lives in the `IntMulTM.Framework.*` modules): no `sorry`, no axioms beyond `propext`, `Quot.sound`,
`Classical.choice`, no `implemented_by` / `extern` / `unsafe` project code.
-/

#intmul_gate_check [IntMulTM.intMul_TM2_nlogn]
#intmul_gate_modules IntMulTM
#intmul_gate_modules Contracts
#intmul_gate_modules LevelSync
#intmul_gate_modules WP
