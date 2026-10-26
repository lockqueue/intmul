import IntMulTM.Gate
import IntMulTM.Exec.TopRun
import IntMulTM.Exec.NativeTop

/-!
# IntMulTM.Exec.Gate — G1 gate over the execution layer

The final execution test runs `IntMulTM.Exec.TopRun.topP`, built from the concrete stage programs. This gate
checks every constant of every project module in its import cone, by module prefix, plus the dependency
cone of the run's definitions: no `sorry`, no `native_decide`/`ofReduceBool`, no `implemented_by`/`extern`, and
axioms within `propext`, `Quot.sound`, `Classical.choice`.
-/

#intmul_gate_modules IntMulTM
#intmul_gate_modules WP
#intmul_gate_modules Contracts
#intmul_gate_modules LevelSync

#intmul_gate_check [IntMulTM.Exec.TopRun.topP, IntMulTM.Exec.TopRun.σ0, IntMulTM.Exec.TopRun.runTopIx,
  IntMulTM.Exec.TopRun.accepted, IntMulTM.Exec.TopRun.ix, IntMulTM.Exec.TopRun.hm9,
  IntMulTM.Exec.TopRun.nrTop_eq, main]
