import IntMulTM.Gate
import IntMulTM.Spec
import IntMulTM.SpecFacts
import IntMulTM.Framework.Accept
import IntMulTM.Framework.Test.EndToEnd
import IntMulTM.Framework.Test.Mutation
import IntMulTM.Framework.Test.Nested
import Contracts.Machine.W3
import Contracts.Machine.W4
import Contracts.Machine.W5
import Contracts.Machine.W6a
import Contracts.W8
import Contracts.W6
import LevelSync.Pure
import LevelSync.Iter
import LevelSync.Sizes

/-!
# G1 integration gate for the merged project (Phase C state)

Checks every constant of every project module family that is merged so far, plus the cones of the key
exported results. Fails the build on `sorry`, compiler-trusting axioms, any axiom beyond `propext`,
`Quot.sound`, `Classical.choice`, and on `implemented_by` / `extern` / `unsafe` project code.
(The `sorry`'d headline scaffold `IntMulTM.SpecScratch` was deleted once the proof landed.)
-/

#intmul_gate_modules IntMulTM
#intmul_gate_modules Contracts
#intmul_gate_modules LevelSync

#intmul_gate_check [IntMulTM.input_bridge, IntMulTM.decodeNatPair_encodeNatPair,
  TMFw.acceptance_of_triple, TMFw.sim,
  IntMulTM.Contracts.W8_machineInterface_holds, IntMulTM.Contracts.W8_divRoundBarrett_exact_holds,
  IntMulTM.Contracts.W8_columnSolve_callSite_holds,
  IntMul.LevelSync.levelEval_eq_map, IntMul.LevelSync.levelEvalV_eq_map, IntMul.LevelSync.runIter_eq_map]
