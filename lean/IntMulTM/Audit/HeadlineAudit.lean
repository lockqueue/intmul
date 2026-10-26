import IntMulTM.Headline
import IntMulTM.Audit.Cone

/-!
# Reports on the headline theorem

Read-only reports, regenerated on every build of this file (commands: `IntMulTM.Audit.Cone`).

1. `#intmul_statement_boundary IntMulTM.IntMulNLogN` lists the definitions that fix what the
   headline's statement says. It fails if any of them comes from project code other than
   `IntMulTM.Spec`, so the statement provably does not depend on the vendored snapshot or on any
   other project definition.
2. `#intmul_cone_report IntMulTM.intMul_TM2_nlogn […]` describes the dependency cone of the
   headline's *proof*: how much of the vendored snapshot it reaches, which of the snapshot's sealed
   cost primitives occur, and where the queried constants occur.

This file imports only the headline and the report commands. A query reported as "not in this
environment" is therefore not even in the headline's import closure.

3. Frozen facts (each fails the build if it stops being true):
   * the snapshot's own cost theorem is *not* in the proof's cone, so the time bound is not
     derived from the snapshot's bit-cost model;
   * the snapshot's cost layer *is* in the cone, because the machine contracts use the snapshot's
     costed functions as value specifications. There it enters only as ordinary kernel-checked
     definitions and lemmas, never as an assumption;
   * the concrete executable programs (`WP.F9.Top.P9C`, its placeholder `holeB`, and the exec
     layer's `topProgC` and `topP`) are outside the headline's import closure.
-/

#intmul_statement_boundary IntMulTM.IntMulNLogN

#intmul_cone_report IntMulTM.intMul_TM2_nlogn [IntMul.AllCallSitesWidthSound,
  IntMul.computablePaperMultiplyOfBitLength_correct_and_isBigO, IntMul.BitCostM,
  IntMul.BitCostM.tick, IntMul.costedExtractRootSlot, IntMul.addBitCost,
  IntMul.computableMulBitCost, IntMul.read1D, IntMul.RecurrenceCallSitesWidthSound,
  IntMul.SincGaussianTapWidthSound, P9C, holeB, topProgC, topP]

#intmul_cone_excludes IntMulTM.intMul_TM2_nlogn
  [IntMul.computablePaperMultiplyOfBitLength_correct_and_isBigO]

#intmul_cone_includes IntMulTM.intMul_TM2_nlogn [IntMul.AllCallSitesWidthSound, IntMul.BitCostM,
  IntMul.costedExtractRootSlot, IntMul.addBitCost, IntMul.computableMulBitCost, IntMul.read1D]

#intmul_not_imported [P9C, holeB, topProgC, topP]
