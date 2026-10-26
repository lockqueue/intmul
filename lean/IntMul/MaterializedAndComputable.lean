import IntMul.MaterializedAndComputable.WordWidthBounds
import IntMul.MaterializedAndComputable.PaperStopAndRadix2Leaf
import IntMul.MaterializedAndComputable.MaterializedArrays
import IntMul.MaterializedAndComputable.SequentialTransducers
import IntMul.MaterializedAndComputable.MaterializedPipeline
import IntMul.MaterializedAndComputable.ComputablePrimitives
import IntMul.MaterializedAndComputable.ComputableExactSolvers
import IntMul.MaterializedAndComputable.ComputableExactPipeline
import IntMul.MaterializedAndComputable.ProgramCostPrimitives
import IntMul.MaterializedAndComputable.PaperHeadlinePipeline
import IntMul.MaterializedAndComputable.FaithfulTablesPerturbation
import IntMul.MaterializedAndComputable.ComputableTranscendentals
import IntMul.MaterializedAndComputable.ComputableTableBuilder
import IntMul.MaterializedAndComputable.CallSiteWidthSoundness

/-!
# Umbrella Module for `IntMul/MaterializedAndComputable/` (Materialized, Pure-Integer & Program-Costed `[MS]` Multiplier Pipeline)

Re-exports all 14 modular files under `IntMul/MaterializedAndComputable/`:
1. `IntMul.MaterializedAndComputable.WordWidthBounds` (word-width & dynamic-range invariants; cf. `[MS]` §§3.2, 5.2, 6.2; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
2. `IntMul.MaterializedAndComputable.PaperStopAndRadix2Leaf` (adaptive stopping rule & `BaseRadix2FFT` leaves; cf. `[MS]` §§6.3, 7.1–7.2; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
3. `IntMul.MaterializedAndComputable.MaterializedArrays` (materialized 1D/2D array primitives; cf. `[MS]` §§3.5, 5.2, 6.2; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
4. `IntMul.MaterializedAndComputable.SequentialTransducers` (sequential multitape array transducers; cf. `[MS]` §§3.2, 3.4, Lemma 3.3; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
5. `IntMul.MaterializedAndComputable.MaterializedPipeline` (end-to-end materialized `FastDFT` & multiplier; cf. `[MS]` §7; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
6. `IntMul.MaterializedAndComputable.ComputablePrimitives` (computable `ℤ × ℤ` fixed-point primitives & spread; cf. `[MS]` §§3.2, 3.5, 6.2; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
7. `IntMul.MaterializedAndComputable.ComputableExactSolvers` (computable `ℤ × ℤ` bidiagonal & Nyquist solvers; cf. `[MS]` §5.2; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
8. `IntMul.MaterializedAndComputable.ComputableExactPipeline` (intermediate `ℤ × ℤ` pipeline & table-perturbation bounds; cf. `[MS]` §§3.3, 7; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
9. `IntMul.MaterializedAndComputable.ProgramCostPrimitives` (`BitCostM` cost interface & program-costed subroutines; cf. `[MS]` §§3.2, 5.2, 6.2, 7; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
10. `IntMul.MaterializedAndComputable.PaperHeadlinePipeline` (paper-stop `BaseRadix2FFT` computable pipeline; cf. `[MS]` §7; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
11. `IntMul.MaterializedAndComputable.FaithfulTablesPerturbation` (perturbation-tolerant `TablesFaithful` closure; cf. `[MS]` §§3.3, 6.3, 7; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
12. `IntMul.MaterializedAndComputable.ComputableTranscendentals` (computable fixed-point series evaluators; cf. `[MS]` §3.3, Lemma 3.2, App. A.1; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
13. `IntMul.MaterializedAndComputable.ComputableTableBuilder` (computable costed table builder; cf. `[MS]` §3.3, Lemma 3.2, eq. (8); executable spec of earlier `[MS]` draft omitted in current `[MS]`)
14. `IntMul.MaterializedAndComputable.CallSiteWidthSoundness` (per-call-site operand width soundness & headline theorem; cf. `[MS]` §§3.2, 7.2, Theorem 1; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
-/
