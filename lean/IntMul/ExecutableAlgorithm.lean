import IntMul.ExecutableAlgorithm.ChunkingAndSyntheticFFT
import IntMul.ExecutableAlgorithm.IdealizedFastDFT
import IntMul.ExecutableAlgorithm.QuantizedSubstepBridges
import IntMul.ExecutableAlgorithm.QuantizedFastDFT
import IntMul.ExecutableAlgorithm.IntrinsicScheduleAndCost
import IntMul.ExecutableAlgorithm.UnconditionalComplexity

/-!
# Umbrella Module for `IntMul/ExecutableAlgorithm/` (Executable Reference & Intrinsic-Cost Pipeline)

Re-exports all 6 modular files under `IntMul/ExecutableAlgorithm/`:
1. `IntMul.ExecutableAlgorithm.ChunkingAndSyntheticFFT` (chunking, ring butterflies & executable tests; cf. `[MS]` §§3.5, 6.2, 7.1; Python spec of earlier `[MS]` draft omitted in current `[MS]`)
2. `IntMul.ExecutableAlgorithm.IdealizedFastDFT` (exact-arithmetic recursive `fastDFT` / `fastIDFT` & root packing; cf. `[MS]` §§3.5, 4–5, 7.1; Python spec of earlier `[MS]` draft omitted in current `[MS]`)
3. `IntMul.ExecutableAlgorithm.QuantizedSubstepBridges` (quantized overlap-add spread & substep error bridges; cf. `[MS]` §§5.1, 6.2–6.3; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
4. `IntMul.ExecutableAlgorithm.QuantizedFastDFT` (multi-level quantized `FastDFT`, routing & exact recovery; cf. `[MS]` §§3.4, 6.3, 7; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
5. `IntMul.ExecutableAlgorithm.IntrinsicScheduleAndCost` (schedule builder & intrinsic bit-cost model; cf. `[MS]` §§3.3–3.4, 6.2–6.3, 7; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
6. `IntMul.ExecutableAlgorithm.UnconditionalComplexity` (parameter-free `O(n log n)` bit-complexity bound; cf. `[MS]` §7.2, Theorem 1; executable spec of earlier `[MS]` draft omitted in current `[MS]`)
-/
