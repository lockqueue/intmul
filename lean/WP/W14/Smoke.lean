import WP.W14.Headline
import IntMul.MaterializedAndComputable.ComputableTableBuilder
import IntMul.MaterializedAndComputable.CallSiteWidthSoundness

/-!
# W14 smoke tests (`#eval`)

W14 adds no Turing-machine program; its executable artefact is the schedule-parametric integer
pipeline `computablePaperFastDFTMultiplyAt`. These evaluations run it on tiny inputs.

* Paper leaf grid: for small `n` the paper recursion `paperSpec n` is a single radix-2 leaf. The leaf
  twiddles are built computably at the paper's grid `q_leaf = p + K + 2` with the snapshot's
  `computableStdCharWithProgramCost` (CTB:94–106 with `q_leaf` a parameter). `n = 16` is the case
  `b ∣ n` where the snapshot's limb count `n/b + 1` would violate `k1 + k2 ≤ 2^K0` at the paper's `K0`.
* Snapshot schedule: the parametric pipeline at `snapshotQLeaf` on the snapshot's two-level `.step`
  smoke spec with the snapshot's computable tables (CSWS:2487).
-/

namespace WP.W14

open IntMul

/-- Computable leaf twiddle tables at an explicit grid (CTB:94–106 with `q_leaf` a parameter). -/
def leafTablesAt (q_leaf p K : ℕ) : ComputablePaperFastDFTSpec :=
  .basePow2 p K (Array.ofFn (fun s : Fin K =>
    (runSequentialScanCostedSteps
      (fun u => computableStdCharWithProgramCost q_leaf u (2 ^ (s.val + 1)) false)
      (2 ^ (s.val + 1))).1))

/-- The paper multiplier with computable leaf tables (meaningful when `paperSpec n` is a leaf). -/
def paperLeafMultiply (n A B : ℕ) : ℕ :=
  let R := paperRoot n
  let p0 := rootPrecision R.b R.K0
  computablePaperFastDFTMultiplyAt paperSchedule.qLeaf
    (leafTablesAt (paperSchedule.qLeaf p0 R.K0) p0 R.K0) R.b R.K0 R.k R.k A B

/-- info: (4, 4, 3, 20, true) -/
#guard_msgs in
#eval let R := paperRoot 16
  (R.b, R.k, R.K0, rootPrecision R.b R.K0, decide (2 ^ R.K0 ≤ 4 * (rootPrecision R.b R.K0) ^ 2))

/-- info: true -/
#guard_msgs in
#eval paperLeafMultiply 16 40000 50000 == 40000 * 50000

/-- info: true -/
#guard_msgs in
#eval paperLeafMultiply 64 (2 ^ 64 - 1) (2 ^ 63 + 12345) == (2 ^ 64 - 1) * (2 ^ 63 + 12345)

/-- info: true -/
#guard_msgs in
#eval computablePaperFastDFTMultiplyAt snapshotQLeaf
  (buildComputablePaperTablesWithProgramCost computableStepSmokeSpec).1 1 2 2 2 2 3 == 6

end WP.W14
