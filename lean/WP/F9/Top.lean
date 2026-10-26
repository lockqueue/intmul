import WP.F9.Pipe
import WP.W9gx.Concrete
import WP.W9sp.Concrete
import WP.W9sq.Concrete
import WP.W9ex.Concrete
import WP.W9h.Concrete
import WP.W9s.Concrete
import WP.W9d.Concrete
import WP.W9cS.Concrete
import WP.W9c.Concrete
import WP.W9f.Concrete

/-!
# WP.F9.Top — the concrete W9 multiplier `P9C` (for `topProgC`)

`WP.F9.Top.P9C : Prog (BLoc m9) (fun _ => Sym) R9` is the `W9_multiply` program, assembled by
`P9of` (WP.F9.Pipe, i.e. the witnesses of `W9_multiply_of_parts_holds` over
`W9_pipeline_of_levels_holds` …). It uses `hm9 : m9 ≤ w9Scratch` and the initial registers
`r9 : R9`.

**Version 1.** The root and leaf kernels are concrete:
* splitPack: `WP.W9sp.Concrete`;
* square: `WP.W9sq.Concrete`;
* extract: `WP.W9ex.Concrete`;
* reconstruct: `WP.W9h.Concrete`;
* leaf FFT: `WP.W9gx.Concrete`.

So are the node phases:
* P1, P2, P8: `WP.W9b.Concrete`;
* P4, P7: `WP.W9d.Concrete`;
* P5: `WP.W9s.Concrete`;
* P3: the spread driver `WP.W9cS.Concrete.progC` with the spread row `WP.W9c.Concrete.progC`;
* Q2, Q3+Q4, Q6: W9e.

* Q5: the columns stage `WP.W9f.Concrete.progColsC`.

**No placeholders remain (version 3).** The W9f column solver keeps function-valued registers, so a
run must use `runTabledIxR` with the register normalizer `nr9` (proved the identity, `nr9_eq`).
WP.F9.MulLeafRun checks `P9C` on leaf-only chains and WP.F9.StepMulRun on a step-level chain
(every node kernel), against `W9_multiply`'s post-state and `A·B`.
-/

namespace WP.F9.Top

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9

/-- The assembled multiplier (version 3: every kernel concrete). -/
def P9v0 := P9of (WP.W9cS.Concrete.progC WP.W9c.Concrete.progC) WP.W9d.Concrete.Pre.progC
  WP.W9s.Concrete.progC
  WP.W9d.Concrete.Post.progC WP.W9f.Concrete.progColsC WP.W9gx.Concrete.progC WP.W9sp.Concrete.progC
  WP.W9sq.Concrete.progC WP.W9ex.Concrete.progC WP.W9h.Concrete.progC

/-- Scratch count of a W9 stage program. -/
def mOf {m : ℕ} {σ : Type} (_ : Prog (BLoc m) (fun _ => Sym) σ) : ℕ := m

/-- Register type of a W9 stage program. -/
def ROf {m : ℕ} {σ : Type} (_ : Prog (BLoc m) (fun _ => Sym) σ) : Type := σ

/-- Scratch count of `P9C`. -/
abbrev m9 : ℕ := mOf P9v0

/-- Registers of `P9C`. -/
abbrev R9 : Type := ROf P9v0

/-- **The concrete W9 multiplier** (`W9_multiply`'s program). -/
def P9C : Prog (BLoc m9) (fun _ => Sym) R9 := P9v0

/-- Its initial registers. -/
def r9 : R9 :=
  P9r0of (WP.W9cS.Concrete.r0C WP.W9c.Concrete.r0C) WP.W9d.Concrete.Pre.r0C WP.W9s.Concrete.r0C
    WP.W9d.Concrete.Post.r0C WP.W9f.Concrete.r0ColsC WP.W9gx.Concrete.r0C WP.W9sp.Concrete.r0C
    WP.W9sq.Concrete.r0C
    WP.W9ex.Concrete.r0C WP.W9h.Concrete.r0C

/-- `P9C` fits the W9 scratch cap. -/
theorem hm9 : m9 ≤ w9Scratch := by decide

/-- `m9 = 64`. -/
theorem m9_eq : m9 = 64 := by decide

/-- `P9C` is closed (every kernel's `closedC`, assembled by WP.F9.Assemble's closedness lemmas). -/
theorem closedC : P9C.Closed :=
  multA_closed (pipeA_closed (preLevelA_closed (preNodeA_closed WP.W9b.Concrete.P1.closedC
      WP.W9b.Concrete.P2.closedC (WP.W9cS.Concrete.closedC WP.W9c.Concrete.closedC)
      WP.W9d.Concrete.Pre.closedC WP.W9s.Concrete.closedC WP.W9d.Concrete.Post.closedC
      WP.W9b.Concrete.P8.closedC))
    (leafLevelA_closed WP.W9gx.Concrete.closedC)
    (postLevelA_closed (postNodeA_closed WP.W9e.Concrete.Q2.closedC WP.W9e.Concrete.Q34.closedC
      WP.W9f.Concrete.closedColsC WP.W9e.Concrete.Q6.closedC)))
    WP.W9sp.Concrete.closedC WP.W9sq.Concrete.closedC WP.W9ex.Concrete.closedC
    WP.W9h.Concrete.closedC

/-- The register normalizer for runs (`runTabledIxR`): W9f's column registers rebuilt from data. -/
def nr9 : R9 → R9 := nrPost WP.W9f.Concrete.normColsC

theorem nr9_eq : ∀ v : R9, nr9 v = v := nrPost_eq _ WP.W9f.Concrete.normColsC_eq

#assert_std_axioms hm9 m9_eq closedC nr9_eq

end WP.F9.Top
