import WP.W9ex.Main
import WP.W9ex.Value
import Contracts.W9.Pipeline

/-!
# WP.W9ex.Extract — **`W9_extract` (root phase R5), proved**

The program is `extractProg` over `BLoc 4` (4 scratch stacks ≤ `w9Scratch`), registers
`Option Sym`, cost constant `C = 64`. No machine-contract hypotheses are needed: the kernel uses
only framework macros (`moveBits`, `copyBlock`, `inc`, `dec`, `zeroTest`) and the macros proved in
`WP.W9ex.Macros`. `W9_extract_holds` / `W9_extract_binding` are the integrator's binding shapes.
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-- **W9.extract (R5)**, proved outright. -/
theorem W9_extract_proved : W9_extract := by
  refine ⟨64, fun _ => ⟨4, Option Sym, extractProg, by decide, inferInstance, ⟨none⟩,
    extractProg_closed, ?_⟩⟩
  intro b K0 k1 k2 wR v σ restS r0 hv hk hw hC0 hS
  have h := xt_extract σ b K0 k1 k2 wR v restS r0 hv hk hw hC0 hS
  rw [← rootDigits_eq_mdig b K0 k1 k2 v hv hk] at h
  exact h.runs

/-- `W3_all`-parameterized binding form of `W9_extract_proved`. -/
theorem W9_extract_holds : W3_all → W9_extract := fun _ => W9_extract_proved

/-- Binding shape of `WP.W9comp.W9StageThms.extract`. -/
theorem W9_extract_binding : W3_all → W4_all → W6a_all → W9_extract := fun _ _ _ =>
  W9_extract_proved

#assert_std_axioms W9_extract_proved W9_extract_holds W9_extract_binding

end WP.W9ex
