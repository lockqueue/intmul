/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutHolds
import SubNLogN.Machine.FFT.LayoutMapUHolds

/-!
# K4.3 (`Machine/FFT/LayoutFinal.lean`): the layout compiler and the layout execution, for both maps

**Scope (honest summary).**
* `layoutCompile_holds (sel) : LayoutCompileStmt sel`: proved, no hypothesis
  (`layoutCompile_of_mapU` with `layoutMapGen_U_holds`, `Machine/FFT/LayoutMapUHolds.lean`).
* `layoutExec_holds_of_posPerm (hPP : PositionalPermMachineStmt Band lam') (sel) :
  LayoutExecStmt Band lam' sel`: the positional-permutation machine (Theorem 5.8, reduced by
  K3-PERM) is the only remaining input.
No `sorry`.
-/

namespace SubNLogN.Machine

/-- **The layout compiler**, both maps, proved. -/
theorem layoutCompile_holds (sel : LayoutSel) : LayoutCompileStmt sel :=
  layoutCompile_of_mapU layoutMapGen_U_holds sel

/-- **The layout maps executed** (`L` or `U`), from the positional-permutation machine. -/
theorem layoutExec_holds_of_posPerm {Band : LayerRT → Prop} {lam' : ℝ}
    (hPP : PositionalPermMachineStmt Band lam') (sel : LayoutSel) : LayoutExecStmt Band lam' sel :=
  layoutExec_of_posPerm_mapU hPP layoutMapGen_U_holds sel

end SubNLogN.Machine
