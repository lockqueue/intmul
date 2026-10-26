/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutMapLHolds

/-!
# K4.3 (`Machine/FFT/LayoutHolds.lean`): the layout compiler and the layout execution, assembled

**Scope (honest summary).**
* `layoutCompile_L_holds : LayoutCompileStmt .L`: proved, no hypothesis
  (`layoutCompile_of_parts` with `permHdrGen_holds` and `layoutMapGen_L_holds`).
* `layoutCompile_of_mapU (hU : LayoutMapGenStmt .U) (sel) : LayoutCompileStmt sel`: the map of `U`
  (`LayoutMapGenStmt .U`, proved in `LayoutMapUHolds.lean`) is the only remaining input.
* `layoutExec_L_of_posPerm`, `layoutExec_of_posPerm_mapU`: `LayoutExecStmt Band lam' sel` from
  `PositionalPermMachineStmt Band lam'` (Theorem 5.8, reduced by K3-PERM), and for `sel = .U`
  also `LayoutMapGenStmt .U`.
No `sorry`.
-/

namespace SubNLogN.Machine

open SubNLogN.Math.Walsh

/-- **The layout compiler for `L`**, proved. -/
theorem layoutCompile_L_holds : LayoutCompileStmt .L :=
  layoutCompile_of_parts .L permHdrGen_holds layoutMapGen_L_holds

/-- **The layout compiler for any selector**, from the map of `U`. -/
theorem layoutCompile_of_mapU (hU : LayoutMapGenStmt .U) (sel : LayoutSel) :
    LayoutCompileStmt sel := by
  cases sel
  · exact layoutCompile_L_holds
  · exact layoutCompile_of_parts .U permHdrGen_holds hU

/-- **The layout `L` executed** on the record array, from the positional-permutation machine. -/
theorem layoutExec_L_of_posPerm {Band : LayerRT → Prop} {lam' : ℝ}
    (hPP : PositionalPermMachineStmt Band lam') : LayoutExecStmt Band lam' .L :=
  layoutExec_of_posPerm .L hPP layoutCompile_L_holds

/-- **The layout maps executed** (`L` or `U`), from the positional-permutation machine and the
map of `U`. -/
theorem layoutExec_of_posPerm_mapU {Band : LayerRT → Prop} {lam' : ℝ}
    (hPP : PositionalPermMachineStmt Band lam') (hU : LayoutMapGenStmt .U) (sel : LayoutSel) :
    LayoutExecStmt Band lam' sel :=
  layoutExec_of_posPerm sel hPP (layoutCompile_of_mapU hU sel)

end SubNLogN.Machine
