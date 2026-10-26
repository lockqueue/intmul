/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.TopExtended
import SubNLogN.Assembly.Cut
import SubNLogN.Assembly.KernelCut
import SubNLogN.Assembly.KernelCutFinal
import SubNLogN.Assembly.KernelCutFinal

/-!
# The kernel-level cut obligation and the TM2 headline theorems

This leaf module discharges the top-level kernel cut obligation (`SubNLogN.Assembly.KernelCut7`). It is PROVED with
0 `sorry`: `kernelCut7_holds : SubNLogN.Assembly.KernelCut7` is `SubNLogN.Assembly.kernelCut7_proved`, from which `w9SubNLogNSpecX_holds : W9SubNLogNSpecX` (the Stage-5
multiplier with extra work stacks and headline-shaped cost; see `S5/TopExtended.lean` and
`Section 8` of the paper) and the four headline theorems below follow (`headline_46_of_w9X`,
`intMulSubNLogN_mono`, `intMulSubNLogN_46_implies_littleO`). Axioms: Lean's standard three only.
-/

namespace SubNLogN.S5

open SubNLogN Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts

/-! ## Kernel-level cut discharge and the headline theorems -/

/-- **PROVED — top-level kernel cut (`SubNLogN.Assembly.KernelCut7`).** All fields of the kernel-level cut are
proved: `SubNLogN.Assembly.kernelCut7_proved` (0 `sorry`). The fields of the earlier cuts (tables, c6, spreadLines, solveAxis, readParams,
preScale, reorder, guard, conversions, widths, cost) are proved and supplied inside the reductions. -/
theorem kernelCut7_holds : SubNLogN.Assembly.KernelCut7 :=
  SubNLogN.Assembly.kernelCut7_proved

/-- The kernel-level cut `KernelCutStmt` (0 `sorry`). -/
theorem kernelCut_holds : SubNLogN.Assembly.KernelCutStmt :=
  SubNLogN.Assembly.kernelCutStmt_of_7 kernelCut7_holds

/-- The bridge-branch cut `WalshBranchCut`, from the kernel-level cut (0 further `sorry`). -/
theorem walshBranchCut_holds : SubNLogN.Assembly.WalshBranchCut :=
  SubNLogN.Assembly.walshBranchCut_of_kernelCut kernelCut_holds

/-- The Stage-5 contract with extra work stacks, from the kernel-level cut (0 further `sorry`). -/
theorem w9SubNLogNSpecX_holds : W9SubNLogNSpecX :=
  SubNLogN.Assembly.w9X_of_kernelCut kernelCut_holds

/-- **Primary `TM2` theorem (`κ = 2^{-46}`, `Theorem 1` / `Theorem 2`, `Table 6`):**
`headline_46_of_w9X` applied to `w9SubNLogNSpecX_holds`; proved with 0 `sorry` (standard axioms
only), as are the three below. -/
theorem headline_TM2_subNLogN_46 : Headline_TM2_SubNLogN_46 :=
  headline_46_of_w9X w9SubNLogNSpecX_holds

/-- **Headline 2 (`κ = 2^{-47}`, `Theorem 2` / `Remark 7.3`, `Table 10`):**
Follows from `headline_TM2_subNLogN_46` by `intMulSubNLogN_mono`. -/
theorem headline_TM2_subNLogN_47 : Headline_TM2_SubNLogN_47 :=
  intMulSubNLogN_mono (by decide : 46 ≤ 47) headline_TM2_subNLogN_46

/-- **Headline 3 (`κ = 2^{-56}`, `Theorem 2` / `Remark 7.3`, `Table 10`):**
Follows from `headline_TM2_subNLogN_46` by `intMulSubNLogN_mono`. -/
theorem headline_TM2_subNLogN_56 : Headline_TM2_SubNLogN_56 :=
  intMulSubNLogN_mono (by decide : 46 ≤ 56) headline_TM2_subNLogN_46

/-- **Headline 4 (`o(n log n)`):**
Follows from `headline_TM2_subNLogN_46` by `intMulSubNLogN_46_implies_littleO`. -/
theorem headline_TM2_littleO_nlogn : Headline_TM2_LittleO_NLogN :=
  intMulSubNLogN_46_implies_littleO headline_TM2_subNLogN_46

end SubNLogN.S5
