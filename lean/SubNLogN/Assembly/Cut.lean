import SubNLogN.Assembly.Pending
import SubNLogN.Math.Bridge.Proofs.Wiring

/-!
# Assembly: the bridge-branch reduction cut below `W9SubNLogNSpecX`

`WalshBranchCut` packages the machine-level bridge-branch obligation below the extended top-level
specification `W9SubNLogNSpecX` (`S5/TopExtended.lean`), and `w9X_of_cut : WalshBranchCut →
W9SubNLogNSpecX` is the reduction (0 `sorry`); `WalshBranchCut` itself is discharged downstream in
`Assembly/KernelCutFinal.lean` (Section 8, `sec:lean`).

Everything around the cut is proved (0 `sorry`, standard axioms):
* the transform: `F_newConcreteK Kc row46 = F_newKR roundHalfUpR Kc row46
  (TabConcreteR roundHalfUpR row46) (walshMid row46)` (`Math/Bridge/Fnew.lean`, `FnewFinal.lean`):
  the bridge of Section 4 (`sec:bridge`, round-half-up roundings, input guard) with the concrete certified
  tables and the Walsh middle of Sections 5–6 (`sec:walsh`, `sec:direct-fft`) when `WalshOK row46 p0 K0` and
  `Kc ≤ K0`, IntMul's radix-2 transform otherwise;
* exact recovery and the root invariant for every input (`rootOKAll_F_newKR`, `RootOK.lean`) from
  Theorem 4.7 (`thm:bridge-precision`, `Wired.bridge_precision`), Proposition 7.2 (`prop:root-packing`, `rootW8_Fnew_of`), the table
  certification (`tabConcrete_certified`, at `roundHalfUpR`), Theorem 6.5 / Corollary 6.6 (`direct_fft`,
  `middle_walshMid`), and the `ChainOK` packaging;
* the dispatch to the proved radix-2 pipe below the cutoff and the cutoff choice
  (`exists_pipeFnewX`, `Kstar_spec`, `walshOK_eventually_holds`, `exists_w8K_threshold`);
* the cost: `headlineCost_walshNat46_W8` (Theorem 1 (`thm:main`) cost bound at the W8 parameters) inside
  `w9X_of_parts` / `w9X_of_pipeX` (root composite, proved root kernels).

What `WalshBranchCut` asserts (the machine implementation of the bridge branch): there are a
threshold `N` and a step bound `Tw` such that a closed pipe program on `BLoc mw ⊕ Ew` (`mw ≤ 64`,
finite extra-stack type `Ew`, finite nonempty registers) computes
`FnewOfR roundHalfUpR row46 (TabConcreteR roundHalfUpR row46) (walshMid row46)` on every pipe input
with `N ≤ n`
(`WalshBranchFromStmt`, `Machine/Pipe/Contract.lean`), and `Tw` satisfies the Walsh-route cost clause
(`WalshCostClause`: `Tw n cSpec ≤ C · walshCostNatW8 row46 λ' τ m D_set n + C · (|tapeSyms cSpec| + 1)`
for all large `n`, with `m` a polylogarithmic multiplication-cost envelope).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Math.Cost SubNLogN.Math.Bridge

/-- **The bridge-branch reduction interface (`WalshBranchCut`).** For some threshold `N` and step
bound `Tw`, the bridge branch `FnewOfR roundHalfUpR row46 (TabConcreteR roundHalfUpR row46)
(walshMid row46)` has a closed pipe
machine on every pipe input with `N ≤ n` (`WalshBranchFromStmt`) whose step bound satisfies the
Walsh-route cost clause (`WalshCostClause`). This corresponds to the `walshBranch` field of
`PendingContracts` (discharged unconditionally in `Assembly/KernelCutFinal.lean`). -/
def WalshBranchCut : Prop :=
  ∃ (N : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
    SubNLogN.Machine.Pipe.WalshBranchFromStmt
      (FnewOfR SubNLogN.Math.Common.roundHalfUpR row46
        (TabConcreteR SubNLogN.Math.Common.roundHalfUpR row46) (walshMid row46)) N Tw ∧
    SubNLogN.Machine.Pipe.WalshCostClause Tw

/-- **`W9SubNLogNSpecX` from the cut (`w9X_of_cut`, 0 `sorry`):** `w9X_of_contracts` with the
`bridgePrecision` field supplied by Theorem 4.7 (`thm:bridge-precision`, `Wired.bridge_precision`). -/
theorem w9X_of_cut (h : WalshBranchCut) : W9SubNLogNSpecX :=
  w9X_of_contracts ⟨Wired.bridge_precision, h⟩

end SubNLogN.Assembly
