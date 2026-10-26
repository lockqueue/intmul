import SubNLogN.Assembly.RootOK
import SubNLogN.Machine.Pipe.Contract
import SubNLogN.Math.Bridge.FnewFinal
import SubNLogN.Math.Bridge.Proofs.RootW8
import SubNLogN.Math.Bridge.Proofs.WalshOK
import SubNLogN.Math.Bridge.Proofs.TablesConcrete
import SubNLogN.Math.Walsh.Proofs.Wiring

/-!
# Assembly: the component contracts and `W9SubNLogNSpecX` from them

The top-level specification `W9SubNLogNSpecX` (`S5/TopExtended.lean`) is reduced to a structure of named
contract statements. The transform is `F_newKR roundHalfUpR Kc row46 Tab mid`
(`Math/Bridge/Fnew.lean`): the bridge `FnewOfR roundHalfUpR row46 Tab mid` (round-half-up nearest
rounding, input guard `ArrW (p0 + p_in + 1)`) when `WalshOK row46 p0 K0` and `Kc ≤ K0`, IntMul's
radix-2 transform otherwise; the cutoff `Kc` is chosen inside the proof (from the pipe contract).
`Assembly/Cut.lean` supplies the `bridgePrecision` field below from Theorem 4.7 (`thm:bridge-precision`),
leaving `WalshBranchCut`, which is discharged in `Assembly/KernelCutFinal.lean`.

* `PendingContractsFor Tab mid` (generic in the tables and the middle): fields `rootW8`
  (`RootW8_FnewStmt`), `tables` (`TablesCertStmt Tab`), `middle` (`MiddleStmt mid`), `pipe`
  (`∃ Kc, PipeFnewXStmt Kc Tab mid`); `w9X_of_contractsFor` is the reduction (it uses
  `rootOKAll_F_newKR`, `rootFacts_of_rootW8` of `RootOK.lean` and `w9X_of_parts` of `Top.lean`).
* `PendingContracts` (closed): `Tab = TabConcreteR roundHalfUpR row46`, `mid = walshMid row46`
  (`Math/Bridge/FnewFinal.lean`). Its fields are only
  - `bridgePrecision : Bridge_precisionStmt` (Theorem 4.7 (`thm:bridge-precision`)), and
  - `walshBranch`: a pipe machine computing the bridge branch `FnewOfR roundHalfUpR row46 …` above a
    threshold `N` (`WalshBranchFromStmt`) with the Walsh-route cost (`WalshCostClause`).
  The remaining generic fields are proved here: `rootW8` by `rootW8_Fnew_of` (from `Bridge_precisionStmt` and
  `walshOK_balanced`), `tables` by `tabConcrete_certified` at `roundHalfUpR`, `middle` by `middle_walshMid`
  (Theorem 6.5 (`thm:direct-fft`, `direct_fft`) and Corollary 6.6 (`cor:walsh-middle`, `walsh_middle_ideal_of_direct_fft`)), and `pipe` by
  `exists_pipeFnewX` (dispatch to the proved radix-2 pipe below the threshold).
* `w9X_of_contracts : PendingContracts → W9SubNLogNSpecX`.

Both fields of `PendingContracts` are discharged unconditionally in `Assembly/Cut.lean` and `Assembly/KernelCutFinal.lean`.
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Math.Cost SubNLogN.Math.Bridge SubNLogN.Math.Common
  Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-- **Table certification at every eligible parameter pair (`TablesCertStmt Tab`).** For all
`p0, K0` with `WalshOK row46 p0 K0`, the tables `Tab p0 K0` satisfy `TablesCertifiedR roundHalfUpR`
(Lemma 4.6 (bridge Lemma C)(iii) (`lem:bridge-C`) with round-half-up table roundings,
Lemma B.3 (`lem:phase-tables`)) at `α = alphaDefault (schedOmega p0 K0 d)` (`d` axes) and
working precision `P = schedP p0 K0`; this is the table hypothesis of `RootW8_FnewStmt`. -/
def TablesCertStmt (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape row46 K0)) : Prop :=
  ∀ p0 K0 : ℕ, WalshOK row46 p0 K0 = true →
    TablesCertifiedR roundHalfUpR (alphaDefault (schedOmega p0 K0 (fnewD row46 K0 + 1)))
      (schedP p0 K0) (fnewShape row46 K0) (Tab p0 K0)

/-- **Definition 4.5 middle at every eligible parameter pair (`MiddleStmt mid`).** For all `p0, K0` with
`WalshOK row46 p0 K0`, `mid p0 K0` is a middle transform (`IsMiddleTransform`, Definition 4.5,
`def:middle-contract`) for the shape `fnewShape row46 K0` at working precision
`schedP p0 K0`, for some `E_mid, δ_mid` (Corollary 6.6 gives `E_mid = 12ℓ`, `δ_mid = 0`); this is the
middle hypothesis of `RootW8_FnewStmt`. -/
def MiddleStmt
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape row46 K0) → ℂ) → (Idx (fnewShape row46 K0) → ℂ)) :
    Prop :=
  ∀ p0 K0 : ℕ, WalshOK row46 p0 K0 = true →
    ∃ (Emid : ℝ) (δmid : ℕ), IsMiddleTransform (fnewShape row46 K0) (schedP p0 K0) Emid δmid
      (mid p0 K0)

/-- **The component contracts for given tables and middle (`PendingContractsFor Tab mid`).** -/
structure PendingContractsFor (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape row46 K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape row46 K0) → ℂ) → (Idx (fnewShape row46 K0) → ℂ)) :
    Prop where
  /-- Theorem 4.7 (`thm:bridge-precision`) + Proposition 7.2 (`prop:root-packing`) at the W8 root parameters. -/
  rootW8 : RootW8_FnewStmt
  /-- The tables are certified at every eligible `(p0, K0)` (Lemma 4.6 (bridge Lemma C)(iii)). -/
  tables : TablesCertStmt Tab
  /-- `mid` is a Definition 4.5 (`def:middle-contract`) middle transform at every eligible `(p0, K0)`. -/
  middle : MiddleStmt mid
  /-- For some cutoff `Kc`, the pipe machine for `F_newKR roundHalfUpR Kc row46 Tab mid` with the
  Walsh-route cost. -/
  pipe : ∃ Kc : ℕ, SubNLogN.Machine.Pipe.PipeFnewXStmt Kc Tab mid

/-- `PipeFnewXStmt Kc Tab mid` implies `PipeXCostStmt (F_newKR roundHalfUpR Kc row46 Tab mid)`
(0 `sorry`; a repackaging). -/
theorem pipeXCost_of_pipeFnewX (Kc : ℕ) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape row46 K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape row46 K0) → ℂ) → (Idx (fnewShape row46 K0) → ℂ))
    (h : SubNLogN.Machine.Pipe.PipeFnewXStmt Kc Tab mid) :
    PipeXCostStmt (F_newKR roundHalfUpR Kc row46 Tab mid) := by
  obtain ⟨m1, E, hfE, hdE, R1, Pp, Tp, hm1, hf1, hn1, hcl, hspec, C, m, Am, jm, Dset, N₀, hm,
    hcost⟩ := h
  exact ⟨m1, E, hfE, hdE, R1, Pp, hm1, hf1, hn1, Tp, C, m, Am, jm, Dset, N₀, hcl, hspec, hm, hcost⟩

/-- **`W9SubNLogNSpecX` from `PendingContractsFor` (`w9X_of_contractsFor`).** Take the cutoff `Kc` of
`pipe`; the root invariant of `F_newKR roundHalfUpR Kc row46 Tab mid` for all inputs is
`rootOKAll_F_newKR` with
the bridge branch from `rootFacts_of_rootW8`; pipe and cost come from `pipe` and
`headlineCost_walshNat46_W8` inside `w9X_of_parts`. -/
theorem w9X_of_contractsFor (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape row46 K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape row46 K0) → ℂ) → (Idx (fnewShape row46 K0) → ℂ))
    (h : PendingContractsFor Tab mid) : W9SubNLogNSpecX := by
  obtain ⟨Kc, hP⟩ := h.pipe
  exact w9X_of_parts (F_newKR roundHalfUpR Kc row46 Tab mid)
    (rootOKAll_F_newKR roundHalfUpR row46 Tab mid (fun a b cSpec hj hOK =>
      rootFacts_of_rootW8 h.rootW8 roundHalfUpR isNearestRounding_roundHalfUpR row46 Tab mid
        h.tables h.middle a b cSpec hj hOK) Kc)
    (pipeXCost_of_pipeFnewX Kc Tab mid hP)

/-- **The Walsh middle with the ideal layer is a Definition 4.5 middle at every eligible pair
(`middle_walshMid`, 0 `sorry`):** from Theorem 6.5 (`thm:direct-fft`, `direct_fft`) and Corollary 6.6
(`cor:walsh-middle`, `walsh_middle_ideal_of_direct_fft`), with `E_mid = 12ℓ`, `δ_mid = 0`; the side conditions
(`8 ≤ q`, `1 ≤ D`, `2 ≤ ℓ < q`, `1 ≤ K ≤ ℓ - 1`, axis exponents in `{ℓ-1, ℓ}`) are conjuncts of
`WalshShapeOK`. -/
theorem middle_walshMid : MiddleStmt (walshMid row46) := by
  intro p0 K0 hOK
  obtain ⟨⟨hd2, hl2, -, hK1, hKl, -, -, hq8, hlq⟩, -, -⟩ := (WalshOK_iff row46 p0 K0).1 hOK
  refine ⟨12 * (fnewL row46 K0 : ℝ), 0, ?_⟩
  exact SubNLogN.Math.Walsh.walsh_middle_ideal_of_direct_fft SubNLogN.Math.Walsh.direct_fft
    (schedP p0 K0) (fnewD row46 K0) (fnewL row46 K0) (KK row46 K0) (fnewA row46 K0)
    hq8 (by unfold fnewD; omega) hl2 hlq hK1 hKl
    (fun i => by unfold fnewA fnewL; split_ifs <;> simp)

/-- **The two-field reduction interface (`PendingContracts`).** Combines the analytic bridge
precision theorem (`Wired.bridge_precision`, supplied in `Assembly/Cut.lean`) with the machine
bridge-branch cut (`WalshBranchCut`, discharged in `Assembly/KernelCutFinal.lean`):
* `bridgePrecision`: Theorem 4.7 (`thm:bridge-precision`, `Bridge_precisionStmt`, `Math/Bridge/Precision.lean`);
* `walshBranch`: for some threshold `N` and step bound `Tw`, a closed pipe machine on
  `BLoc mw ⊕ Ew` computing the bridge branch
  `FnewOfR roundHalfUpR row46 (TabConcreteR roundHalfUpR row46) (walshMid row46)`
  on every pipe input with `N ≤ n` (`WalshBranchFromStmt`, `Machine/Pipe/Contract.lean`), whose
  step bound satisfies the Walsh-route cost clause (`WalshCostClause`: `Tw ≤ C·walshCostNatW8 row46
  λ' τ m D_set n + C·(|tape| + 1)` for large `n`, `m` a polylogarithmic multiplication-cost
  envelope). -/
structure PendingContracts : Prop where
  /-- Theorem 4.7 (`thm:bridge-precision`), the bridge precision theorem. -/
  bridgePrecision : Bridge_precisionStmt
  /-- The bridge-branch pipe machine above a threshold, with the Walsh-route cost (Section 7.3). -/
  walshBranch : ∃ (N : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
    SubNLogN.Machine.Pipe.WalshBranchFromStmt
      (FnewOfR roundHalfUpR row46 (TabConcreteR roundHalfUpR row46) (walshMid row46)) N Tw ∧
    SubNLogN.Machine.Pipe.WalshCostClause Tw

/-- The current cut implies the v1 cut at the concrete tables and middle (0 `sorry`). -/
theorem pendingFor_of_pending (h : PendingContracts) :
    PendingContractsFor (TabConcreteR roundHalfUpR row46) (walshMid row46) where
  rootW8 := rootW8_Fnew_of h.bridgePrecision walshOK_balanced
  tables := fun p0 K0 hOK =>
    tabConcrete_certified roundHalfUpR isNearestRounding_roundHalfUpR row46 p0 K0 hOK
  middle := middle_walshMid
  pipe := by
    obtain ⟨N, Tw, hW, hC⟩ := h.walshBranch
    exact SubNLogN.Machine.Pipe.exists_pipeFnewX _ _ N Tw hW hC

/-- **`W9SubNLogNSpecX` from the pending contracts (`w9X_of_contracts`).** -/
theorem w9X_of_contracts (h : PendingContracts) : W9SubNLogNSpecX :=
  w9X_of_contractsFor _ _ (pendingFor_of_pending h)

end SubNLogN.Assembly
