/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanModeShift
import SubNLogN.Machine.Walsh.CnotScanModeSelScalar
import SubNLogN.Machine.Walsh.CnotScanCz
import SubNLogN.Machine.Walsh.CnotScanSelPhase

/-!
# `SubNLogN.Machine.Walsh.CnotScan`: the four recordwise scans of a CNOT batch

Paper: Lemma 5.1 (`lem:walsh-select`), Section 5.2 eq. (`eq:walsh-CZ`), and Proposition 5.5 (`prop:cnot-batch`) (the gadget's `S_U`
diagonal and scalar, the sign diagonal `CZ`, the final `×2^s`). Contract: `CnotScanStmt`
(`Walsh/CnotLeaf.lean:83`).

**Scope (honest summary).** `cnotScan_holds : ∀ mode, CnotScanStmt mode`, unconditional, by cases:
`shift` (`cnotScanShift_holds`, `Walsh/CnotScanModeShift.lean`), `selScalar`
(`cnotScanSelScalar_holds`, `Walsh/CnotScanModeSelScalar.lean`), `cz`
(`SubNLogN.Machine.cnotScanCz_holds`, K1-add, `Walsh/CnotScanCz.lean`) and `selPhase`
(`SubNLogN.Machine.cnotScanSelPhase_holds`, K1-add, `Walsh/CnotScanSelPhase.lean`).
`cnotScan_of_selPhase` is the intermediate form with `selPhase` as a hypothesis.
-/

namespace SubNLogN.Machine.WalshScanAux

open SubNLogN.Machine

/-- **K3.4b, all four scans, from the mode `selPhase`** (`CnotScanStmt`, `Walsh/CnotLeaf.lean`;
Lemma 5.1 (`lem:walsh-select`), Proposition 5.5 (`prop:cnot-batch`)): `shift`, `selScalar` and `cz` are proved (no
hypothesis); `selPhase` enters as the explicit hypothesis `hsp`. -/
theorem cnotScan_of_selPhase (hsp : CnotScanStmt .selPhase) : ∀ mode, CnotScanStmt mode
  | .selPhase => hsp
  | .cz => cnotScanCz_holds
  | .selScalar => cnotScanSelScalar_holds
  | .shift => cnotScanShift_holds

/-- **K3.4b, the four recordwise scans of a CNOT batch, proved** (`CnotScanStmt mode` for every
`mode : CnotScanMode`, `Walsh/CnotLeaf.lean:83`; Lemma 5.1 (`lem:walsh-select`), Proposition 5.5 (`prop:cnot-batch`)). No
hypotheses beyond those of the contract. -/
theorem cnotScan_holds (mode : CnotScanMode) : CnotScanStmt mode :=
  cnotScan_of_selPhase cnotScanSelPhase_holds mode

end SubNLogN.Machine.WalshScanAux
