/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Records
import SubNLogN.Math.Common.DFT

/-!
# `SubNLogN.Machine` contracts (`Contracts/RecordsTensor.lean`): tensor address orders

**Scope (honest summary).** Two definitions only (no kernel, no contract): the storage orders of
tensor arrays `Idx t → ℂ` used by the bridge (`SubNLogN.Math.Common.DFT`; Sections 4.1 and 4.4).
Split from `Contracts/Records.lean` so that the record format does not depend on `DFT.lean`.
-/

namespace SubNLogN.Machine

open SubNLogN.Math.Common

/-- Tensor addresses in input order (`encIn`: axis `0` least significant). -/
def idxAddrsIn {d : ℕ} (t : Fin d → ℕ) : List (Idx t) :=
  (List.finRange (totalLen t)).map (encIn t).symm

/-- Tensor addresses in natural frequency order (`encFreq`: last axis contiguous). -/
def idxAddrsFreq {d : ℕ} (t : Fin d → ℕ) : List (Idx t) :=
  (List.finRange (totalLen t)).map (encFreq t).symm

end SubNLogN.Machine
