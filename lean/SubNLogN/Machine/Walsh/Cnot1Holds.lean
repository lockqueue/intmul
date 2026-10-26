/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.Cnot1
import SubNLogN.Machine.K1.DigitPairPerm

/-!
# `SubNLogN.Machine.Walsh.Cnot1Holds`: `Cnot1MachineStmt`, unconditional (K3.3)

Paper: Lemma 5.4 (`lem:cnot`), the leftover targets of Theorem 5.8 (`thm:positional-perm`), and
Lemma A.4(1) (`lem:transfer-streams`).

**Scope (honest summary).** Proved (no `sorry`, no hypotheses): `cnot1Machine_holds :
Cnot1MachineStmt`, by instantiating `cnot1Machine_of_pairPerm` (`Walsh/Cnot1.lean`) with the
pair-permutation kernel `K1Digit.k1PairPerm_holds 2 cnotPP` (`K1/DigitPairPerm.lean`).
-/

namespace SubNLogN.Machine.WalshCnot1

/-- **K3.3, one controlled flip, proved** (`Cnot1MachineStmt`, `Contracts/Walsh.lean`). -/
theorem cnot1Machine_holds : Cnot1MachineStmt :=
  cnot1Machine_of_pairPerm (K1Digit.k1PairPerm_holds 2 cnotPP)

end SubNLogN.Machine.WalshCnot1
