/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedCycMath

/-!
# Schedule compiler, part 7 (`Machine/Walsh/PosPermSchedDefs.lean`): cycle-phase sub-statements

State-level sub-statements of the schedule compiler on `Stk` (`PosPermSchedState.lean`),
with `CycPushSpec` carrying the explicit bounds `n ≤ m`, `i ≤ m`. Each is `∃ P, P.Closed ∧ Spec P`.

`ScrClean S keep`: every register outside `keep` and every raw temporary
(`U, BT, B1, …, B4`) is empty. All other stacks (named stacks, `PT`, `I0T`, `I1T`, `ACC`) may hold
data. Since `Runs` fixes the exact final state, they are restored.
* `CycBaseStmt` (a): `b := baseAcc π x m` (= `cycleBase π x`, `cycleBase_val`).
* `CycIdxLenStmt` (b): `idx := findAcc … m` (= `cycleIdx`), `len := findAcc … m + 1`
  (= `cycleLen`), from `b`.
* `CycPushStmt` (c): push `π^[(n-i)%n] b` onto `I0T` and `π^[(n+1-i)%n] b` onto `I1T`
  (`n = len`, `i = idx`).
* `CycPhaseStmt`: the whole cycle phase, `I0T := utab (finVals (invol0 π))`,
  `I1T := utab (finVals (invol1 π))`.
The outer loop counter `xc` is live during (a)–(c); `d`, `K` (header values) are live throughout.

**Scope (honest summary).** Definitions only; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh

/-- Every register outside `keep` and every raw temporary is empty. -/
def ScrClean (S : Stk → List Sym) (keep : List RegN) : Prop :=
  (∀ q, q ∉ keep → S (rg q) = []) ∧ S (rs .U) = [] ∧ S (rs .BT) = [] ∧ S (rs .B1) = [] ∧
    S (rs .B2) = [] ∧ S (rs .B3) = [] ∧ S (rs .B4) = []

/-- (a) The cycle base, by walking `m` orbit steps. -/
def CycBaseSpec (P : SProg Stk) : Prop :=
  ∃ C k : ℕ, ∀ (m : ℕ) (π : Fin m → Fin m) (x : ℕ) (S : Stk → List Sym), x < m →
    S (rs .PT) = utab (finVals π) → S (rg .m) = una m → S (rg .x) = una x →
    ScrClean S [.m, .xc, .x, .d, .K] →
    Runs P S (Function.update S (rg .b) (una (baseAcc π x m))) (fun _ => True)
      (C * (m + 1) ^ k)

/-- (a) frozen target. -/
def CycBaseStmt : Prop := ∃ P : SProg Stk, P.Closed ∧ CycBaseSpec P

/-- (b) The cycle index and length of `x` from its base `bb`, by first-hit scans over `k < m`. -/
def CycIdxLenSpec (P : SProg Stk) : Prop :=
  ∃ C k : ℕ, ∀ (m : ℕ) (π : Fin m → Fin m) (x bb : ℕ) (S : Stk → List Sym), x < m → bb < m →
    S (rs .PT) = utab (finVals π) → S (rg .m) = una m → S (rg .x) = una x →
    S (rg .b) = una bb → ScrClean S [.m, .xc, .x, .b, .d, .K] →
    Runs P S
      (Function.update (Function.update S (rg .idx)
          (una (findAcc (fun j => decide ((piN π)^[j] bb = x)) m))) (rg .len)
        (una (findAcc (fun j => decide ((piN π)^[j] (piN π bb) = bb)) m + 1)))
      (fun _ => True) (C * (m + 1) ^ k)

/-- (b) frozen target. -/
def CycIdxLenStmt : Prop := ∃ P : SProg Stk, P.Closed ∧ CycIdxLenSpec P

/-- (c) Push the two involution values of the current point onto `I0T`, `I1T`. -/
def CycPushSpec (P : SProg Stk) : Prop :=
  ∃ C k : ℕ, ∀ (m : ℕ) (π : Fin m → Fin m) (bb i n : ℕ) (S : Stk → List Sym), bb < m → 1 ≤ n →
    n ≤ m → i ≤ m →
    S (rs .PT) = utab (finVals π) → S (rg .m) = una m → S (rg .b) = una bb →
    S (rg .idx) = una i → S (rg .len) = una n →
    ScrClean S [.m, .xc, .x, .b, .idx, .len, .d, .K] →
    Runs P S
      (Function.update (Function.update S (rs .I0T)
          (ent ((piN π)^[(n - i) % n] bb) ++ S (rs .I0T))) (rs .I1T)
        (ent ((piN π)^[(n + 1 - i) % n] bb) ++ S (rs .I1T)))
      (fun _ => True) (C * (m + 1) ^ k)

/-- (c) frozen target. -/
def CycPushStmt : Prop := ∃ P : SProg Stk, P.Closed ∧ CycPushSpec P

/-- The whole cycle phase: the two involution tables. -/
def CycPhaseSpec (P : SProg Stk) : Prop :=
  ∃ C k : ℕ, ∀ (m : ℕ) (π : Fin m → Fin m) (S : Stk → List Sym),
    S (rs .PT) = utab (finVals π) → S (rg .m) = una m → S (rs .I0T) = [] →
    S (rs .I1T) = [] → ScrClean S [.m, .d, .K] →
    Runs P S
      (Function.update (Function.update S (rs .I0T) (utab (finVals (invol0 π)))) (rs .I1T)
        (utab (finVals (invol1 π))))
      (fun _ => True) (C * (m + 1) ^ k)

/-- Cycle-phase frozen target (from (a), (b), (c)). -/
def CycPhaseStmt : Prop := ∃ P : SProg Stk, P.Closed ∧ CycPhaseSpec P

end SubNLogN.Machine.Walsh.PosPermSchedAux
