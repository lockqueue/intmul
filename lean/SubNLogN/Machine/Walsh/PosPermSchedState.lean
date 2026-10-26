/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedTbl
import SubNLogN.Machine.Walsh.PosPermLeaf

/-!
# Schedule compiler, part 4 (`Machine/Walsh/PosPermSchedState.lean`): the compiler's stacks

The kernel of `PosPermSchedStmt` runs on `Stk = KLoc (Fin 3) (RawN ⊕ RegN)`: the three named
stacks (`0` header, `1` permutation, `2` output), raw scratch stacks `RawN` (tables, the output
accumulator `ACC`, temporaries) and unary registers `RegN`.

`StageEmitSpec stageProg` is the specification of one emission stage: for a
table `IT ∈ {I0T, I1T}` holding an involution `I` as `utab`, the registers `m, d, K`, and all other
registers and the scratch raw stacks `BT, U, B1, …, B4` empty, `stageProg IT stA` pushes
`(schedSyms (stageCmds m d K (stageA I or stageB I))).reverse` onto `ACC` and restores everything
else.

**Scope (honest summary).** Definitions only; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh

/-- Raw scratch stacks: the tables `PT` (π), `I0T`, `I1T` (involutions), `BT` (a batch), the
output accumulator `ACC`, and temporaries `U`, `B1`–`B4`. -/
inductive RawN
  | PT | I0T | I1T | BT | ACC | U | B1 | B2 | B3 | B4
  deriving DecidableEq

instance : Fintype RawN :=
  Fintype.ofList [.PT, .I0T, .I1T, .BT, .ACC, .U, .B1, .B2, .B3, .B4]
    (by intro w; cases w <;> decide)

/-- Unary registers. -/
inductive RegN
  | d | K | m
  | xc | x | y | b | kc | kk | idx | len | fnd | v | e0 | e1 | lc
  | f | t1 | t2 | t3 | tmp
  | J | G | gc | g | rc | rho | j0 | D | nS | DK | hi | cnt | c | t | Ix | xu | JK
  | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  deriving DecidableEq

instance : Fintype RegN :=
  Fintype.ofList [.d, .K, .m, .xc, .x, .y, .b, .kc, .kk, .idx, .len, .fnd, .v, .e0, .e1, .lc, .f,
    .t1, .t2, .t3, .tmp, .J, .G, .gc, .g, .rc, .rho, .j0, .D, .nS, .DK, .hi, .cnt, .c, .t, .Ix, .xu,
    .JK, .q1, .q2, .q3, .q4, .q5, .q6, .q7, .q8]
    (by intro q; cases q <;> decide)

/-- The private scratch of the kernel. -/
abbrev Scr : Type := RawN ⊕ RegN

/-- The kernel's stacks. -/
abbrev Stk : Type := KLoc (Fin 3) Scr

/-- A raw scratch stack. -/
abbrev rs (w : RawN) : Stk := .inr (.inl w)

/-- A unary register. -/
abbrev rg (q : RegN) : Stk := .inr (.inr q)

/-- The values of a map `Fin m → Fin m` as naturals (the table layout). -/
def finVals {m : ℕ} (f : Fin m → Fin m) : List ℕ := List.ofFn fun p => (f p : ℕ)

/-- **Stage-emission specification (one stage).** -/
def StageEmitSpec (stageProg : RawN → Bool → SProg Stk) : Prop :=
  ∃ C k : ℕ, ∀ (IT : RawN) (_ : IT = .I0T ∨ IT = .I1T) (stA : Bool) (m d K : ℕ)
    (I : Fin m → Fin m) (S : Stk → List Sym) (A : List Sym), 1 ≤ d → 1 ≤ K →
    S (rs IT) = utab (finVals I) → S (rg .m) = una m → S (rg .d) = una d → S (rg .K) = una K →
    S (rs .ACC) = A → (∀ q, q ≠ .m → q ≠ .d → q ≠ .K → S (rg q) = []) →
    S (rs .BT) = [] → S (rs .U) = [] → S (rs .B1) = [] → S (rs .B2) = [] →
    S (rs .B3) = [] → S (rs .B4) = [] →
    Runs (stageProg IT stA) S
      (Function.update S (rs .ACC)
        ((schedSyms (stageCmds m d K (if stA then stageA I else stageB I))).reverse ++ A))
      (fun _ => True) (C * (m + d + K + 1) ^ k)

/-- **Stage-emission contract.** Some closed stage program family satisfies `StageEmitSpec`. -/
def StageProgStmt : Prop :=
  ∃ stageProg : RawN → Bool → SProg Stk,
    (∀ IT stA, (stageProg IT stA).Closed) ∧ StageEmitSpec stageProg

end SubNLogN.Machine.Walsh.PosPermSchedAux
