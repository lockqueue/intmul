/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Div
import SubNLogN.Machine.Tables.Roles
import SubNLogN.Math.Bridge.IntForms.Tables
import SubNLogN.Machine.Contracts.Records
import SubNLogN.Machine.Contracts.Bridge

/-!
# K6 (`Machine/Tables/TapEntryStmt.lean`): the tap-record fragment — statement only

**Scope (honest summary).** Defines the stored window `tapWin`, the per-record cost unit
`tapRecCost` and the named contract statement `TapRecStmt` (consumed by the tap-block
loops of K6 as an explicit hypothesis, proved in `TapRec.lean`); the stack roles it refers to live in
`Roles.lean`. Nothing is proved here except the definitional `tapOffsets_eq_tapWin`.

`TapRecStmt` asks for **one** host program (`TP I`, uniform in all runtime data) that pushes the
tap record of shift index `a`: the stored coefficients `tapInt ω P t A a e`, `e` in the stored
window (the integer form of `gridInt (P+2) (tapConcreteR roundHalfUpR ω P t A a e)`,
`SubNLogN/Math/Bridge/IntForms/Tables.lean`) in the record format of `Contracts/Records.lean`
(`crecBits`, then `sep`) onto `tapTab`, reading the runtime parameters from fixed scratch
stacks (each holding exactly one number), using the scratch stacks `.inr 40 … .inr 60` as
temporaries (empty before and after), and restoring every other stack. Cost: per entry `(2P+1)` sample
evaluations of size `tabUnit` plus the output width.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms

/-- The stored window of offsets for the axis length `t` (`tapOffsets t P i = tapWin (t i) P`). -/
def tapWin (t P : ℕ) : List ℤ :=
  if 2 * P + 1 ≤ t then (List.range (2 * P + 1)).map fun n => (n : ℤ) - (P : ℤ)
  else (List.range t).map fun n => (n : ℤ)

theorem tapOffsets_eq_tapWin {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (i : Fin d) :
    tapOffsets t P i = tapWin (t i) P := rfl

/-- Cost unit of one tap record: `|tapWin t P|` (`≤ 2P+1`) entries, each with `2P+1` samples of
size `tabUnit` (`Contracts/Tables.lean:54`) and the output width. The factor is the exact window
length (not `2P+1`) so that the output-width part `|tapWin|·(wT+1)` is covered by `tapTabLen`
(`wT` is not bounded by `tabUnit`). -/
def tapRecCost (ω P t A wT : ℕ) : ℕ :=
  (tapWin t P).length *
    ((2 * P + 1) * (ω + 4 * P + 2 * Nat.size (2 * t * A) + 100) ^ 5 + wT + 1)

/-- **[INTERFACE] The tap-record machine** (`TapRecStmt`). One closed host
program `prog` (chosen after the constant `K` and the instance bundle, before all runtime data)
such that, for every host state `B` with the parameters on their role stacks (each stack holding
exactly the number), empty temporaries `.inr 40 … .inr 60`, `1 ≤ ω`, `1 ≤ wT`, `1 ≤ t`, `a < A`,
and every stored entry fitting `wT` bits, `prog` pushes the tap record
`recSyms (crecBits wT [tapInt ω P t A a e | e ∈ tapWin t P])` (first entry's real field on top,
record end `sep` at the bottom) onto `tapTab` and restores every other stack, within
`K·(C+1)·(KM+1)·tapRecCost`. -/
def TapRecStmt : Prop :=
  ∃ K : ℕ, ∀ (I : TB) (Mul : ℕ → ℕ) (C KM : ℕ), I.Spec Mul C → (∀ w, Mul w ≤ KM * (w + 1) ^ 2) →
    ∃ prog : TP I, prog.Closed ∧
      ∀ (B : TL → List Sym) (ω P wT t A a : ℕ),
        1 ≤ ω → 1 ≤ wT → 1 ≤ t → a < A →
        (∀ e ∈ tapWin t P, FitsTwos wT (tapInt ω P t A a e).1 ∧
          FitsTwos wT (tapInt ω P t A a e).2) →
        B rP = natSyms P → B rW = natSyms ω → B rB = natSyms (tapPrec P) →
        B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec P))).1 →
        B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec P))).1 →
        B rPW = intSyms ((2 ^ wT : ℕ) : ℤ) → B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ) →
        B rT = natSyms t → B rA = natSyms A → B rDen = natSyms (2 * t * A) → B ra = natSyms a →
        (∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) →
        HT [] B prog
          (Function.update B sTap
            (recSyms (crecBits wT ((tapWin t P).map (tapInt ω P t A a))) ++ B sTap))
          (K * (C + 1) * (KM + 1) * tapRecCost ω P t A wT)

end SubNLogN.Machine.Tables
