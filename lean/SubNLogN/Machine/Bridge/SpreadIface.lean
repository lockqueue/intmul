/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadPrim

/-!
# K5 spreading: AR-level sub-contracts of the block step (`Bridge/SpreadIface.lean`)

**Scope (honest summary).** Statements only (no proofs): three AR-level (`Arith/Base.lean`)
sub-contracts of the line primitive of `SpreadLinesStmt`, split off so that they can be proved in
parallel. Each asserts the existence of a program, uniform in the stack type `K` and given by an
injective role map `ι : Role → K`, closed (`Prog.Closed`, needed for the closed kernel program
of `SpreadLinesStmt`), with an exact final state (named roles as stated, every other stack
unchanged) and a cost bound `C · (…)` with a constant `C` independent of the data.

* `SlotPassStmt`: the bit-serial lockstep adder of one output slot: nine bit streams (signs
  `+,+,+,+,-,-,-,-,+`), `s` steps from carry `0`, the `s` output bits pushed onto `out`
  (`serialRun`, `SpreadMath.lean`). An exhausted stream reads as `0`.
* `PackDataStmt`: Kronecker packing of a block of `m ≤ W` one-coefficient data records (width
  `w`) into the four nonnegative parts `re⁺, re⁻, im⁺, im⁻` (`cpart`), slot width `s`, as binary
  counters `natSyms (pack s …)`; the record count is pushed as marks.
* `PackFilterStmt`: the same for one tap record `F` (width `w`), packed in reverse order (the
  filter of the correlation), with a restore copy of the consumed record.

All declarations live in `SubNLogN.Machine.Bridge.SpreadAux`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith

/-! ## The slot pass -/

/-- Roles of the slot pass: nine bit streams, the output, a ruler (`s` marks) and a walk
temporary. -/
inductive SlotRole
  | src (j : Fin 9)
  | out
  | R
  | X
  deriving DecidableEq

/-- Signs of the slot-pass streams (`true` = `+`): streams `0-3` positive, `4-7` negative, `8`
(the overlap-add tail) positive. -/
def slotSign (j : Fin 9) : Bool := decide ((j : ℕ) < 4 ∨ (j : ℕ) = 8)

/-- The signed stream family of the slot pass. -/
def slotSrcs (L : Fin 9 → List Bool) : List (Bool × List Bool) :=
  (List.finRange 9).map fun j => (slotSign j, L j)

/-- **[SUB-CONTRACT] Slot pass.** Stream `j` holds the bits `L j` (LSB on top) above a
non-bit `rest j`. The program consumes the first `s` bits of every stream (fewer if it is
shorter; an exhausted stream reads as `0` and is not popped further), and pushes the `s` output
bits of the lockstep adder `serialRun s 0 (slotSrcs L)` (= `twosBits s (∑ ±value)`,
`serialRun_correct`) onto `out`, in order (so the last output bit ends on top). The ruler `R`
(`s` marks above a non-mark `D`) and the temporary `X` are restored; every other stack is
unchanged. Cost `≤ C·(s+1)`. -/
def SlotPassStmt : Prop :=
  ∃ (prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K) (C : ℕ),
  (∀ (K : Type) [DecidableEq K] (ι : SlotRole → K), (prog K ι).Closed) ∧
  ∀ (K : Type) [DecidableEq K] (ι : SlotRole → K), Function.Injective ι →
  ∀ (s : ℕ) (L : Fin 9 → List Bool) (rest : Fin 9 → List Sym) (D : List Sym)
    (S : K → List Sym) (v : AReg),
    (∀ j, TermOK (rest j)) → D.head? ≠ some .mark → (S (ι .X)).head? ≠ some .mark →
    S (ι .R) = List.replicate s .mark ++ D →
    (∀ j, S (ι (.src j)) = (L j).map Sym.bit ++ rest j) →
    ∃ (v' : AReg) (S' : K → List Sym) (c : ℕ), Eval [] (prog K ι) ⟨v, S⟩ ⟨v', S'⟩ c ∧
      c ≤ C * (s + 1) ∧
      (∀ j, S' (ι (.src j)) = ((L j).drop s).map Sym.bit ++ rest j) ∧
      S' (ι .out) = (serialRun s 0 (slotSrcs L)).reverse.map Sym.bit ++ S (ι .out) ∧
      ∀ k, (∀ j, k ≠ ι (.src j)) → k ≠ ι .out → S' k = S k

/-! ## Kronecker packing -/

/-- The four nonnegative parts of a coefficient at width `w`: `re⁺, re⁻, im⁺, im⁻`, where
`z = lowPart w z - sgnPart w z` for `FitsTwos w z` (`split_eq`). -/
def cpart (w : ℕ) (k : Fin 4) (x : CInt) : ℕ :=
  ![lowPart w x.1, sgnPart w x.1, lowPart w x.2, sgnPart w x.2] k

/-- Roles of the data packer: the source records, the four packed outputs, the record counter
`M`, three rulers (`W`, `w - 1`, `s - w` marks) and eight scratch stacks (empty before and
after). -/
inductive PackRole
  | src
  | out (k : Fin 4)
  | M
  | RW
  | Rlo
  | Rpad
  | tmp (j : Fin 8)
  deriving DecidableEq

/-- **[SUB-CONTRACT] Data packing.** The source holds `m = |B| ≤ W` one-coefficient records of
width `w` (`carrSyms w`), followed by `rest`, which starts with a non-bit when `m < W` (so the
packer stops after `W` records or at the first non-record). The program pops the `m` records and
pushes, for each part `k`, the binary counter `natSyms (pack s (B.map (cpart w k)))` (record `0` in
the least significant slot) onto `out k`, and `m` marks onto `M`. Rulers are restored, scratch
stacks are empty again, every other stack is unchanged. Cost `≤ C·(W·(s+1)+1)`. -/
def PackDataStmt : Prop :=
  ∃ (prog : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K) (C : ℕ),
  (∀ (K : Type) [DecidableEq K] (ι : PackRole → K), (prog K ι).Closed) ∧
  ∀ (K : Type) [DecidableEq K] (ι : PackRole → K), Function.Injective ι →
  ∀ (W w s : ℕ) (B : List CInt) (rest DW Dlo Dpad : List Sym) (S : K → List Sym) (v : AReg),
    1 ≤ w → w ≤ s → B.length ≤ W → (B.length < W → TermOK rest) →
    (∀ x ∈ B, FitsTwos w x.1 ∧ FitsTwos w x.2) →
    DW.head? ≠ some .mark → Dlo.head? ≠ some .mark → Dpad.head? ≠ some .mark →
    S (ι .src) = carrSyms w (B.map fun x => [x]) ++ rest →
    S (ι .RW) = List.replicate W .mark ++ DW →
    S (ι .Rlo) = List.replicate (w - 1) .mark ++ Dlo →
    S (ι .Rpad) = List.replicate (s - w) .mark ++ Dpad →
    (∀ j, S (ι (.tmp j)) = []) →
    ∃ (v' : AReg) (S' : K → List Sym) (c : ℕ), Eval [] (prog K ι) ⟨v, S⟩ ⟨v', S'⟩ c ∧
      c ≤ C * (W * (s + 1) + 1) ∧
      S' (ι .src) = rest ∧
      (∀ k, S' (ι (.out k)) = natSyms (pack s (B.map (cpart w k))) ++ S (ι (.out k))) ∧
      S' (ι .M) = List.replicate B.length .mark ++ S (ι .M) ∧
      ∀ k, k ≠ ι .src → (∀ j, k ≠ ι (.out j)) → k ≠ ι .M → S' k = S k

/-- Roles of the filter packer: the source (tap table), the four packed outputs, the restore
copy `tr`, two rulers (`w - 1`, `s - w` marks) and eight scratch stacks (empty before and
after). -/
inductive FiltRole
  | src
  | out (k : Fin 4)
  | tr
  | Rlo
  | Rpad
  | tmp (j : Fin 8)
  deriving DecidableEq

/-- **[SUB-CONTRACT] Filter packing.** The source holds one record `F` of width `w`
(`carrSyms w [F]`, so its symbols end with `sep`) above `rest`. The program pops the record,
pushes its symbols in reading order onto `tr` (so `tr` receives the reversed symbol list), and
pushes for each part `k` the binary counter `natSyms (pack s (F.reverse.map (cpart w k)))` (the
last coefficient of `F` in the least significant slot) onto `out k`. Rulers are restored,
scratch stacks are empty again, every other stack is unchanged. Cost `≤ C·(|F|·(s+1)+1)`. -/
def PackFilterStmt : Prop :=
  ∃ (prog : ∀ (K : Type) [DecidableEq K], (FiltRole → K) → AProg K) (C : ℕ),
  (∀ (K : Type) [DecidableEq K] (ι : FiltRole → K), (prog K ι).Closed) ∧
  ∀ (K : Type) [DecidableEq K] (ι : FiltRole → K), Function.Injective ι →
  ∀ (w s : ℕ) (F : List CInt) (rest Dlo Dpad : List Sym) (S : K → List Sym) (v : AReg),
    1 ≤ w → w ≤ s → (∀ x ∈ F, FitsTwos w x.1 ∧ FitsTwos w x.2) →
    Dlo.head? ≠ some .mark → Dpad.head? ≠ some .mark →
    S (ι .src) = carrSyms w [F] ++ rest →
    S (ι .Rlo) = List.replicate (w - 1) .mark ++ Dlo →
    S (ι .Rpad) = List.replicate (s - w) .mark ++ Dpad →
    (∀ j, S (ι (.tmp j)) = []) →
    ∃ (v' : AReg) (S' : K → List Sym) (c : ℕ), Eval [] (prog K ι) ⟨v, S⟩ ⟨v', S'⟩ c ∧
      c ≤ C * (F.length * (s + 1) + 1) ∧
      S' (ι .src) = rest ∧
      S' (ι .tr) = (carrSyms w [F]).reverse ++ S (ι .tr) ∧
      (∀ k, S' (ι (.out k)) = natSyms (pack s (F.reverse.map (cpart w k))) ++ S (ι (.out k))) ∧
      ∀ k, k ≠ ι .src → k ≠ ι .tr → (∀ j, k ≠ ι (.out j)) → S' k = S k

end SubNLogN.Machine.Bridge.SpreadAux
