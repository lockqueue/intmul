/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Layout
import Mathlib.Data.ZMod.Basic

/-!
# `SubNLogN.Machine` contracts, K1 (`Contracts/Streams.lean`): Appendix A stream primitives and long-record scans

**Scope (honest summary).** This file contains contract *statements* only: data encodings, pure
index specifications, and kernel contracts in the `KContract` shape (`Contracts/Layout.lean`). No
kernel is implemented and no contract is proved. The only proofs are `decide` sanity checks of the
pure specifications on small inputs.

Paper: Appendix A.1 (`sec:transfer-premises`). Lemma A.4 (`lem:transfer-streams`, Fact 3.3) gives
items (1)–(5) and the controlled-shift / unit-multiplication clause. Lemma A.5
(`lem:transfer-long-record`) covers long-record scans (`C3*` are historical names from an earlier draft).

## Encodings (decisions recorded here; the paper fixes only the tape-level ideas)
* **Arrays.** The paper stores arrays in lexicographic address order with addresses implicit (Section 3.2).
  * An array is a list `v : List (List Bool)` of record payloads, record `x` at address `x`.
  * On a stack it is `arrSyms v = blk .down (v.map recSyms)`: first record on top, each record its
    payload bits followed by the record end `sep`. This is the W4 record format `RecOK`
    (`Contracts/Machine/W4.lean:60`).
  * The rest of the stack must satisfy `BlkTerm` (W4).
  * Inputs and outputs use orientation `.down`; an orientation change is one extra `O(V)` pass.
* **Volume.** `V = vol v = (arrSyms v).length`: payload bits plus one end symbol per record.
* **Addresses.** `k` radix-`q` digits, digit `0` most significant (`digitAt`). In §3 of this file,
  mixed ranges and trailing payload fields (Appendix A) are specialized to `k` uniform radix-`q`
  digits with opaque payloads. §5 adds collapsed mixed shapes, with runtime spectator blocks around
  the active digits.
* **Parameters.** Digit positions, digit counts and widths are runtime data. They are passed as
  binary counters `natSyms` (LSB first, as in Lemma A.4) on named parameter stacks, which are restored.
  * Fixed objects are compile-time parameters of the contract definitions, so the cost constant
    may depend on them: the radix `q`, the permutation `π`, the pointwise map `g`, the role count
    `W`, the merge order `ord`, and the unit `a/d`.
* **Digit fields and fixed-width numbers.** A radix-`q` digit stored explicitly is a
  `digitWidth q`-bit group (`digitBits`, LSB first). A `w`-bit two's-complement field is
  `twosBits w z`, the bits of `z mod 2^w`, LSB first; the guard condition is `FitsTwos w z`.
* **Convention.** Every kernel consumes its source array (the source stack becomes `rest`) and
  pushes its result block onto the destination's previous content, as in W4. All other named
  stacks and all private scratch stacks (`KLoc`, restored convention) are unchanged.
* **Concrete stack choices.** While the written text takes Fact 3.3 (`fact:oai-streams`) as a black
  box, the Lean development proves all stream kernels from scratch (`SubNLogN/Machine/K1/`) using
  the concrete choices above (record format, `.down` orientation, counters on parameter stacks,
  uniform radix, digitwise pointwise maps in (3), and equal-length role streams in (4)).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-! ## 1. Encodings -/

/-- A record with payload bits `p`: the bits, then the record end `sep`. It is a W4 `RecOK`
record. -/
def recSyms (p : List Bool) : List Sym := p.map Sym.bit ++ [Sym.sep]

/-- An array of records on a stack, first record on top (`blk .down`). -/
def arrSyms (v : List (List Bool)) : List Sym := blk .down (v.map recSyms)

/-- Logical volume of an array, in stack symbols. -/
def vol (v : List (List Bool)) : ℕ := (arrSyms v).length

/-- `w`-bit unsigned group of `d`, least significant bit first. -/
def bitsLE (w d : ℕ) : List Bool := (List.range w).map fun i => d.testBit i

/-- Bits per explicitly stored radix-`q` digit. -/
def digitWidth (q : ℕ) : ℕ := Nat.size (q - 1)

/-- An explicitly stored radix-`q` digit `d < q`: a fixed-width bit group. -/
def digitBits (q d : ℕ) : List Bool := bitsLE (digitWidth q) d

/-- `w`-bit two's-complement field of `z` (LSB first): the bits of `z mod 2^w`. -/
def twosBits (w : ℕ) (z : ℤ) : List Bool := bitsLE w (z % (2 ^ w : ℤ)).toNat

/-- `z` is representable in a `w`-bit two's-complement field (the guard-bit condition). -/
def FitsTwos (w : ℕ) (z : ℤ) : Prop := -(2 ^ (w - 1) : ℤ) ≤ z ∧ z < 2 ^ (w - 1)

/-! ## 2. Addresses and pure index specifications -/

/-- Digit `i` (`0` = most significant) of the `k`-digit radix-`q` address `x`. -/
def digitAt (q k i x : ℕ) : ℕ := x / q ^ (k - 1 - i) % q

/-- `x` with digit `i` replaced by `d`. -/
def setDigit (q k i d x : ℕ) : ℕ := x - digitAt q k i x * q ^ (k - 1 - i) + d * q ^ (k - 1 - i)

/-- The `k` digits of `x`, most significant first. -/
def digitsMSB (q k x : ℕ) : List ℕ := (List.range k).map fun i => digitAt q k i x

/-- Value of a most-significant-first digit list. -/
def ofDigitsMSB (q : ℕ) (ds : List ℕ) : ℕ := ds.foldl (fun acc d => acc * q + d) 0

/-- Digit `i` of `x` as an element of `Fin q`. -/
def digitFin (q k i x : ℕ) [NeZero q] : Fin q := ⟨digitAt q k i x, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩

/-- An address permutation given by its inverse `g`: output record `y` is input record `g y`. -/
def permByInv {α : Type} [Inhabited α] (g : ℕ → ℕ) (v : List α) : List α :=
  (List.range v.length).map fun y => v.getD (g y) default

/-- (1) Address map of a fixed permutation `π` of the digit pair at positions `i, j`. -/
def pairPermAddr (q k i j : ℕ) [NeZero q] (π : Equiv.Perm (Fin q × Fin q)) (x : ℕ) : ℕ :=
  setDigit q k j (π (digitFin q k i x, digitFin q k j x)).2
    (setDigit q k i (π (digitFin q k i x, digitFin q k j x)).1 x)

/-- (2) Move the digit at position `i` to position `j`, other digits in order. -/
def moveDigitList (ds : List ℕ) (i j : ℕ) : List ℕ := (ds.eraseIdx i).insertIdx j (ds.getD i 0)

/-- (2) Address map of the digit move `i ↦ j`. -/
def moveAddr (q k i j x : ℕ) : ℕ := ofDigitsMSB q (moveDigitList (digitsMSB q k x) i j)

/-- An explicitly stored record of `A`-ary digits: each digit is a `digitWidth A`-bit group. -/
def digitRec (A : ℕ) (ds : List ℕ) : List Bool := ds.flatMap (digitBits A)

/-- (3) Split at digit `i`, apply a fixed *pointwise* map `g` to the `q` aligned streams, and merge.
Records are lists of `B` data digits (alphabet `[A]`, stored with `digitRec`). Output record `x`,
whose address digit `i` is `c`, has data digit `t` equal to
`g (fun c' => data digit t of input record (setDigit i c' x)) c`. -/
def splitMapMerge (q k i : ℕ) [NeZero q] (g : (Fin q → ℕ) → Fin q → ℕ) (B : ℕ)
    (v : List (List ℕ)) : List (List ℕ) :=
  (List.range v.length).map fun x =>
    (List.range B).map fun t =>
      g (fun c' => (v.getD (setDigit q k i c'.val x) []).getD t 0) (digitFin q k i x)

/-- (4) The rows of class `r` modulo `W`, in order. -/
def roleRows {α : Type} (W r : ℕ) (v : List α) : List α :=
  (List.range v.length).filterMap fun x => if x % W = r then v[x]? else none

/-- (4) Merge `W` streams of `g` rows each in the fixed class order `ord`: round `t` emits row `t`
of streams `ord 0, ord 1, …, ord (W - 1)`. -/
def mergeRows {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g : ℕ) (us : Fin W → List α) : List α :=
  (List.range g).flatMap fun t => (List.finRange W).filterMap fun c => (us (ord c))[t]?

/-- (Moreover, rotation) Inverse address map of the controlled cyclic shift. In fiber `c` (records
`c·Q, …, c·Q + Q - 1`), the record at offset `u` moves to offset `(u + off c) mod Q`. -/
def rotInvAddr (Q : ℕ) (off : ℕ → ℕ) (x : ℕ) : ℕ :=
  x / Q * Q + (x % Q + Q - off (x / Q) % Q) % Q

/-- (Moreover, unit) Inverse address map of multiplying the target coordinate by the unit `a/d`
mod `Q`. The record at offset `t` moves to offset `a·t·d⁻¹ mod Q`, so the record now at offset
`u` came from `d·u·a⁻¹ mod Q`. -/
def unitInvAddr (Q a d : ℕ) (x : ℕ) : ℕ :=
  x / Q * Q + d * (x % Q) * ((a : ZMod Q)⁻¹).val % Q

/-- (5) Exact binary shift by `t : ℤ`: `z·2^t` for `t ≥ 0`, and `z / 2^(-t)` for `t < 0` (exact
when the discarded low bits are zero). -/
def shiftZ (z t : ℤ) : ℤ := if 0 ≤ t then z * 2 ^ t.toNat else z / 2 ^ (-t).toNat

/-! ### Sanity checks of the pure specifications (`decide`) -/

example : permByInv (fun y => (y + 3) % 4) [0, 1, 2, 3] = [3, 0, 1, 2] := by decide
example : digitsMSB 3 2 5 = [1, 2] ∧ ofDigitsMSB 3 [1, 2] = 5 := by decide
example : pairPermAddr 2 2 0 1 (Equiv.prodComm _ _) 1 = 2 := by decide
example : moveAddr 2 3 0 2 4 = 1 := by decide
example : splitMapMerge 2 1 0 (fun b c => if c.val = 0 then b 0 else (b 0 + b 1) % 2) 2
    [[1, 0], [1, 1]] = [[1, 0], [0, 1]] := by decide
example : roleRows 2 1 [10, 11, 12, 13, 14] = [11, 13] := by decide
example : mergeRows 2 id 2 (fun r => roleRows 2 r.val [10, 11, 12, 13]) = [10, 11, 12, 13] := by
  decide
example : permByInv (rotInvAddr 4 (fun _ => 1)) [0, 1, 2, 3, 4, 5, 6, 7] =
    [3, 0, 1, 2, 7, 4, 5, 6] := by decide
example : twosBits 4 (-3) = [true, false, true, true] := by decide
example : shiftZ (-12) (-2) = -3 ∧ shiftZ 5 3 = 40 := by decide

/-! ## 3. Contracts: elementary streams (Lemma A.4, `lem:transfer-streams`) -/

/-- **[CONTRACT] K1a, fixed permutation of a digit pair** (Lemma A.4(1), `lem:transfer-streams`: split into
`q²` streams by the two digit values and merge with permuted labels).
Named stacks (`Fin 5`): `0` the source array (consumed), `1` the destination, `2`/`3`/`4` the
counters `k`, `i`, `j` (restored). The array has `q^k` records, and the record at address `x`
moves to `pairPermAddr q k i j π x`. Cost `C·(V + 1)`. -/
def K1PairPermStmt (q : ℕ) [NeZero q] (π : Equiv.Perm (Fin q × Fin q)) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (k i j : ℕ) (v : List (List Bool)) (rest r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      i < k → j < k → i ≠ j → v.length = q ^ k → BlkTerm rest →
      TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms k ++ r2 →
      S (.inl 3) = natSyms i ++ r3 → S (.inl 4) = natSyms j ++ r4 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (pairPermAddr q k i j π.symm) v) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] K1b, move a digit position** (Lemma A.4(2), `lem:transfer-streams`: `q` streams, with
the selected digit inserted at another place of the nested merge). Named stacks as in
`K1PairPermStmt`. The record at address `x` moves to `moveAddr q k i j x`: digit `i` moves to
position `j` and the other digits keep their order. Cost `C·(V + 1)`. -/
def K1MoveDigitStmt (q : ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (k i j : ℕ) (v : List (List Bool)) (rest r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      i < k → j < k → v.length = q ^ k → BlkTerm rest →
      TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms k ++ r2 →
      S (.inl 3) = natSyms i ++ r3 → S (.inl 4) = natSyms j ++ r4 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (moveAddr q k j i) v) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] K1c, split, pointwise map, merge** (Lemma A.4(3), `lem:transfer-streams`). Named stacks (`Fin 4`): `0` the
source (consumed), `1` the destination, `2`/`3` the counters `k`, `i` (restored). Each of the
`q^k` records holds `B` data digits over the alphabet `[A]` (`digitRec A`). The output is
`splitMapMerge q k i g B v`. We read "fixed pointwise map" as a map on aligned data digits;
carry arithmetic is K3. Cost `C·(V + 1)`. -/
def K1SplitMapMergeStmt (q : ℕ) [NeZero q] (A : ℕ) (g : (Fin q → ℕ) → Fin q → ℕ) : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (k i B : ℕ) (v : List (List ℕ)) (rest r2 r3 : List Sym) (S : KLoc (Fin 4) E → List Sym),
      i < k → v.length = q ^ k → (∀ ds ∈ v, ds.length = B ∧ ∀ d ∈ ds, d < A) →
      (∀ (f : Fin q → ℕ) (c : Fin q), (∀ c', f c' < A) → g f c < A) →
      BlkTerm rest → TermOK r2 → TermOK r3 →
      S (.inl 0) = arrSyms (v.map (digitRec A)) ++ rest → S (.inl 2) = natSyms k ++ r2 →
      S (.inl 3) = natSyms i ++ r3 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms ((splitMapMerge q k i g B v).map (digitRec A)) ++ S (.inl 1)))
        (fun _ => True) (C * (vol (v.map (digitRec A)) + 1))

/-- Final stacks of `K2DistributeStmt`: the source becomes `rest`, and role stack `r` receives its
rows `roleRows W r v` (first row on top) on top of its old content. -/
def distPost {W : ℕ} {E : Type} (v : List (List Bool)) (rest : List Sym)
    (S : KLoc (Option (Fin W)) E → List Sym) : KLoc (Option (Fin W)) E → List Sym
  | .inl none => rest
  | .inl (some r) => arrSyms (roleRows W r.val v) ++ S (.inl (some r))
  | .inr e => S (.inr e)

/-- **[CONTRACT] K2a, cyclic distribution of rows into `W` role streams** (Lemma A.4(4),
`lem:transfer-streams`: row `r` goes to stream `r mod W`, each stream keeps the row order). Named stacks
(`Option (Fin W)`): `none` is the source array (consumed) and `some r` is role stack `r`. `W` is
fixed, for example `W_b ≈ 1.8·10^20`. Cost `C·(V + 1)`. -/
def K2DistributeStmt (W : ℕ) : Prop :=
  KContract (Option (Fin W)) Unit fun _ E _ _ _ C P =>
    ∀ (v : List (List Bool)) (rest : List Sym) (S : KLoc (Option (Fin W)) E → List Sym),
      BlkTerm rest → S (.inl none) = arrSyms v ++ rest →
      Runs P S (distPost v rest S) (fun _ => True) (C * (vol v + 1))

/-- Final stacks of `K2MergeStmt`: every role stack `r` loses its block (leaving `rests r`), and the
destination receives the merged rows on top of its old content. -/
def mergePost {W : ℕ} {E : Type} (ord : Fin W → Fin W) (g : ℕ) (us : Fin W → List (List Bool))
    (rests : Fin W → List Sym) (S : KLoc (Option (Fin W)) E → List Sym) :
    KLoc (Option (Fin W)) E → List Sym
  | .inl none => arrSyms (mergeRows W ord g us) ++ S (.inl none)
  | .inl (some r) => rests r
  | .inr e => S (.inr e)

/-- **[CONTRACT] K2b, merge `W` role streams in a fixed order of the row classes** (Lemma A.4(4), `lem:transfer-streams`).
Named stacks (`Option (Fin W)`): `none` is the destination and `some r` is role stack `r`, holding
`g` rows (consumed). The output is `mergeRows W ord g us`. With `ord = id` this inverts
`K2DistributeStmt` on `W·g` rows. Cost `C·(V + 1)`, where `V` is the total volume of the role
streams. -/
def K2MergeStmt (W : ℕ) (ord : Equiv.Perm (Fin W)) : Prop :=
  KContract (Option (Fin W)) Unit fun _ E _ _ _ C P =>
    ∀ (g : ℕ) (us : Fin W → List (List Bool)) (rests : Fin W → List Sym)
      (S : KLoc (Option (Fin W)) E → List Sym),
      (∀ r, (us r).length = g) → (∀ r, BlkTerm (rests r)) →
      (∀ r, S (.inl (some r)) = arrSyms (us r) ++ rests r) →
      Runs P S (mergePost ord g us rests S) (fun _ => True)
        (C * (((List.finRange W).map fun r => vol (us r)).sum + 1))

/-- A stream of `w`-bit two's-complement fields, one field per record. -/
def fieldArr (w : ℕ) (zs : List ℤ) : List (List Bool) := zs.map (twosBits w)

/-- **[CONTRACT] K3, fieldwise addition of two aligned field streams** (Lemma A.4(5), `lem:transfer-streams`:
ordinary carry scans). Named stacks (`Fin 3`): `0` holds `x` and `1` holds `y` (both consumed),
`2` the destination. The width `w ≥ 1` is the record width. The guards: inputs and sums fit `w`
bits. The output is the fieldwise sum. Cost `C·(V + 1)`, where `V` is the input volume. -/
def K3AddStmt : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (w : ℕ) (as bs : List ℤ) (ra rb : List Sym) (S : KLoc (Fin 3) E → List Sym),
      1 ≤ w → as.length = bs.length → (∀ a ∈ as, FitsTwos w a) → (∀ b ∈ bs, FitsTwos w b) →
      (∀ t < as.length, FitsTwos w (as.getD t 0 + bs.getD t 0)) →
      BlkTerm ra → BlkTerm rb →
      S (.inl 0) = arrSyms (fieldArr w as) ++ ra → S (.inl 1) = arrSyms (fieldArr w bs) ++ rb →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) ra) (.inl 1) rb) (.inl 2)
          (arrSyms (fieldArr w (List.zipWith (· + ·) as bs)) ++ S (.inl 2)))
        (fun _ => True) (C * (vol (fieldArr w as) + vol (fieldArr w bs) + 1))

/-- **[CONTRACT] K3, fieldwise subtraction** (Lemma A.4(5), `lem:transfer-streams`). Same shape as `K3AddStmt`, output
`a - b`. -/
def K3SubStmt : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (w : ℕ) (as bs : List ℤ) (ra rb : List Sym) (S : KLoc (Fin 3) E → List Sym),
      1 ≤ w → as.length = bs.length → (∀ a ∈ as, FitsTwos w a) → (∀ b ∈ bs, FitsTwos w b) →
      (∀ t < as.length, FitsTwos w (as.getD t 0 - bs.getD t 0)) →
      BlkTerm ra → BlkTerm rb →
      S (.inl 0) = arrSyms (fieldArr w as) ++ ra → S (.inl 1) = arrSyms (fieldArr w bs) ++ rb →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) ra) (.inl 1) rb) (.inl 2)
          (arrSyms (fieldArr w (List.zipWith (· - ·) as bs)) ++ S (.inl 2)))
        (fun _ => True) (C * (vol (fieldArr w as) + vol (fieldArr w bs) + 1))

/-- **[CONTRACT] K3, fieldwise sign change** (Lemma A.4(5), `lem:transfer-streams`). Named stacks (`Fin 2`): `0` the source
(consumed) and `1` the destination. The guard is that `-a` fits `w` bits. Cost `C·(V + 1)`. -/
def K3NegStmt : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C P =>
    ∀ (w : ℕ) (as : List ℤ) (ra : List Sym) (S : KLoc (Fin 2) E → List Sym),
      1 ≤ w → (∀ a ∈ as, FitsTwos w a ∧ FitsTwos w (-a)) → BlkTerm ra →
      S (.inl 0) = arrSyms (fieldArr w as) ++ ra →
      Runs P S
        (Function.update (Function.update S (.inl 0) ra) (.inl 1)
          (arrSyms (fieldArr w (as.map (- ·))) ++ S (.inl 1)))
        (fun _ => True) (C * (vol (fieldArr w as) + 1))

/-- **[CONTRACT] K3, fieldwise exact binary shift by a supplied exponent** (Lemma A.4(5),
`lem:transfer-streams`: copy the retained interval and fill known zero or sign bits; not `t` one-bit shifts).
Named stacks (`Fin 4`): `0` the source with `w1`-bit fields (consumed), `1` the destination with
`w2`-bit fields, `2` the counter `w2` (restored), `3` the signed exponent `t` (`intSyms`,
restored). The output field is `shiftZ a t`. Right shifts are exact: the discarded low bits are
zero. Cost `C·(V_in + M·(w2 + 1) + bitLen |t| + 1)`: linear in the input and output widths and
uniform in `t`, except for reading its counter. -/
def K3ShiftStmt : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 : ℕ) (t : ℤ) (as : List ℤ) (ra r2 r3 : List Sym) (S : KLoc (Fin 4) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → (∀ a ∈ as, FitsTwos w1 a) →
      (∀ a ∈ as, t < 0 → (2 ^ (-t).toNat : ℤ) ∣ a) → (∀ a ∈ as, FitsTwos w2 (shiftZ a t)) →
      BlkTerm ra → TermOK r2 → TermOK r3 →
      S (.inl 0) = arrSyms (fieldArr w1 as) ++ ra → S (.inl 2) = natSyms w2 ++ r2 →
      S (.inl 3) = intSyms t ++ r3 →
      Runs P S
        (Function.update (Function.update S (.inl 0) ra) (.inl 1)
          (arrSyms (fieldArr w2 (as.map fun a => shiftZ a t)) ++ S (.inl 1)))
        (fun _ => True)
        (C * (vol (fieldArr w1 as) + as.length * (w2 + 1) + bitLen t.natAbs + 1))

/-! ### The "Moreover" clause of Lemma A.4 (`lem:transfer-streams`): controlled shift and unit multiplication -/

/-- **[CONTRACT] Premise of K4: the offset routine** (Lemma A.4, `lem:transfer-streams`, "an offset computable from the controls
in `b^{O(1)}` time"). Named stacks (`Fin 3`): `0` the counter `b`, `1` the control (fiber) index `c`
(both restored), `2` the destination, which receives `natSyms (off b c)`. Cost
`C·(b + bitLen c + 1)^J`. -/
def K4OffsetStmt (off : ℕ → ℕ → ℕ) (J : ℕ) : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (b c : ℕ) (r0 r1 : List Sym) (S : KLoc (Fin 3) E → List Sym), TermOK r0 → TermOK r1 →
      S (.inl 0) = natSyms b ++ r0 → S (.inl 1) = natSyms c ++ r1 →
      Runs P S (Function.update S (.inl 2) (natSyms (off b c) ++ S (.inl 2))) (fun _ => True)
        (C * (b + bitLen c + 1) ^ J)

/-- **[CONTRACT] K4, controlled cyclic shift of the target coordinate** (Lemma A.4,
`lem:transfer-streams`). The array is `nc` fibers of `Q = q^b` records: the target coordinate is the last `b`
digits, and the controls are the fiber index `c`. In fiber `c`, the record at offset `u` moves to
offset `(u + off b c) mod Q`. Named stacks (`Fin 3`): `0` the source (consumed), `1` the
destination, `2` the counter `b` (restored). The explicit premises are: `q ≥ 2`, an offset routine
(`K4OffsetStmt off J`), reduced offsets (`off b c < q^b`), and controls with `O(b)` digits
(`bitLen nc ≤ cb·(b + 1)`). These make the offset work absorbable by the fiber scan, as in
Lemma A.4 (`lem:transfer-streams`). Cost `C·(V + 1)`.

The reduced-offset premise requires the offset routine to return a canonical representative in
`[Q]` (Lemma A.4), so that `% Q` in `rotInvAddr` is a no-op. A use site whose formula
is not reduced supplies `off' b c := off b c % q^b` with its own `b^{O(1)}` routine
(`K4OffsetStmt off' J'`). So the premise only moves the reduction into the supplied routine; it does
not weaken the paper's claim. -/
def K4RotateStmt (q cb J : ℕ) (off : ℕ → ℕ → ℕ) : Prop :=
  2 ≤ q → K4OffsetStmt off J → (∀ b c, off b c < q ^ b) →
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (b nc : ℕ) (v : List (List Bool)) (rest r2 : List Sym) (S : KLoc (Fin 3) E → List Sym),
      v.length = nc * q ^ b → bitLen nc ≤ cb * (b + 1) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms b ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (rotInvAddr (q ^ b) (off b)) v) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] K5, multiplication of the target coordinate by a fixed rational unit `a/d` mod
`Q = q^b`** (Lemma A.4, `lem:transfer-streams`). `a` and `d` are fixed and coprime to `q`. In each fiber,
the record at offset `t` moves to offset `a·t·d⁻¹ mod Q`. Named stacks as in `K4RotateStmt`. Only
positive `a, d` are covered; the paper's negative multiplier is this composed with a reversal.
Cost `C·(V + 1)`. -/
def K5UnitMulStmt (q a d : ℕ) : Prop :=
  Nat.Coprime a q → Nat.Coprime d q →
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (b nc : ℕ) (v : List (List Bool)) (rest r2 : List Sym) (S : KLoc (Fin 3) E → List Sym),
      v.length = nc * q ^ b → BlkTerm rest → TermOK r2 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms b ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (unitInvAddr (q ^ b) a d) v) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-! ## 4. Contracts: long-record address-dependent scans (Lemma A.5, `lem:transfer-long-record`) -/

/-- **[CONTRACT] Premise of Lemma A.5: the address routine** (`lem:transfer-long-record`, "address preparation takes
`P^{O(1)}` time"). Named stacks (`Fin 3`): `0` the record index `x`, `1` the descriptor record `d`
(both restored), `2` the destination, which receives the address-data record `α d x`. Cost
`C·(bitLen x + |d| + 1)^J`. -/
def C3AddrStmt (α : List Bool → ℕ → List Bool) (J : ℕ) : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (x : ℕ) (d : List Bool) (r0 r1 : List Sym) (S : KLoc (Fin 3) E → List Sym), TermOK r0 →
      S (.inl 0) = natSyms x ++ r0 → S (.inl 1) = recSyms d ++ r1 →
      Runs P S (Function.update S (.inl 2) (recSyms (α d x) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen x + d.length + 1) ^ J)

/-- **[CONTRACT] Premise of Lemma A.5: the payload routine** (`lem:transfer-long-record`, "payload processing takes `O(rq)`
time"). Named stacks (`Fin 3`): `0` the record `p` (consumed), `1` the address data `a`
(restored), `2` the destination, which receives the record `F a p`. Cost `C·(|p| + |a| + 1)`. -/
def C3PayloadStmt (F : List Bool → List Bool → List Bool) : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (p a : List Bool) (rest r1 : List Sym) (S : KLoc (Fin 3) E → List Sym),
      S (.inl 0) = recSyms p ++ rest → S (.inl 1) = recSyms a ++ r1 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 2)
          (recSyms (F a p) ++ S (.inl 2)))
        (fun _ => True) (C * (p.length + a.length + 1))

/-- **[CONTRACT] Long-record address-dependent scan** (Lemma A.5, `lem:transfer-long-record`).
* Inputs: an address routine `α` (`C3AddrStmt α J`) and a payload routine `F` (`C3PayloadStmt F`).
* Effect: record `x` of the array becomes `F (α d x) p_x`.
* Named stacks (`Fin 3`): `0` the source array (consumed), `1` the destination, `2` the descriptor
  record `d` (restored).
* The paper's hypothesis "records of `Θ(rq)` bits, addresses and descriptors `O(q)`,
  `r/q^j → ∞`" is made explicit at the routine's exponent `J`:
  `(bitLen M + |d| + 1)^J ≤ |p_x| + 1` for every record `x`, where `M` is the number of records.
* Cost `C·(V + 1)`; the constant depends only on `J` and the two routines.
* Special cases (Lemma A.5): a per-record phase in `{1, -1, i, -i}`, and twiddle selection by one
  table scan per record.
* General coefficient multiplications after the scan are charged separately (Lemma A.5). -/
def C3LongRecordScanStmt (α : List Bool → ℕ → List Bool) (F : List Bool → List Bool → List Bool)
    (J : ℕ) : Prop :=
  C3AddrStmt α J → C3PayloadStmt F →
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (d : List Bool) (v : List (List Bool)) (rest r2 : List Sym) (S : KLoc (Fin 3) E → List Sym),
      (∀ x < v.length, (bitLen v.length + d.length + 1) ^ J ≤ (v.getD x []).length + 1) →
      BlkTerm rest →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = recSyms d ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (v.mapIdx fun x p => F (α d x) p) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-! ## 5. Mixed-shape generalizations

The §3 contracts use uniform radix-`q` addresses. Their Appendix A consumers (Lemma A.6, Proposition A.7, Lemmas A.8–A.10) need
*collapsed mixed shapes*: spectator blocks of arbitrary runtime size around the active digits
(`[OAI26, §2.1]` and Lemma 13 of `[OAI26]`). The contracts below are new definitions; the §3 contracts are unchanged.
Shapes are listed most significant first. Spectator sizes are runtime counters on named parameter
stacks, which are restored. The leading block size is implied by the array length. -/

/-- `n mod q` as an element of `Fin q`. -/
def modFin (q : ℕ) [NeZero q] (n : ℕ) : Fin q := ⟨n % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩

/-- (1, mixed) Address map of a fixed permutation `π` of the digit pair `(d1, d2)` in the shape
`[N0] × [q] × [N1] × [q] × [N2]`, address `(x0, d1, x1, d2, x2)`. -/
def pairPermMixAddr (q N1 N2 : ℕ) [NeZero q] (π : Equiv.Perm (Fin q × Fin q)) (x : ℕ) : ℕ :=
  let p := π (modFin q (x / (N2 * q * N1)), modFin q (x / N2))
  (((x / (N2 * q * N1 * q) * q + p.1.val) * N1 + x / (N2 * q) % N1) * q + p.2.val) * N2 + x % N2

/-- (2, mixed) Inverse address map of moving the digit `d` to the right across the block `x1`:
`[N0] × [q] × [N1] × [N2] → [N0] × [N1] × [q] × [N2]`, `(x0, d, x1, x2) ↦ (x0, x1, d, x2)`.
Output record `(x0, x1, d, x2)` is input record `(x0, d, x1, x2)`. -/
def moveRightMixInv (q N1 N2 : ℕ) (y : ℕ) : ℕ :=
  ((y / (N2 * q * N1) * q + y / N2 % q) * N1 + y / (N2 * q) % N1) * N2 + y % N2

/-- (2, mixed) Inverse address map of moving the digit `d` to the left across the block `x1`:
`[N0] × [N1] × [q] × [N2] → [N0] × [q] × [N1] × [N2]`, `(x0, x1, d, x2) ↦ (x0, d, x1, x2)`. -/
def moveLeftMixInv (q N1 N2 : ℕ) (y : ℕ) : ℕ :=
  ((y / (N2 * N1 * q) * N1 + y / N2 % N1) * q + y / (N2 * N1) % q) * N2 + y % N2

/-- (3, mixed) Split at the digit `c` of the shape `[N0] × [q] × [N1]`, apply a fixed pointwise
map `g` to the `q` aligned records, and merge. Records are lists of `B` data digits. Output record
`(x0, c, x1)` has data digit `t` equal to `g (fun c' => data digit t of input (x0, c', x1)) c`. -/
def splitMapMergeMix (q N1 : ℕ) [NeZero q] (g : (Fin q → ℕ) → Fin q → ℕ) (B : ℕ)
    (v : List (List ℕ)) : List (List ℕ) :=
  (List.range v.length).map fun x =>
    (List.range B).map fun t =>
      g (fun c' => (v.getD (x / (N1 * q) * (q * N1) + c'.val * N1 + x % N1) []).getD t 0)
        (modFin q (x / N1))

/-- (4, blocks) The rows of class `w` modulo `W`, in order, where row `r` is the block of records
`[r·s, (r+1)·s)`. -/
def roleBlocks {α : Type} (W w s : ℕ) (v : List α) : List α :=
  (List.range v.length).filterMap fun x => if x / s % W = w then v[x]? else none

/-- (4, blocks) Merge `W` streams of `g` rows of `s` records each, in the fixed class order `ord`:
round `t` emits row `t` of streams `ord 0, ord 1, …, ord (W - 1)`. -/
def mergeBlocks {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g s : ℕ) (us : Fin W → List α) :
    List α :=
  (List.range g).flatMap fun t =>
    (List.finRange W).flatMap fun c => ((us (ord c)).drop (t * s)).take s

/-- (Moreover, mixed rotation) Inverse address map of the controlled cyclic shift in the shape
`[np] × [Q1] × [n1] × [Q2] × [n2] × [Q] × [s]`, address `(p, c1, y1, c2, y2, u, z)`, with target
`u` and controls `c1, c2`. The record at target offset `u` moves to `(u + off c1 c2) mod Q`; all
other coordinates are fixed. -/
def rotCtlInvAddr (Q1 n1 Q2 n2 Q s : ℕ) (off : ℕ → ℕ → ℕ) (x : ℕ) : ℕ :=
  let f := x / (s * Q)
  f * (s * Q) + (x / s % Q + Q - off (f / (n2 * Q2 * n1) % Q1) (f / n2 % Q2) % Q) % Q * s + x % s

/-- (Moreover, mixed unit) Inverse address map of multiplying the target `t` by `a/d` mod `Q` in
the shape `[np] × [Q] × [s]`: the record at `(p, t, z)` moves to `(p, a·t·d⁻¹ mod Q, z)`. -/
def unitMixInvAddr (Q s a d : ℕ) (x : ℕ) : ℕ :=
  x / (s * Q) * (s * Q) + d * (x / s % Q) * ((a : ZMod Q)⁻¹).val % Q * s + x % s

/-- (Negation) Inverse address map of `t ↦ -t mod Q` in the shape `[np] × [Q] × [s]`: block `0`
is fixed, blocks `1, …, Q - 1` are reversed, and every block keeps its internal order. -/
def negMixInvAddr (Q s : ℕ) (x : ℕ) : ℕ :=
  x / (s * Q) * (s * Q) + (Q - x / s % Q) % Q * s + x % s

/-! ### Sanity checks of the mixed specifications (`decide`) -/

example : pairPermMixAddr 2 1 1 (Equiv.prodComm _ _) 1 = 2 := by decide
example : permByInv (moveRightMixInv 2 3 1) [0, 1, 2, 3, 4, 5] = [0, 3, 1, 4, 2, 5] := by decide
example : permByInv (moveLeftMixInv 2 3 1) [0, 3, 1, 4, 2, 5] = [0, 1, 2, 3, 4, 5] := by decide
example : splitMapMergeMix 2 1 (fun b c => if c.val = 0 then b 0 else (b 0 + b 1) % 2) 2
    [[1, 0], [1, 1]] = [[1, 0], [0, 1]] := by decide
example : roleBlocks 2 1 2 [10, 11, 12, 13, 14, 15] = [12, 13] := by decide
example : mergeBlocks 2 id 2 2 (fun w => roleBlocks 2 w.val 2 [10, 11, 12, 13, 14, 15, 16, 17]) =
    [10, 11, 12, 13, 14, 15, 16, 17] := by decide
example : permByInv (rotCtlInvAddr 2 1 1 1 2 1 (fun c1 _ => c1)) [0, 1, 2, 3] = [0, 1, 3, 2] := by
  decide
example : permByInv (negMixInvAddr 3 2) [0, 1, 2, 3, 4, 5] = [0, 1, 4, 5, 2, 3] := by decide

/-- **[CONTRACT] K1a-mix, fixed permutation of a digit pair in a mixed shape** (Lemma A.4(1),
`lem:transfer-streams`; `[OAI26, §2.1]`). Shape `[N0] × [q] × [N1] × [q] × [N2]`: `(x0, d1, x1, d2, x2)` moves to
`(x0, e1, x1, e2, x2)` with `(e1, e2) = π (d1, d2)`. Named stacks (`Fin 4`): `0` the source
(consumed), `1` the destination, `2`/`3` the counters `N1`, `N2` (restored). It generalizes
`K1PairPermStmt` (there `N0 = q^i`, `N1 = q^{j-i-1}`, `N2 = q^{k-1-j}` for `i < j`). Cost
`C·(V + 1)`. -/
def K1PairPermMixStmt (q : ℕ) [NeZero q] (π : Equiv.Perm (Fin q × Fin q)) : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (N0 N1 N2 : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      v.length = N0 * q * N1 * q * N2 → BlkTerm rest → TermOK r2 → TermOK r3 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms N1 ++ r2 →
      S (.inl 3) = natSyms N2 ++ r3 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (pairPermMixAddr q N1 N2 π.symm) v) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] K1b-mix, move a digit across a spectator block** (Lemma A.4(2); `[OAI26, §2.1]`).
With `toRight = true` the shape `[N0] × [q] × [N1] × [N2]` becomes `[N0] × [N1] × [q] × [N2]`,
`(x0, d, x1, x2) ↦ (x0, x1, d, x2)`. With `toRight = false` it is the inverse move. The direction
is a compile-time parameter. Named stacks (`Fin 4`): `0` the source (consumed), `1` the
destination, `2`/`3` the counters `N1`, `N2` (restored). Cost `C·(V + 1)`. -/
def K1MoveDigitMixStmt (q : ℕ) (toRight : Bool) : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (N0 N1 N2 : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      v.length = N0 * q * N1 * N2 → BlkTerm rest → TermOK r2 → TermOK r3 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms N1 ++ r2 →
      S (.inl 3) = natSyms N2 ++ r3 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv
            (if toRight then moveRightMixInv q N1 N2 else moveLeftMixInv q N1 N2) v)
            ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] K1c-mix, split, pointwise map, merge in a mixed shape** (Lemma A.4(3)). Shape
`[N0] × [q] × [N1]`, split at the middle digit. Records hold `B` data digits over `[A]`
(`digitRec A`). The output is `splitMapMergeMix q N1 g B v`. Named stacks (`Fin 3`): `0` the source
(consumed), `1` the destination, `2` the counter `N1` (restored). Cost `C·(V + 1)`. -/
def K1SplitMapMergeMixStmt (q : ℕ) [NeZero q] (A : ℕ) (g : (Fin q → ℕ) → Fin q → ℕ) : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (N0 N1 B : ℕ) (v : List (List ℕ)) (rest r2 : List Sym) (S : KLoc (Fin 3) E → List Sym),
      v.length = N0 * q * N1 → (∀ ds ∈ v, ds.length = B ∧ ∀ d ∈ ds, d < A) →
      (∀ (f : Fin q → ℕ) (c : Fin q), (∀ c', f c' < A) → g f c < A) →
      BlkTerm rest → TermOK r2 →
      S (.inl 0) = arrSyms (v.map (digitRec A)) ++ rest → S (.inl 2) = natSyms N1 ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms ((splitMapMergeMix q N1 g B v).map (digitRec A)) ++ S (.inl 1)))
        (fun _ => True) (C * (vol (v.map (digitRec A)) + 1))

/-- Final stacks of `K2DistributeBlkStmt`: the source becomes `rest`, the counter is unchanged, and
role stack `w` receives its rows `roleBlocks W w s v` (first record on top) on its old content. -/
def distBlkPost {W : ℕ} {E : Type} (s : ℕ) (v : List (List Bool)) (rest : List Sym)
    (S : KLoc (Fin 2 ⊕ Fin W) E → List Sym) : KLoc (Fin 2 ⊕ Fin W) E → List Sym := fun l =>
  match l with
  | .inl (.inl i) => if i = 0 then rest else S l
  | .inl (.inr w) => arrSyms (roleBlocks W w.val s v) ++ S l
  | .inr _ => S l

/-- **[CONTRACT] K2a-blk, cyclic distribution of block rows into `W` role streams** (Lemma A.4(4);
Proposition A.7 and Lemma A.10 rows are blocks). The array has `R·s` records, and row `r` is `[r·s, (r+1)·s)`.
Row `r` goes to stream `r mod W`, and each stream keeps the row order. Named stacks
(`Fin 2 ⊕ Fin W`): `inl 0` the source (consumed), `inl 1` the counter `s` (restored), `inr w` role
stack `w`. Cost `C·(V + 1)`. -/
def K2DistributeBlkStmt (W : ℕ) : Prop :=
  KContract (Fin 2 ⊕ Fin W) Unit fun _ E _ _ _ C P =>
    ∀ (R s : ℕ) (v : List (List Bool)) (rest r1 : List Sym)
      (S : KLoc (Fin 2 ⊕ Fin W) E → List Sym),
      v.length = R * s → BlkTerm rest → TermOK r1 →
      S (.inl (.inl 0)) = arrSyms v ++ rest → S (.inl (.inl 1)) = natSyms s ++ r1 →
      Runs P S (distBlkPost s v rest S) (fun _ => True) (C * (vol v + 1))

/-- Final stacks of `K2MergeBlkStmt`: every role stack `w` loses its block (leaving `rests w`), the
counter is unchanged, and the destination receives the merged rows on its old content. -/
def mergeBlkPost {W : ℕ} {E : Type} (ord : Fin W → Fin W) (g s : ℕ)
    (us : Fin W → List (List Bool)) (rests : Fin W → List Sym)
    (S : KLoc (Fin 2 ⊕ Fin W) E → List Sym) : KLoc (Fin 2 ⊕ Fin W) E → List Sym := fun l =>
  match l with
  | .inl (.inl i) => if i = 0 then arrSyms (mergeBlocks W ord g s us) ++ S l else S l
  | .inl (.inr w) => rests w
  | .inr _ => S l

/-- **[CONTRACT] K2b-blk, merge `W` streams of block rows in a fixed class order** (Lemma A.4(4)). Role
stack `w` holds `g` rows of `s` records (consumed). The output is `mergeBlocks W ord g s us`. With
`ord = id` this inverts `K2DistributeBlkStmt` on `W·g` rows. Named stacks (`Fin 2 ⊕ Fin W`):
`inl 0` the destination, `inl 1` the counter `s` (restored), `inr w` role stack `w`. Cost
`C·(V + 1)`, where `V` is the total volume of the role streams. -/
def K2MergeBlkStmt (W : ℕ) (ord : Equiv.Perm (Fin W)) : Prop :=
  KContract (Fin 2 ⊕ Fin W) Unit fun _ E _ _ _ C P =>
    ∀ (g s : ℕ) (us : Fin W → List (List Bool)) (rests : Fin W → List Sym) (r1 : List Sym)
      (S : KLoc (Fin 2 ⊕ Fin W) E → List Sym),
      (∀ w, (us w).length = g * s) → (∀ w, BlkTerm (rests w)) → TermOK r1 →
      (∀ w, S (.inl (.inr w)) = arrSyms (us w) ++ rests w) →
      S (.inl (.inl 1)) = natSyms s ++ r1 →
      Runs P S (mergeBlkPost ord g s us rests S) (fun _ => True)
        (C * (((List.finRange W).map fun w => vol (us w)).sum + 1))

/-- **[CONTRACT] Premise of K4-ctl: the two-control offset routine** (Lemma A.4, `lem:transfer-streams`). Named stacks
(`Fin 4`): `0` the counter `b`, `1`/`2` the controls `c1`, `c2` (all restored), `3` the
destination, which receives `natSyms (off b c1 c2)`. Cost `C·(b + bitLen c1 + bitLen c2 + 1)^J`. -/
def K4OffsetCtlStmt (off : ℕ → ℕ → ℕ → ℕ) (J : ℕ) : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (b c1 c2 : ℕ) (r0 r1 r2 : List Sym) (S : KLoc (Fin 4) E → List Sym),
      TermOK r0 → TermOK r1 → TermOK r2 →
      S (.inl 0) = natSyms b ++ r0 → S (.inl 1) = natSyms c1 ++ r1 →
      S (.inl 2) = natSyms c2 ++ r2 →
      Runs P S (Function.update S (.inl 3) (natSyms (off b c1 c2) ++ S (.inl 3)))
        (fun _ => True) (C * (b + bitLen c1 + bitLen c2 + 1) ^ J)

/-- **[CONTRACT] K4-ctl, controlled cyclic shift with two control blocks in a mixed shape**
(Lemma A.4, `lem:transfer-streams`; Lemma A.6 uses one control block, Lemma A.9 two). Shape
`[np] × [q^{b1}] × [n1] × [q^{b2}] × [n2] × [q^b] × [s]`, address `(p, c1, y1, c2, y2, u, z)`. The
record at target offset `u` moves to `(u + off b c1 c2) mod q^b`; all other coordinates are fixed
(`rotCtlInvAddr`). Explicit premises: `q ≥ 2`; an offset routine (`K4OffsetCtlStmt off J`);
reduced offsets `off b c1 c2 < q^b` (as in `K4RotateStmt`); controls with `O(b)` digits
(`b1, b2 ≤ cb·b`). `np, n1, n2, s` are arbitrary. One control block is the case `b2 = 0`,
`n2 = 1`. Named stacks (`Fin 8`): `0` the source (consumed), `1` the destination, `2`-`7` the
counters `b1, n1, b2, n2, b, s` (restored). Cost `C·(V + 1)`. -/
def K4RotateCtlStmt (q cb J : ℕ) (off : ℕ → ℕ → ℕ → ℕ) : Prop :=
  2 ≤ q → K4OffsetCtlStmt off J → (∀ b c1 c2, off b c1 c2 < q ^ b) →
  KContract (Fin 8) Unit fun _ E _ _ _ C P =>
    ∀ (np b1 n1 b2 n2 b s : ℕ) (v : List (List Bool)) (rest r2 r3 r4 r5 r6 r7 : List Sym)
      (S : KLoc (Fin 8) E → List Sym),
      v.length = np * q ^ b1 * n1 * q ^ b2 * n2 * q ^ b * s → b1 ≤ cb * b → b2 ≤ cb * b →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 →
      S (.inl 0) = arrSyms v ++ rest →
      S (.inl 2) = natSyms b1 ++ r2 → S (.inl 3) = natSyms n1 ++ r3 →
      S (.inl 4) = natSyms b2 ++ r4 → S (.inl 5) = natSyms n2 ++ r5 →
      S (.inl 6) = natSyms b ++ r6 → S (.inl 7) = natSyms s ++ r7 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (rotCtlInvAddr (q ^ b1) n1 (q ^ b2) n2 (q ^ b) s (off b)) v)
            ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] K5-mix, multiplication of the target by a fixed rational unit `a/d` mod `q^b` in
a mixed shape** (Lemma A.4, `lem:transfer-streams`). Shape `[np] × [q^b] × [s]`: the record at
`(p, t, z)` moves to `(p, a·t·d⁻¹ mod q^b, z)` (`unitMixInvAddr`). `a, d` are fixed, positive in
`ℕ` and coprime to `q`. Named stacks (`Fin 4`): `0` the source (consumed), `1` the destination,
`2`/`3` the counters `b`, `s` (restored). It generalizes `K5UnitMulStmt` (`s = 1`). Cost
`C·(V + 1)`. -/
def K5UnitMulMixStmt (q a d : ℕ) : Prop :=
  Nat.Coprime a q → Nat.Coprime d q →
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (np b s : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      v.length = np * q ^ b * s → BlkTerm rest → TermOK r2 → TermOK r3 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms b ++ r2 →
      S (.inl 3) = natSyms s ++ r3 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (unitMixInvAddr (q ^ b) s a d) v) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] K5-neg, negation of the target mod `q^b` in a mixed shape** (Lemma A.4,
`lem:transfer-streams`; `[OAI26, proof of Lemma 4, §2.1]`). Shape `[np] × [q^b] × [s]`: `(p, t, z)` moves to
`(p, -t mod q^b, z)` (`negMixInvAddr`). In each fiber, block `0` stays, blocks `1, …, q^b - 1` are
reversed, and every block keeps its internal order. With `K5UnitMulMixStmt` it covers negative
units. Named stacks (`Fin 4`): `0` the source (consumed), `1` the destination, `2`/`3` the counters
`b`, `s` (restored). Cost `C·(V + 1)`. -/
def K5NegStmt (q : ℕ) : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (np b s : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      v.length = np * q ^ b * s → BlkTerm rest → TermOK r2 → TermOK r3 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms b ++ r2 →
      S (.inl 3) = natSyms s ++ r3 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (negMixInvAddr (q ^ b) s) v) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))
end SubNLogN.Machine
