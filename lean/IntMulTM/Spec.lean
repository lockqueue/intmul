import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding

/-!
# Specification: `O(n log n)` integer multiplication on a multi-stack Turing machine

Top-level specification for our independent `O(n log n)` multitape Turing-machine formalization of the two-dimensional multiplier of `[MS]`.
This module contains no `sorry` or non-standard axioms.

Stated for Lean v4.33.1 and Mathlib `0df444a3` (Aug 2026). Relative to Lean v4.27.0,
Mathlib's computability API changed
since the v4.27.0 original: `Computability.Encoding` now takes its alphabet as a parameter,
`FinEncoding` survives only as a deprecated alias of a different shape, and
`Turing.TM2ComputableInTime` takes encoding *functions*. The statement is otherwise unchanged: same
machine model, same encodings, same time bound.

## Model

Mathlib's `Turing.FinTM2`, bundled as `Turing.TM2ComputableInTime`: finitely many stacks, a finite
label set, a finite internal state. Time is the number of `Turing.FinTM2.step` calls. One step runs
one label's statement, which is a bounded (program-dependent) number of pushes, pops and state
updates.

`Turing.FinTM2` only requires the *input* stack alphabet to be finite. The acceptance statement
below additionally requires every stack alphabet to be finite, so that no reader has to rely on the
argument that only finitely many symbols can ever be pushed.

## The only modeling convention

A machine with `k` stacks over finite alphabets and a multitape Turing machine simulate each other
with `O(1)` slowdown (two stacks make one tape; one tape holds one stack). So TM2 time with finite
alphabets is multitape-TM time up to constant factors, which is the model of Schönhage–Strassen,
Fürer and Harvey–van der Hoeven.

## Encodings

* Input: `encodeNatPair (a, b) = bits(a) ++ [sep] ++ bits(b)` over the 3-symbol alphabet `PairSym`,
  where `bits` is Mathlib's little-endian binary `Computability.encodeNat` (no leading zeros,
  `0 ↦ []`).
* Output: Mathlib's `Computability.encodeNat`, the same binary code over `Bool`.

Time is measured in the input length `L = |bits a| + |bits b| + 1`, so `n`-bit operands give
`L ≤ 2n + 1`. A bound `C · L · log₂ L` is therefore the usual `O(n log n)` bound.
-/

namespace IntMulTM

open Computability

/-- Input alphabet: a bit, or the separator between the two operands. -/
inductive PairSym
  | bit (b : Bool)
  | sep
  deriving DecidableEq, Fintype

/-- Read a bit back (the separator has none). -/
def PairSym.toBool? : PairSym → Option Bool
  | .bit b => some b
  | .sep => none

/-- `encodeNatPair (a, b) = bits(a) ++ sep :: bits(b)`, with Mathlib's little-endian `encodeNat`. -/
def encodeNatPair (p : ℕ × ℕ) : List PairSym :=
  (encodeNat p.1).map PairSym.bit ++ PairSym.sep :: (encodeNat p.2).map PairSym.bit

/-- Split a word at its first separator. -/
def splitSep : List PairSym → Option (List Bool × List Bool)
  | [] => none
  | .sep :: rest => some ([], rest.filterMap PairSym.toBool?)
  | .bit b :: rest => (splitSep rest).map fun xy => (b :: xy.1, xy.2)

/-- Decoder for `encodeNatPair`. -/
def decodeNatPair (l : List PairSym) : Option (ℕ × ℕ) :=
  (splitSep l).map fun xy => (decodeNat xy.1, decodeNat xy.2)

theorem filterMap_toBool?_map_bit (R : List Bool) :
    (R.map PairSym.bit).filterMap PairSym.toBool? = R := by
  induction R with
  | nil => rfl
  | cons b R ih => simp [PairSym.toBool?, ih]

theorem splitSep_append (L R : List Bool) :
    splitSep (L.map PairSym.bit ++ PairSym.sep :: R.map PairSym.bit) = some (L, R) := by
  induction L with
  | nil => simp only [List.map_nil, List.nil_append, splitSep, filterMap_toBool?_map_bit]
  | cons b L ih => simp [splitSep, ih]

theorem decodeNatPair_encodeNatPair (p : ℕ × ℕ) :
    decodeNatPair (encodeNatPair p) = some p := by
  simp [decodeNatPair, encodeNatPair, splitSep_append, decode_encodeNat]

/-- The input encoding as a Mathlib `Encoding`: binary `a`, separator, binary `b`, over the
3-symbol alphabet `PairSym`. -/
def encNatPair : Encoding (ℕ × ℕ) PairSym where
  encode := encodeNatPair
  decode := decodeNatPair
  decode_encode := decodeNatPair_encodeNatPair

theorem encNatPair_encode_length (a b : ℕ) :
    (encNatPair.encode (a, b)).length = (encodeNat a).length + (encodeNat b).length + 1 := by
  simp [encNatPair, encodeNatPair]
  omega

/-- **Acceptance statement.** Some multi-stack Turing machine with finite alphabets maps
`encodeNatPair (a, b)` to the binary code of `a * b`, and on every input of length `L ≥ N₀` it halts
(with all work stacks empty, as `Turing.haltList` demands) within `C · L · log₂ L` steps. -/
def IntMulNLogN : Prop :=
  ∃ M : Turing.TM2ComputableInTime encNatPair.encode encodingNatBool.encode
      (fun p : ℕ × ℕ => p.1 * p.2),
    (∀ k, Finite (M.tm.Γ k)) ∧
    ∃ C N₀ : ℕ, ∀ L ≥ N₀, M.time L ≤ C * L * Nat.log2 L

/-! ### Sanity checks on the encoding -/

theorem encNatPair_encode_eq (p : ℕ × ℕ) : encNatPair.encode p = encodeNatPair p := rfl

-- Evaluated tests (they produce no proof terms and add no axioms).
#guard encodeNatPair (5, 3) == [.bit true, .bit false, .bit true, .sep, .bit true, .bit true]
#guard encodeNatPair (0, 0) == [.sep]
#guard decodeNatPair [.bit false, .bit true, .sep, .bit true] == some (2, 1)
#guard decodeNatPair (encodeNatPair (123456789, 987654321)) == some (123456789, 987654321)
#guard encodeNat 6 == [false, true, true]

end IntMulTM
