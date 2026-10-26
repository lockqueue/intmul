/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.FFT
import SubNLogN.Machine.Contracts.Arith
import SubNLogN.Math.Walsh.Proofs.LayoutPerm

/-!
# K4-PREFIX, definitions (`Machine/FFT/PrefixDefs.lean`)

Definitions for the prefix-round kernel (`PrefixRoundStmt`, `Contracts/FFT.lean:239`; Theorem 6.5,
`thm:direct-fft`, Section 6.4: exact individual butterflies followed by one truncation `Q_q`).

**Design.** For a prefix round (`v = ℓ - 1` or `v < b₀`), `roundSet ℓ K a v` is a block of
consecutive address positions `[s, s + n)` (`pfS`, `pfN`). With `cubeOfNat` (position `0` = most
significant index bit), these are the record-index bits `L, …, L + n - 1`, `L = m₀ - s - n`.
`H_T` is then `n` exact butterfly passes, one per bit (`bpass`, iterated by `bflyIter`).

The pass with half-blocks of `h` records works on `M` block pairs:
* the even blocks `bev h M B` (records `2jh, …, 2jh + h - 1`) and the odd blocks `bod h M B`
  (records `2jh + h, …, 2jh + 2h - 1`);
* the exact sums `zipC caddC` and differences `zipC csubC` of the two;
* the blockwise interleave `bint h M` of the sums and the differences.

No `sorry`: this file only contains definitions.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- Even `h`-blocks of `2hM` records: block `j` is records `2jh, …, 2jh + h - 1`. -/
def bev {α : Type} (h M : ℕ) (B : List α) : List α :=
  (List.range M).flatMap fun j => (B.drop (2 * j * h)).take h

/-- Odd `h`-blocks of `2hM` records: block `j` is records `2jh + h, …, 2jh + 2h - 1`. -/
def bod {α : Type} (h M : ℕ) (B : List α) : List α :=
  (List.range M).flatMap fun j => (B.drop (2 * j * h + h)).take h

/-- Blockwise interleave: `X`-block `j` (records `jh, …, jh + h - 1` of `X`), then `Y`-block `j`,
for `j < M`. -/
def bint {α : Type} (h M : ℕ) (X Y : List α) : List α :=
  (List.range M).flatMap fun j => (X.drop (j * h)).take h ++ (Y.drop (j * h)).take h

/-- One exact butterfly pass with half-blocks of `h` records and `M` block pairs: in every pair
`(A, B)` the records become `A + B` (first half) and `A - B` (second half), coefficientwise and
exactly. -/
def bpass (h M : ℕ) (B : List (List CInt)) : List (List CInt) :=
  bint h M (zipC caddC (bev h M B) (bod h M B)) (zipC csubC (bev h M B) (bod h M B))

/-- Exact butterfly passes on the index bits `L, L + 1, …, L + j - 1` of a `2^m`-record array. -/
def bflyIter (m L : ℕ) : ℕ → List (List CInt) → List (List CInt)
  | 0, B => B
  | j + 1, B => bpass (2 ^ (L + j)) (2 ^ (m - L - j - 1)) (bflyIter m L j B)

/-- The address positions `s, …, s + n - 1` of an `m`-bit cube. -/
def posBlock (m s n : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun p => s ≤ (p : ℕ) ∧ (p : ℕ) < s + n

/-- First position of `roundSet ℓ K a v` for a prefix round: `0` for `v = ℓ - 1`, and
`n_long + (b₀ - 1 - v)·D` for `v < b₀`. -/
def pfS {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) : ℕ :=
  if v + 1 = ℓ then 0 else LayoutPermAux.nLong ℓ a + (layoutB0 ℓ K - 1 - v) * D

/-- Size of `roundSet ℓ K a v` for a prefix round: `n_long = #{i | a_i = ℓ}` for `v = ℓ - 1`, and
`D` for `v < b₀`. -/
def pfN {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) : ℕ :=
  if v + 1 = ℓ then LayoutPermAux.nLong ℓ a else D

/-- The factor `Y` of the number `L = D·Y` of index bits below the block `roundSet ℓ K a v`:
`Y = ℓ - 1` for `v = ℓ - 1`, and `Y = ℓ - 1 - b₀ + v` for `v < b₀`. Under `MidShapeOK`,
`L = D·pfY ℓ K v = m₀ - pfS - pfN` (`pf_bound`, `Machine/FFT/PrefixFacts.lean`). -/
def pfY (ℓ K v : ℕ) : ℕ := if v + 1 = ℓ then ℓ - 1 else ℓ - 1 - layoutB0 ℓ K + v

end SubNLogN.Machine.FFT.PrefixAux
