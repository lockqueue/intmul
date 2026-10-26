/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams
import SubNLogN.Spec
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `SubNLogN.Machine` contracts, K2.3 (`Contracts/AppC.lean`): Appendix A interchanges and packed addition

**Scope (honest summary).** This file contains contract *statements* (`def … : Prop`) and pure
index specifications, with `decide` sanity checks; no kernel is implemented or proved here.
(`AppC` and `C5`/`C6`/`C7`/`c7` are historical names from an earlier draft for Appendix A.2–A.4):
* Proposition A.7 (`prop:transfer11`): power-width interchange in time `O(V e^τ)`;
* Lemma A.8 (`lem:transfer12`): arbitrary-width interchange in time `O(V u^τ)`;
* Lemma A.9 (`lem:transfer13`): packed selected-bit addition with deterministic repair.

Lemma A.6 (`lem:transfer-shear`) has no separate contract. Its machine content is the
lower-triangular streaming maps (`K4RotateCtlStmt`, `K5UnitMulMixStmt` and `K5NegStmt` in
`Streams.lean` §5) plus one child interchange per pivot. Inside Proposition A.7 that child is a
recursive call rather than a closed kernel; Lemma A.10 (`lem:transfer-phase`) is in `CCore.lean`.

## Conventions (decisions recorded here)
* **Data.** Arrays are stored in lexicographic address order as `recSyms` records, addresses
  implicit (`Streams.lean` §1). All records have one fixed width `w` (`∀ p ∈ v, p.length = w`).
  Interchanges combine records bitwise (XOR), so payloads must be fixed-width bit strings of
  uniform length `w`. Otherwise payloads are arbitrary: the functional part is a pure permutation.
* **Shapes.** Collapsed mixed shapes, most significant field first, as in `Streams.lean` §5. Sizes
  are runtime counters (`natSyms`) on named stacks, which are restored. The leading block size is
  implied by the length.
* **In place.** Named stack `0` holds the array followed by a `BlkTerm` tail and is updated in
  place.
* **Restored convention.** Every other named stack and every private scratch stack (`KLoc`) is
  unchanged at exit and may hold arbitrary content at entry. The private scratch contains the role
  stacks, the parking stack and the descriptor stack of Proposition A.7 (`prop:transfer11`). A
  recursive proof goes through a framed variant with frame tails, as `CCoreStmt` is stated; the
  wrapper pushes and pops one `mark` per private stack.
* **Fixed constants.** These are fixed before the cost constant `C`: the radix `q` of Proposition A.7
  (the prime `q_rad` of `lem:transfer-shear`), the exponent `τ` with `s_b/W_b < m^τ` (a premise), and
  the chunk-name arrangement `σ` of Lemma A.9. (`KContract` has `∃ C` before runtime quantifiers.)
* **Network premises.** The bit-network facts and the choice of `q` are hypotheses of the eventual
  theorems, not of these statements.
* **Functional targets.** The address maps agree with the math-layer `Model.Step.swapBlocks`
  (`Math/Networks/AppCModel.lean`) and with the ideal map of `packedT0` (`AppCShear.lean`) on the
  corresponding layouts. That correspondence is not proved here.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-! ## Pure index specifications -/

/-- **Field interchange across a spectator field.** This is the inverse address map of
`[A] × [Hh] × [G] × [Hd] × [B] → [A] × [Hd] × [G] × [Hh] × [B]`, `(a, h, g, d, z) ↦ (a, d, g, h, z)`:
output record `(a, d, g, h, z)` is input record `(a, h, g, d, z)`. The prefix size `A` is implied. -/
def swapFieldsInv (Hh G Hd B : ℕ) (y : ℕ) : ℕ :=
  (((y / (B * Hh * G * Hd) * Hh + y / B % Hh) * G + y / (B * Hh) % G) * Hd +
    y / (B * Hh * G) % Hd) * B + y % B

/-- Strides of the three chunk slots of the Lemma A.9 (`lem:transfer13`) rectangle
`[N0] × [2^L] × [N1] × [2^L] × [N2] × [2^L] × [N3]` (slot `0` most significant). -/
def c7Stride (L N1 N2 N3 : ℕ) (j : Fin 3) : ℕ :=
  if j.val = 0 then N3 * 2 ^ L * N2 * 2 ^ L * N1 else if j.val = 1 then N3 * 2 ^ L * N2 else N3

/-- Value of chunk slot `j` at record index `x`. -/
def c7Slot (L N1 N2 N3 : ℕ) (j : Fin 3) (x : ℕ) : ℕ := x / c7Stride L N1 N2 N3 j % 2 ^ L

/-- The selected bits `ρ + iK` (`i < f`) of `xv`, kept at their positions. -/
def selMask (K ρ f xv : ℕ) : ℕ :=
  ∑ i ∈ Finset.range f, 2 ^ (ρ + i * K) * (xv / 2 ^ (ρ + i * K) % 2)

/-- **Packed selected-bit addition** (Lemma A.9, `lem:transfer13`). This is the address map of
`y_{ρ+iK} ← y_{ρ+iK} ⊕ x_{ρ+iK}` for `0 ≤ i < f` on the Lemma A.9 rectangle with `L = f·K`. Slot `j`
holds the chunk named `σ j` (`0 = x`, `1 = y`, `2 = z`). All other address bits are unchanged, in
particular the auxiliary chunk `z`. On slot values this is the ideal map `packedT0` extended to
all `f` selected bits (`packedT0` itself covers `i < f - 1`). The map is an involution, so it is
also its own inverse address map. -/
def packedXorAddr (L K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (x : ℕ) : ℕ :=
  x - c7Slot L N1 N2 N3 (σ.symm 1) x * c7Stride L N1 N2 N3 (σ.symm 1) +
    Nat.xor (c7Slot L N1 N2 N3 (σ.symm 1) x) (selMask K ρ f (c7Slot L N1 N2 N3 (σ.symm 0) x)) *
      c7Stride L N1 N2 N3 (σ.symm 1)

/-! ### Sanity checks (`decide`; `Nat.xor` is well-founded, so `packedXorAddr` is not checked) -/

example : permByInv (swapFieldsInv 2 1 2 1) [0, 1, 2, 3] = [0, 2, 1, 3] := by decide
example : permByInv (swapFieldsInv 4 1 2 1) [0, 1, 2, 3, 4, 5, 6, 7] = [0, 2, 4, 6, 1, 3, 5, 7] := by
  decide
example : permByInv (swapFieldsInv 2 2 2 1) [0, 1, 2, 3, 4, 5, 6, 7] = [0, 4, 2, 6, 1, 5, 3, 7] := by
  decide
example : c7Slot 1 1 1 1 0 5 = 1 ∧ c7Slot 1 1 1 1 1 5 = 0 ∧ c7Slot 1 1 1 1 2 5 = 1 := by decide
example : selMask 3 1 2 0b111111 = 0b010010 := by decide

/-! ## Proposition A.7 (`prop:transfer11`): power-width interchange -/

/-- **[CONTRACT] Parameterized power-width interchange** (Proposition A.7, `prop:transfer11`).
* Shape `[N0] × [R] × [N1] × [q^e] × [G] × [q^e] × [B]` with `e = m^k` (`m = tripleM 100`) and all
  sizes `≥ 1`. The row field `[R]` precedes both chunks and `W_b^k ∣ R` (`W_b = tripleWb 100`).
* Effect: the two chunks of `e` radix-`q` digits are interchanged, `(…, h, g, d, z) ↦ (…, d, g, h, z)`
  (`swapFieldsInv (q^e) G (q^e) B`). All other fields and all payloads are preserved.
* Records have one fixed width `w`; the data is arbitrary.
* Named stacks (`Fin 6`): `0` the array (in place); `1`-`5` the counters `k, R, N1, G, B`
  (restored).
* Premise: `s_b/W_b < m^τ`. Cost `C·(⌈V·e^τ⌉₊ + 1)`, uniform in all field lengths and data.
The statement is meant for the prime `q = q_rad` of Lemma A.6 (`lem:transfer-shear`, an odd prime
avoiding the denominators of the fixed factorizations). The base case `k = 0` is one digit-pair
interchange (`K1PairPermMixStmt`). -/
def C5InterchangeStmt (q : ℕ) (τ : ℝ) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
  KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (k N0 R N1 G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 r5 : List Sym)
      (S : KLoc (Fin 6) E → List Sym),
      1 ≤ N0 → 1 ≤ R → 1 ≤ N1 → 1 ≤ G → 1 ≤ B → tripleWb 100 ^ k ∣ R →
      v.length = N0 * R * N1 * q ^ (tripleM 100 ^ k) * G * q ^ (tripleM 100 ^ k) * B →
      (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms k ++ r1 →
      S (.inl 2) = natSyms R ++ r2 → S (.inl 3) = natSyms N1 ++ r3 →
      S (.inl 4) = natSyms G ++ r4 → S (.inl 5) = natSyms B ++ r5 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv
            (swapFieldsInv (q ^ (tripleM 100 ^ k)) G (q ^ (tripleM 100 ^ k)) B) v) ++ rest))
        (fun _ => True)
        (C * (⌈(vol v : ℝ) * ((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊ + 1))

/-! ## Lemma A.8 (`lem:transfer12`): arbitrary-width interchange -/

/-- **[CONTRACT] Parameterized arbitrary-width interchange** (Lemma A.8,
`lem:transfer12`).
* Shape `[A] × [2^{u1}] × [G] × [2^{u2}] × [B]` with `u1, u2 ≥ 1`, `|u1 - u2| ≤ 1` and
  `A, G, B ≥ 1` (`B = 1` is allowed).
* Effect: the two binary fields are interchanged across `[G]`, `(a, h, g, d, z) ↦ (a, d, g, h, z)`
  (`swapFieldsInv (2^{u1}) G (2^{u2}) B`). Equal widths are the main case of `lem:transfer12`; widths
  differing by one bit are its final clause, which covers the bridge's axis exposures.
* Records have one fixed width `w`; the data is arbitrary.
* Named stacks (`Fin 6`): `0` the array (in place); `1`-`5` the counters `u1, u2, G, B, w`
  (restored). `w` is supplied because the padding records have width `w`.
* Premise: `s_b/W_b < m^τ`. Cost `C·(⌈V·u^τ⌉₊ + 1)` with `u = max u1 u2`, including shape
  processing, padding, unpadding and cleanup.
Internally the proof pads binary ranges into radix `q_rad`, invokes Proposition A.7 (`prop:transfer11`)
above an explicit size threshold with row and coordinate padding, and removes all padded entries
before returning; none of these internal steps appears in the external contract statement. -/
def C6InterchangeStmt (τ : ℝ) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
  KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (A u1 u2 G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 r5 : List Sym)
      (S : KLoc (Fin 6) E → List Sym),
      1 ≤ u1 → 1 ≤ u2 → u1 ≤ u2 + 1 → u2 ≤ u1 + 1 → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * 2 ^ u1 * G * 2 ^ u2 * B → (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms u1 ++ r1 →
      S (.inl 2) = natSyms u2 ++ r2 → S (.inl 3) = natSyms G ++ r3 →
      S (.inl 4) = natSyms B ++ r4 → S (.inl 5) = natSyms w ++ r5 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (swapFieldsInv (2 ^ u1) G (2 ^ u2) B) v) ++ rest))
        (fun _ => True) (C * (⌈(vol v : ℝ) * ((max u1 u2 : ℕ) : ℝ) ^ τ⌉₊ + 1))

/-! ## Lemma A.9 (`lem:transfer13`): packed selected-bit addition -/

/-- `A = ⌈lg 2V⌉`, the integer bit-width of addresses and ranks for a stream of volume `V`
(Lemma A.9, `lem:transfer13`). -/
def lgVol (V : ℕ) : ℕ := Nat.clog 2 (2 * V)

/-- The exceptional-set bound `min(M, ⌊80(f-1)M / 2^K⌋)` (Lemma A.9, `lem:transfer13`; `PackedBadCardStmt`). -/
def badMax (K f M : ℕ) : ℕ := min M (80 * (f - 1) * M / 2 ^ K)

/-- **Cost bound of Lemma A.9 (`lem:transfer13`)** (eq. `eq:transfer-packed`):
`⌈V(L^τ + 1)⌉₊ + M(A+1)^3 + badMax·A·(R + A + 2)`, with `L = fK`, `M` records, `V` the stack
volume, `R` the record width and `A = lgVol V`. The factors `(A+1)^3` and `R + A + 2` include
explicit `+ 1` / `+ 2` slack for degenerate zero-width edge cases. -/
noncomputable def c7Cost (τ : ℝ) (K f M V R : ℕ) : ℕ :=
  ⌈(V : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ + M * (lgVol V + 1) ^ 3 +
    badMax K f M * lgVol V * (R + lgVol V + 2)

/-- **[CONTRACT] Parameterized packed selected-bit addition** (Lemma A.9,
`lem:transfer13`).
* Shape: records of `R ≥ 1` bits on `[N0] × [2^L] × [N1] × [2^L] × [N2] × [2^L] × [N3]` with
  `L = f·K`, `K ≥ 6`, `f ≥ 1`, `ρ < K` and `N0, …, N3 ≥ 1`. Slot `j` holds the chunk named `σ j`
  (`0 = x`, `1 = y`, `2 = z`). The arrangement `σ` is fixed.
* Effect: `y_{ρ+iK} ← y_{ρ+iK} ⊕ x_{ρ+iK}` for `0 ≤ i < f` (`packedXorAddr`). Every other address
  bit and every payload is preserved, and the auxiliary chunk `z` is restored for every initial
  value.
* Named stacks (`Fin 8`): `0` the array (in place); `1`-`7` the counters `K, ρ, f, N1, N2, N3, R`
  (restored).
* Premise: `s_b/W_b < m^τ`. Cost `C · c7Cost τ K f M V R`.
The deterministic repair phase is realized sequentially on stacks via tagged holes, a stable radix
sort by destination rank, and a forward reinsertion scan (Appendix A.4). Under `(A+1)^3 ≤ R` and
`160(f-1)(A+1) ≤ 2^K`, the total cost simplifies to `O(V(L^τ + 1))`. -/
def C7PackedXorStmt (τ : ℝ) (σ : Equiv.Perm (Fin 3)) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
  KContract (Fin 8) Unit fun _ E _ _ _ C P =>
    ∀ (K ρ f N0 N1 N2 N3 R : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 r5 r6 r7 : List Sym)
      (S : KLoc (Fin 8) E → List Sym),
      6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 → 1 ≤ R →
      v.length = N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 →
      (∀ p ∈ v, p.length = R) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
      TermOK r6 → TermOK r7 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms K ++ r1 →
      S (.inl 2) = natSyms ρ ++ r2 → S (.inl 3) = natSyms f ++ r3 →
      S (.inl 4) = natSyms N1 ++ r4 → S (.inl 5) = natSyms N2 ++ r5 →
      S (.inl 6) = natSyms N3 ++ r6 → S (.inl 7) = natSyms R ++ r7 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (packedXorAddr (f * K) K ρ f N1 N2 N3 σ) v) ++ rest))
        (fun _ => True) (C * c7Cost τ K f v.length (vol v) R)
end SubNLogN.Machine
