/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Walsh
import SubNLogN.Math.Walsh.Identities

/-!
# K3-PERM (`Machine/Walsh/CnotLeaf.lean`): leaf contracts of the CNOT-batch reduction

**Scope (honest summary).** Statements only (`def … : Prop`), no proofs: the two leaf kernels used by
`cnotBatchMachine_of` (`Machine/Walsh/CnotBatch.lean`) besides the contracts of
`Contracts/Walsh.lean`. They are kept in this small file so that their implementations can import
them without the reduction.
* `CnotHdrStmt` — the header builder of a batch (Lemma 5.3, Proposition 5.5).
* `CnotScanStmt mode` — the recordwise scans of a lifted batch array: `S_U` (`selPhase`), `CZ`
  (`cz`), the selective scalar (`selScalar`), the final `×2^s` (`shift`) (Lemma 5.1, Proposition 5.5).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## Leaf contracts -/

/-- **[LEAF CONTRACT] K3.4a, header builder of a CNOT batch** (Lemma 5.3 (`lem:walsh-lift`):
`P_* = P + 8d`, `w_* = w + 8d`; the batch procedure of Proposition 5.5 (`prop:cnot-batch`)).
* Named stacks (`Fin 3`): `0` the slice header `sliceHdr P d r w K m j₀ D nS ρ` (restored; the
  header has ten fields, so nothing is assumed below it), `1` receives the lift/lowering header
  `hdrSyms [w, 8d]` on top of its content, `2` receives the lifted slice header
  `sliceHdr (P + 8d) d r (w + 8d) K m j₀ D nS ρ` on top of its content.
* Every other stack is restored; private scratch clean on entry (`KClean`).
* Cost `C·(|sliceHdr| + 1)`: one read of the header, binary `8d`, `P + 8d`, `w + 8d` (linear in
  the field lengths), and the outputs, whose lengths are `O(|sliceHdr|)`. -/
def CnotHdrStmt : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r w K m j₀ D nS ρ : ℕ) (hrest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → S (.inl 0) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      Runs Pr S
        (Function.update (Function.update S (.inl 1) (hdrSyms [w, 8 * d] ++ S (.inl 1)))
          (.inl 2) (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ ++ S (.inl 2)))
        (fun _ => True) (C * ((sliceHdr P d r w K m j₀ D nS ρ).length + 1))

/-- The four recordwise scans of a CNOT batch (Lemma 5.1 (`lem:walsh-select`), Proposition 5.5 (`prop:cnot-batch`)). -/
inductive CnotScanMode : Type
  /-- the diagonal `S_U`, `U = Sel ∖ T` (eq. (`eq:walsh-SU`)) -/
  | selPhase
  /-- the sign diagonal `CZ` of the pairs (eq. (`eq:walsh-CZ`)) -/
  | cz
  /-- the selective scalar `2^s [2(1-i)]^{q_sel}` (Lemma 5.1) -/
  | selScalar
  /-- the final multiplication by `2^s` (Lemma 5.4) -/
  | shift
  deriving DecidableEq

/-- The array map of a scan (`Sel = slicePos m K j₀ D ρ`, `T = targets pairs`, `U = Sel ∖ T`,
`s = |T|`, `q_sel = |U|`; for `shift`, `s = |pairs|`). -/
noncomputable def cnotScanMap {m r : ℕ} (K j₀ D ρ : ℕ) (pairs : List (Fin m × Fin m)) :
    CnotScanMode → RArr (Cube m) r → RArr (Cube m) r
  | .selPhase => sDiag (slicePos m K j₀ D ρ \ targets pairs)
  | .cz => diagArr (czSign pairs)
  | .selScalar =>
      scaleArr (selScalar (targets pairs).card (slicePos m K j₀ D ρ \ targets pairs).card)
  | .shift => scaleArr (2 ^ pairs.length)

/-- **[LEAF CONTRACT] K3.4b, one recordwise scan of a lifted CNOT-batch array**
(Lemma 5.1 (`lem:walsh-select`) for the gadget's `S_U` diagonals and its scalar, applied in one scan as a fourth-root
phase, at most one multiplication by `1 - i` and one binary shift; Section 5.2 eq. (`eq:walsh-CZ`) and Proposition 5.5 for the sign
diagonal `CZ`, computed once per record from its address and the pair list; Proposition 5.5 for the final
`×2^s`; all are long-record scans, Lemma A.5 (`lem:transfer-long-record`)).
* Named stacks (`Fin 3`): `0` the lifted array `carrSyms (w + 8d) (encCube (P + 8d) y)` (in
  place), `1` the slice header `sliceHdr P d r w K m j₀ D nS ρ` (restored), `2` the batch
  `pairsSyms pairs` (restored).
* Hypotheses: the slice shape (`j₀ + DK + nS = m`, `ρ < K`), `P + 2 ≤ w`, `d, K ≤ w + m`, the pairs
  are disjoint (`CnotPairsValid`, Section 5.2; so `|pairs| ≤ m/2`), and both
  the input `y` and the output `cnotScanMap … mode y` are disk arrays on the `(P + 8d)`-grid (so
  every stored numerator is exact and fits `w + 8d` bits; the scans are exact integer maps of the
  numerators: units `±1, ±i`, the Gaussian integer `2^s(2-2i)^{q_sel}`, or `2^s`).
* Effect: the array becomes `carrSyms (w + 8d) (encCube (P + 8d) (cnotScanMap … mode y))`.
* Cost `C·(V_* + 2^m·((w + m + 1)^J + |pairsSyms pairs|) + |sliceHdr|)`, `V_* = cvolCube m r
  (w + 8d)`: one pass over the array, per record the address work and one read of the pair list
  (exponent `J` fixed by the kernel), one read of the header. -/
def CnotScanStmt (mode : CnotScanMode) : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m)) (y : RArr (Cube m) r)
      (rest hrest prest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → j₀ + D * K + nS = m → ρ < K → P + 2 ≤ w → d ≤ w + m → K ≤ w + m →
      CnotPairsValid pairs → ArrOnDiskGrid (P + 8 * d) y →
      ArrOnDiskGrid (P + 8 * d) (cnotScanMap K j₀ D ρ pairs mode y) → BlkTerm rest →
      S (.inl 0) = carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest →
      S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      S (.inl 2) = pairsSyms pairs ++ prest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms (w + 8 * d) (encCube (P + 8 * d) (cnotScanMap K j₀ D ρ pairs mode y)) ++ rest))
        (fun _ => True)
        (C * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J + (pairsSyms pairs).length) +
          (sliceHdr P d r w K m j₀ D nS ρ).length))

end SubNLogN.Machine
