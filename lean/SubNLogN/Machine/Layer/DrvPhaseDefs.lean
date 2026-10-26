/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreDefs

/-!
# Layer driver: shared record-pass statements (`Machine/Layer/DrvPhaseDefs.lean`)

**Scope (honest summary).** Definitions and named statements (`def … : Prop`) only; nothing is
proved here. They are hypotheses of the reductions `drvPost_of_parts` and `drvPre_of_parts`
(`Machine/Layer/DrvPost*.lean`, `DrvPre*.lean`).
* `DrvPhaseScanStmt` — one recordwise scan: every coefficient of record `x` is multiplied by
  `i^{s(x) + c}` (`s(x)` = number of selected bits of the address of `x`, `selCount`) and, if `o = 1`,
  by `1 - i`; the width may change. Used for `𝒮_D` (pre, `c = 0`, `o = 0`) and for `𝒮_D`, the phase of
  `b^D` and its factor `1 - i` (post, `c ≡ -⌊D/2⌋`, `o = D mod 2`); the halvings of `b^D` and the
  truncation are a separate `TruncShiftStmt` pass.
* `DrvUnpadStmt` — keep the first `N0` records of every block of `N0 + Npad` records (inverse of
  `DrvPadStmt`).

Integer level, format of `Contracts/Records.lean` (`carrSyms w v`).
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-! ## Integer level -/

/-- Rotation of a numerator by `i^e` (`e` read modulo `4`). -/
def rotC (e : ℕ) (c : CInt) : CInt :=
  if e % 4 = 0 then c
  else if e % 4 = 1 then (-c.2, c.1)
  else if e % 4 = 2 then (-c.1, -c.2)
  else (c.2, -c.1)

/-- Multiplication of a numerator by `1 - i`: `(a + bi)(1 - i) = (a + b) + (b - a)i`. -/
def omiC (c : CInt) : CInt := (c.1 + c.2, c.2 - c.1)

/-- Selected-bit count of record index `x` in a layer array `[A] × [2^K]^D × [S]` in lexicographic
order: the number of chunks `j < D` whose bit `ρ` is set, i.e. of `j < D` with bit `ρ + K·j` of
`x / S` set. -/
def selCount (S K ρ D x : ℕ) : ℕ :=
  ((List.range D).filter fun j => (x / S).testBit (ρ + K * j)).length

/-- The phase map of record `x`: every coefficient times `i^{selCount x + c}`, then times `1 - i` if
`o = 1`. -/
def phaseRec (S K ρ D c o x : ℕ) (cs : List CInt) : List CInt :=
  cs.map fun z => if o = 1 then omiC (rotC (selCount S K ρ D x + c) z)
    else rotC (selCount S K ρ D x + c) z

/-! ## Statements -/

/-- **[CONTRACT] Driver phase scan** (Lemma A.5 (`lem:transfer-long-record`), Section A.6: a
long-record scan with a fourth-root phase and at most one multiplication by `1 - i`). Record `x` of
the array becomes `phaseRec S K ρ D c o x` of itself, at width `w2`.
* Named stacks (`Fin 2`): `0` the array (in place), `1` the parameter header
  `hdrSyms [S, K, ρ, D, c, o, w1, w2]` (restored; anything may lie below it).
* Guards: `1 ≤ S`, `ρ < K`, `o ≤ 1`, `1 ≤ w1`, `1 ≤ w2`, inputs fit `w1`, outputs fit `w2`.
* Every other stack is unchanged (restored convention, arbitrary private scratch at entry).
* Cost `C·(V_in + V_out + (N + 1)·(bitLen N + |hdr| + 1)^J)` for one exponent `J`, `N` = number
  of records (the address computation of each record; absorbed by long records). -/
def DrvPhaseScanStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (S K ρ D c o w1 w2 : ℕ) (v : List (List CInt)) (rest rp : List Sym)
      (St : KLoc (Fin 2) E → List Sym),
      1 ≤ S → ρ < K → o ≤ 1 → 1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v →
      CArrFits w2 (v.mapIdx (phaseRec S K ρ D c o)) → BlkTerm rest → TermOK rp →
      St (.inl 0) = carrSyms w1 v ++ rest →
      St (.inl 1) = hdrSyms [S, K, ρ, D, c, o, w1, w2] ++ rp →
      Runs Pr St
        (Function.update St (.inl 0) (carrSyms w2 (v.mapIdx (phaseRec S K ρ D c o)) ++ rest))
        (fun _ => True)
        (C * (cvol w1 v + cvol w2 v +
          (v.length + 1) * (bitLen v.length + (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length + 1) ^ J))

/-- **[CONTRACT] Driver post-phase, unpad** (Section A.6 (`sec:transfer-layer`), Proposition A.11). The array is a
sequence of blocks of `N0 + Npad` records; every block keeps its first `N0` records.
* Named stacks (`Fin 3`): `0` the array (in place), `1` the counter `N0`, `2` the counter `Npad`
  (both restored).
* Guards: every block has `N0 + Npad` records.
* Every other stack is unchanged (restored convention).
* Cost `C·(V_in + (#blocks + 1)·(bitLen N0 + bitLen Npad + 1))`, `V_in = cvol w` of the input. -/
def DrvUnpadStmt : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (N0 Npad w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 : List Sym)
      (S : KLoc (Fin 3) E → List Sym),
      (∀ blk ∈ blks, blk.length = N0 + Npad) → BlkTerm rest → TermOK r1 → TermOK r2 →
      S (.inl 0) = carrSyms w blks.flatten ++ rest → S (.inl 1) = natSyms N0 ++ r1 →
      S (.inl 2) = natSyms Npad ++ r2 →
      Runs Pr S
        (Function.update S (.inl 0) (carrSyms w (blks.map (List.take N0)).flatten ++ rest))
        (fun _ => True)
        (C * (cvol w blks.flatten + (blks.length + 1) * (bitLen N0 + bitLen Npad + 1)))

end SubNLogN.Machine.Layer
