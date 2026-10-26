/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Core

/-!
# Proposition A.7 kernel leaves (`AppC/C5Leaves.lean`): streaming kernels of a node

Statements only (no kernel is implemented here). Paper: Lemma A.6 (`lem:transfer-shear`) and
Proposition A.7 (`prop:transfer11`); pure-network steps: `lowerSteps`/`shearOps`/`subHSteps`/
`hMinusDSteps` (`Math/Networks/AppCProc.lean`).
(`Machine/AppC` and `C5`/`c5` retain earlier draft numbering for stability; see Appendix A.)

**Shape of a node array** (descriptor `(k, N1, G, B)`, `k ≥ 1`, `e = m^k`, `b = m^(k-1)`,
`Q = q^b`): `[Rt] × [N1] × [q^e] × [G] × [q^e] × [B]` (the row prefix `[Rt]` is untouched).
The first `q^e` field is the chunk `H`, the second `D`; each chunk is the vector of its `m`
coordinates `X_0, …, X_{m-1}` (radix `Q`, `X_0` most significant).

**Static stream operations** (`StreamOp m`; their inverse address maps `streamMap`):
* `unit X i r`: `X_i ← [r]_Q · X_i` (`[r]_Q = r.num · r.den⁻¹ mod Q`, `ratModC5`, matching
  `ratModNat` in `Math/Networks/`);
* `lowShift X i c`: `X_i ← X_i + Σ_{j<i} [c_j]_Q · X_j` (earlier coordinates of the same chunk);
* `hdShift i j neg`: `D_j ← D_j + H_i` (`neg = false`) or `D_j ← D_j − H_i` (`neg = true`).
All arithmetic is modulo `Q` per coordinate. These match the pure-network elementary node steps
(`AppCProc.lean`): `lowerSteps` = `unit`/`lowShift`, the pivot shifts of `shearOps` = `hdShift _ _ false`
and `unit D _ (-1)`, `subHSteps` = `hdShift i i true`, `hMinusDSteps` = `unit D i (-1)`, `hdShift i i false`.
Validity (`StreamOp.Valid q`): the unit `r` has numerator and denominator prime to `q`, and the
`lowShift` coefficients have denominators prime to `q` (`FacData.Valid`, `Math/Networks/Cert.lean`).

**[LEAF L2] `C5StreamStmt q m op`**: for a valid `op`, a kernel (`KContract`, named stacks `Fin 5`:
`0` the array, `1`-`4` the counters `k, N1, G, B`, restored) applying `op` in place, cost `C·(V + 1)`
(`V = vol v` counts all symbols, separators included).
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts

/-- The chunk targeted by a coordinate operation. -/
inductive Chunk where
  | H
  | D
  deriving DecidableEq

/-- Static stream operations of a Proposition A.7 node. -/
inductive StreamOp (m : ℕ) where
  | unit (X : Chunk) (i : Fin m) (r : ℚ)
  | lowShift (X : Chunk) (i : Fin m) (c : Fin m → ℚ)
  | hdShift (i j : Fin m) (neg : Bool)

/-- `[r]_Q = r.num · r.den⁻¹ mod Q` as a natural number (matching `ratModNat` in
`Math/Networks/Framed.lean` and `Math/Networks/AppCProc.lean`). -/
def ratModC5 (Q : ℕ) (r : ℚ) : ℕ := ((r.num : ZMod Q) * ((r.den : ZMod Q))⁻¹).val

/-- Validity of a stream operation at the radix base `q`: units are `q`-adic units (numerator and
denominator prime to `q`), shift coefficients are `q`-integral (denominator prime to `q`). Then every
`streamMap` below is a bijection of the indices (for every `k ≥ 1`). -/
def StreamOp.Valid {m : ℕ} (q : ℕ) : StreamOp m → Prop
  | .unit _ _ r => Nat.Coprime r.num.natAbs q ∧ Nat.Coprime r.den q
  | .lowShift _ _ c => ∀ j, Nat.Coprime (c j).den q
  | .hdShift _ _ _ => True

/-- Coordinate `i` (`0` most significant) of a chunk value `cv` with `m` coordinates of radix
`Q`. -/
def coordOf (m Q cv : ℕ) (i : ℕ) : ℕ := cv / Q ^ (m - 1 - i) % Q

/-- Replace coordinate `i` of a chunk value by `d`. -/
def setCoordOf (m Q cv : ℕ) (i d : ℕ) : ℕ := cv - coordOf m Q cv i * Q ^ (m - 1 - i) + d * Q ^ (m - 1 - i)

/-- The `D` chunk value of index `y` (`Qe = q^e`). -/
def dvalOf (Qe B y : ℕ) : ℕ := y / B % Qe

/-- The `H` chunk value of index `y`. -/
def hvalOf (Qe G B y : ℕ) : ℕ := y / (B * Qe * G) % Qe

/-- Replace the `D` chunk value of `y`. -/
def setDOf (Qe B y dv : ℕ) : ℕ := y - dvalOf Qe B y * B + dv * B

/-- Replace the `H` chunk value of `y`. -/
def setHOf (Qe G B y hv : ℕ) : ℕ := y - hvalOf Qe G B y * (B * Qe * G) + hv * (B * Qe * G)

/-- The chunk value of `X` at `y`, and its replacement. -/
def chunkVal (Qe G B : ℕ) : Chunk → ℕ → ℕ
  | .H, y => hvalOf Qe G B y
  | .D, y => dvalOf Qe B y

/-- Replace the chunk value of `X` at `y`. -/
def setChunk (Qe G B : ℕ) : Chunk → ℕ → ℕ → ℕ
  | .H, y, v => setHOf Qe G B y v
  | .D, y, v => setDOf Qe B y v

/-- **Inverse address maps of the stream operations** at descriptor `(k, N1, G, B)`: output index
`y` holds the input record at `streamMap q m op k N1 G B y`. (`N1` and the row prefix are never
changed.) -/
def streamMap (q m : ℕ) : StreamOp m → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | .unit X i r, k, _, G, B, y =>
    let Q := q ^ m ^ (k - 1)
    let Qe := q ^ m ^ k
    let cv := chunkVal Qe G B X y
    setChunk Qe G B X y (setCoordOf m Q cv i (ratModC5 Q r⁻¹ * coordOf m Q cv i % Q))
  | .lowShift X i c, k, _, G, B, y =>
    let Q := q ^ m ^ (k - 1)
    let Qe := q ^ m ^ k
    let cv := chunkVal Qe G B X y
    let off := ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), ratModC5 Q (c j) * coordOf m Q cv j
    setChunk Qe G B X y (setCoordOf m Q cv i ((coordOf m Q cv i + Q - off % Q) % Q))
  | .hdShift i j neg, k, _, G, B, y =>
    let Q := q ^ m ^ (k - 1)
    let Qe := q ^ m ^ k
    let dv := dvalOf Qe B y
    let h := coordOf m Q (hvalOf Qe G B y) i
    setDOf Qe B y (setCoordOf m Q dv j
      (if neg then (coordOf m Q dv j + h) % Q else (coordOf m Q dv j + Q - h) % Q))

/-- **[LEAF L2] Streaming kernel of a Proposition A.7 node** for the static operation `op`
(`lem:transfer-shear` streaming maps and the outer shears; realized by `K4RotateCtlStmt`,
`K5UnitMulMixStmt`, `K5NegStmt` with descriptor arithmetic). Hypothesis: `op.Valid q`. Named
stacks (`Fin 5`): `0` the array (in place, followed by a `BlkTerm` tail), `1`-`4` the counters
`k, N1, G, B` (restored); all other stacks (private scratch) restored. Cost `C·(V + 1)`, `C` depending
only on `q, m, op`, uniform in the data and the descriptor. -/
def C5StreamStmt (q m : ℕ) (op : StreamOp m) : Prop :=
  op.Valid q → KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (k Rt N1 G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B → v.length = Rt * rowSize q m k N1 G B →
      (∀ p ∈ v, p.length = w) → BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms k ++ r1 →
      S (.inl 2) = natSyms N1 ++ r2 → S (.inl 3) = natSyms G ++ r3 → S (.inl 4) = natSyms B ++ r4 →
      Runs P S (Function.update S (.inl 0)
          (arrSyms (permByInv (streamMap q m op k N1 G B) v) ++ rest))
        (fun _ => True) (C * (vol v + 1))

/-! ## Leaves L3-L5: XOR gate, child descriptor, row size

The level-`0` interchange (leaf L1) is not a new leaf: it is `K1PairPermMixStmt q (prodComm)`
(proved, `K1/DigitPairPermMix.lean`), used in place through a transfer. -/

/-- Record-wise XOR of two aligned arrays (bitwise on records of equal width). -/
def xorArr (a b : List (List Bool)) : List (List Bool) := List.zipWith (List.zipWith Bool.xor) a b

/-- **[LEAF L3] Elementary XOR gate on two aligned role arrays** (the bit-network gates over
`𝔽₂` in Proposition A.7 (`prop:transfer11`); every gate row of `Scalar.lean` `rowUpd` reads saved
inputs with disjoint targets and controls, so it is a sequence of these). Named stacks (`Fin 2`): `0`
target array `a`, `1` source array `b` (both followed by `BlkTerm` tails; `b` restored).
Result: `a ← xorArr a b`; all other stacks restored. Cost `C·(vol a + vol b + 1)`. -/
def C5XorStmt : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C P =>
    ∀ (w : ℕ) (a b : List (List Bool)) (ra rb : List Sym) (S : KLoc (Fin 2) E → List Sym),
      a.length = b.length → (∀ p ∈ a, p.length = w) → (∀ p ∈ b, p.length = w) →
      BlkTerm ra → BlkTerm rb → S (.inl 0) = arrSyms a ++ ra → S (.inl 1) = arrSyms b ++ rb →
      Runs P S (Function.update S (.inl 0) (arrSyms (xorArr a b) ++ ra)) (fun _ => True)
        (C * (vol a + vol b + 1))

/-- **[LEAF L4] Child descriptor of pivot `(i, j)`** (Proposition A.7 (`prop:transfer11`): the child
interchanges `H_i` and `D_j` of `b = m^(k-1)` fields; spectators re-factored as `cN1, cG, cB`).
Named stacks (`Fin 4`): the counters `k, N1, G, B` (each `natSyms` above a `TermOK` tail). Each
stack gets the child value and a `mark` pushed on top of its old contents:
`k-1`, `cN1 q m k N1 i = N1·q^(i·b)`, `cG q m k G i j = q^((m-1-i)·b)·G·q^(j·b)`,
`cB q m k B j = q^((m-1-j)·b)·B`. Hypotheses `1 ≤ k, N1, G, B`. Cost `C·(rowSize + 1)`. -/
def C5DescStmt (q m : ℕ) (i j : Fin m) : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (k N1 G B : ℕ) (r1 r2 r3 r4 : List Sym) (S : KLoc (Fin 4) E → List Sym),
      1 ≤ k → 1 ≤ N1 → 1 ≤ G → 1 ≤ B → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = natSyms k ++ r1 → S (.inl 1) = natSyms N1 ++ r2 →
      S (.inl 2) = natSyms G ++ r3 → S (.inl 3) = natSyms B ++ r4 →
      Runs P S (Function.update (Function.update (Function.update (Function.update S
          (.inl 0) (natSyms (k - 1) ++ Sym.mark :: S (.inl 0)))
          (.inl 1) (natSyms (cN1 q m k N1 i) ++ Sym.mark :: S (.inl 1)))
          (.inl 2) (natSyms (cG q m k G i j) ++ Sym.mark :: S (.inl 2)))
          (.inl 3) (natSyms (cB q m k B j) ++ Sym.mark :: S (.inl 3)))
        (fun _ => True) (C * (rowSize q m k N1 G B + 1))

/-- **[LEAF L5] Row size** `rowSize q m k N1 G B = N1·q^(m^k)·G·q^(m^k)·B` pushed (with a `mark`
below it) on stack `0` (arbitrary contents); stacks `1`-`4` the counters `k, N1, G, B` (restored).
Hypotheses `1 ≤ N1, G, B`. Cost `C·(rowSize + 1)`. -/
def C5RowSizeStmt (q m : ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (k N1 G B : ℕ) (r1 r2 r3 r4 : List Sym) (S : KLoc (Fin 5) E → List Sym),
      1 ≤ N1 → 1 ≤ G → 1 ≤ B → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 1) = natSyms k ++ r1 → S (.inl 2) = natSyms N1 ++ r2 →
      S (.inl 3) = natSyms G ++ r3 → S (.inl 4) = natSyms B ++ r4 →
      Runs P S (Function.update S (.inl 0)
          (natSyms (rowSize q m k N1 G B) ++ Sym.mark :: S (.inl 0)))
        (fun _ => True) (C * (rowSize q m k N1 G B + 1))

end SubNLogN.Machine.C5
