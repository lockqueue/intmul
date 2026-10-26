/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Layer
import SubNLogN.Machine.Contracts.Arith
import SubNLogN.Math.Walsh.Cube

/-!
# `SubNLogN.Machine` contracts, K3 (`Contracts/Walsh.lean`): Walsh-layer positional permutations

**Scope (honest summary).** This file contains data-format definitions and kernel contract
*statements* (`def … : Prop`, `KContract` shape of `Contracts/Layout.lean`) for the machine part of
Section 5 (`sec:walsh`) of the paper. No kernel is implemented and
nothing here asserts that a contract holds. The only proofs are `decide` sanity checks of pure
definitions.

Statements (with paper anchors):
* `CubeLayerStmt Band lam'`: one completed layer call of Proposition A.11 (`prop:prop14-param`) on a
  slice of a complete binary address cube; the value is `Q_P(H_T z)` with `T` the slice positions
  (`sliceCall_eq`, `Math/Walsh/Cube.lean`).
* `LiftMachineStmt`, `LowerMachineStmt`: exact re-encoding at precision `P + δ` and back (Lemma 5.3,
  `lem:walsh-lift`, and the exact lowering of Proposition 5.5, `prop:cnot-batch`).
* `Cnot1MachineStmt`: one controlled flip by a two-digit permutation (Lemma A.4(1),
  `lem:transfer-streams`), for leftover targets in Theorem 5.8 (`thm:positional-perm`).
* `CnotBatchMachineStmt Band lam'`: slice-batched controlled flips (Proposition 5.5,
  `prop:cnot-batch`).
* `PositionalPermMachineStmt Band lam'`: positional permutations of a complete `m`-bit address
  cube (Theorem 5.8, `thm:positional-perm`).

## Conventions (decisions recorded here)
* **Cube arrays.** A record array `z : RArr (Cube m) r` (`Math/Walsh/Cube.lean`; position `0` of
  an address is the most significant bit, Section 5.1) is stored as `carrSyms w (encCube P z)`: records
  in the order of their index `∑_p x_p 2^{m-1-p}` (`cubeAddrs`), each record its `r` coefficients
  (`Contracts/Records.lean`: two's complement, LSB first, real field then imaginary field). For
  every slice shape `[2^{j₀}] × [2^K]^D × [2^{nS}]` with `j₀ + DK + nS = m` this is the
  lexicographic layer order of Proposition A.11 (`prop:prop14-param`), so a layer call acts on the cube
  array in place (the index equals `lexIndex ∘ cubeToAddr`).
* **Layer interface.** Every statement is generic in the layer's admissible calls `Band` (a
  predicate on `LayerRT`, `Contracts/Layer.lean`) and uses the layer cost `layerCost lam'`
  (`V·⌈d^{λ'}⌉₊ + V + 1`). It is proved from `LayerMachineGenStmt Band (layerCost lam')` in `Machine/Walsh/`;
  Proposition A.11 is `Band = LayerBands p P₀`, `lam' = p.lam'`.
* **Runtime data.** All parameters are runtime data on named stacks, restored: `hdrSyms` lists
  (`Contracts/W9/Common.lean:121`). A positional map `π` is `permSyms π = hdrSyms [π 0, …, π (m-1)]`
  (move convention, Definition 5.6); a batch of controlled flips is
  `pairsSyms pairs = hdrSyms [s, c₁, t₁, …, c_s, t_s]` (count, then control and target; Section 5.2).
  Every runtime list is self-delimiting (its length is in a header or in the list itself), so
  nothing is assumed about the stack content below it.
* **Clean scratch.** Every statement assumes `KClean S` (all private scratch stacks empty on
  entry, hence on exit by the exact final stacks). This is the weaker form for implementers; all
  consumers (K4, `Contracts/FFT.lean`) are clean composites.
* **Costs.** `C * (explicit bound)` with `C` fixed before all runtime data. The per-record address
  work (computing a record's address bits, parities and phases, `poly(P)` per record) is charged
  explicitly as `2^m·(w + m + 1)^J`, with `J` fixed by the kernel before all runtime data
  (`∃ J, KContract …`). The paper absorbs it into `O(V)` by Lemma A.5 (`r ≫ poly(q)`,
  `lem:transfer-long-record`); here it is an explicit lower-order term. Reading a runtime
  header is charged by its length (`|sliceHdr …|`, `|permHdr …|`), and `d, K ≤ w + m` bound the
  header arithmetic.
* **Volume.** `cvolCube m r w = 2^m·(2rw + 1)` is the stack volume of a cube array (`cvol` of
  `Contracts/Arith.lean`; the paper's `V = 2^m·2rw` in Theorem 5.8, plus one record end per record).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## 1. Cube arrays on a stack -/

/-- The cube address with index `i`: bit `p` (position `0` most significant) is bit `m-1-p` of
`i`. -/
def cubeOfNat (m i : ℕ) : Cube m := fun p => i.testBit (m - 1 - (p : ℕ))

/-- All `2^m` addresses of the complete `m`-bit cube, in increasing index order. -/
def cubeAddrs (m : ℕ) : List (Cube m) := (List.range (2 ^ m)).map (cubeOfNat m)

/-- Stored data of a cube record array at precision `F` (records in `cubeAddrs` order). -/
noncomputable def encCube {m r : ℕ} (F : ℕ) (z : RArr (Cube m) r) : List (List CInt) :=
  encArr F (cubeAddrs m) z

/-- Stack volume of a cube array of `2^m` records of `r` coefficients at width `w`. -/
def cvolCube (m r w : ℕ) : ℕ := 2 ^ m * (2 * r * w + 1)

/-! ## 2. Layer calls on slices -/

/-- The layer call (`Contracts/Layer.lean`) on the slice shape `[2^{j₀}] × [2^K]^D × [2^{nS}]` of
the cube at precision `P` and width `w`. -/
def layerRT (P d r w K j₀ D nS ρ : ℕ) : LayerRT :=
  { P := P, d := d, r := r, D := D, A := 2 ^ j₀, S := 2 ^ nS, K := K, ρ := ρ, w := w }

/-- The layer call of a CNOT batch: the slice call at the lifted precision `P + 8d` and width
`w + 8d` (Lemma 5.3, `lem:walsh-lift`). -/
def sliceRT (P d r w K j₀ D nS ρ : ℕ) : LayerRT :=
  layerRT (P + 8 * d) d r (w + 8 * d) K j₀ D nS ρ

/-- Every slice call that a positional permutation of the complete `m`-bit cube can make is
admissible: for every slice shape (`j₀ + DK + nS = m`, `1 ≤ D ≤ d`, `ρ < K`; Definition 5.6,
`def:walsh-positional`) the lifted call `sliceRT` satisfies `Band`. (Proposition A.11's bands are uniform
in the slice shape: the record count is always `2^m` and the header length depends on `j₀ + nS ≤ m` only,
Section 5.3.) This is only an admissibility hypothesis for the layer calls the schedule makes. It
is vacuous when `m < K` (no slice shape with `D ≥ 1` exists, so it holds even for
`Band := fun _ => False`; the schedule then makes no layer call), and it implies no global bound
on `r`, `w`, `m`, `d` (no `m₀ = O(q)`, width or long-record inequality is bundled into
`SliceCallsBand`). Consumers that need such bounds take them as explicit hypotheses (e.g.
`midCost_bound` in `FFT/Middle.lean`). -/
def SliceCallsBand (Band : LayerRT → Prop) (P d r w K m : ℕ) : Prop :=
  ∀ j₀ D nS ρ : ℕ, j₀ + D * K + nS = m → 1 ≤ D → D ≤ d → ρ < K →
    Band (sliceRT P d r w K j₀ D nS ρ)

/-! ## 3. Runtime headers -/

/-- Header of a slice layer call or batch: `[P, d, r, w, K, m, j₀, D, nS, ρ]`. -/
def sliceHdr (P d r w K m j₀ D nS ρ : ℕ) : List Sym := hdrSyms [P, d, r, w, K, m, j₀, D, nS, ρ]

/-- Header of a positional permutation: `[P, d, r, w, K, m]`. -/
def permHdr (P d r w K m : ℕ) : List Sym := hdrSyms [P, d, r, w, K, m]

/-- A positional map as runtime data: `[π 0, …, π (m-1)]` (the bit at position `p` moves to
position `π p`, Definition 5.6, `def:walsh-positional`). -/
def permSyms {m : ℕ} (π : Fin m → Fin m) : List Sym := hdrSyms (List.ofFn fun p => (π p : ℕ))

/-- A batch of controlled flips as runtime data: `[s, c₁, t₁, …, c_s, t_s]` (the count, then
control and target of each pair; the count makes the list self-delimiting). -/
def pairsSyms {m : ℕ} (pairs : List (Fin m × Fin m)) : List Sym :=
  hdrSyms (pairs.length :: pairs.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)])

/-- Exact lift of a coefficient by `δ` fractional bits: both components times `2^δ`. -/
def liftC (δ : ℕ) (c : CInt) : CInt := (c.1 * 2 ^ δ, c.2 * 2 ^ δ)

/-! ## 4. Costs -/

/-- Cost bound of Theorem 5.8 (`thm:positional-perm`, eq. `eq:walsh-perm-cost`, `O(V[(m₀/d + K) d^{λ'} + K])`):
`(m/d + K + 1)·(V_*·(⌈d^{λ'}⌉₊ + 1) + 2^m·(w + m + 1)^J)` with the lifted volume
`V_* = cvolCube m r (w + 8d)`. The factor `m/d + K` bounds `N_slice = K⌈⌊m/K⌋/d⌉`
(eq. `eq:walsh-slices`); `36 N_slice` layer calls and `< 6K` leftover two-digit permutations
(Theorem 5.8, Section 5.3) are absorbed into the constant. -/
noncomputable def permCost (lam' : ℝ) (J d r w K m : ℕ) : ℕ :=
  (m / d + K + 1) *
    (cvolCube m r (w + 8 * d) * (⌈(d : ℝ) ^ lam'⌉₊ + 1) + 2 ^ m * (w + m + 1) ^ J)

/-! ## 5. Contracts -/

/-- **[CONTRACT] K3.0, one completed layer call on a slice of the cube array** (Proposition A.11,
`prop:prop14-param`, at the slice shape of Definition 5.6, `def:walsh-positional`).
* Named stacks (`Fin 2`): `0` the cube array (in place), `1` the header
  `sliceHdr P d r w K m j₀ D nS ρ` (restored).
* For `j₀ + DK + nS = m`, `ρ < K`, `P + 2 ≤ w`, an admissible call
  `Band (layerRT P d r w K j₀ D nS ρ)` and a disk-grid input `z` at precision `P`, the array becomes
  `Q_P(H_T z)`, `T = slicePos m K j₀ D ρ` (the paper's `H` on bit `ρ` of the `D` chunks; equal to
  `sliceCall layer …` for every oracle satisfying `LayerSpec`, by `sliceCall_eq`).
* Cost `C·(layerCost lam' t + (w + m + 1)^J + |sliceHdr|)`: the layer call, building its
  header `LayerRT.hdr` from `sliceHdr` (reading the header is charged by its length; `d, K ≤ w + m`
  bound the header arithmetic).
* Intended proof: `LayerMachineGenStmt Band (layerCost lam')` on the same array stack (the cube
  order is the layer order), plus a header builder. -/
def CubeLayerStmt (Band : LayerRT → Prop) (lam' : ℝ) : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r w K m j₀ D nS ρ : ℕ) (z : RArr (Cube m) r) (rest hrest : List Sym)
      (S : KLoc (Fin 2) E → List Sym),
      KClean S → j₀ + D * K + nS = m → ρ < K → P + 2 ≤ w → d ≤ w + m → K ≤ w + m →
      Band (layerRT P d r w K j₀ D nS ρ) → ArrOnDiskGrid P z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube P z) ++ rest →
      S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms w (encCube P (truncArr P (hT (slicePos m K j₀ D ρ) z))) ++ rest))
        (fun _ => True)
        (C * (layerCost lam' (layerRT P d r w K j₀ D nS ρ) + (w + m + 1) ^ J +
          (sliceHdr P d r w K m j₀ D nS ρ).length))

/-- **[CONTRACT] K3.1, exact lift by `δ` fractional bits** (Lemma 5.3, `lem:walsh-lift`,
Section 5.1: "append `8d` fractional zero bits to every numerator and use width `w_* = w + 8d`").
* Named stacks (`Fin 2`): `0` the array (in place), `1` the header `hdrSyms [w, δ]` (restored).
* Every coefficient `(re, im)` at width `w` becomes `(re·2^δ, im·2^δ)` at width `w + δ`
  (`liftC δ`). At the value level, for a `P`-grid array, `encCube (P + δ) z` is
  `mapC (liftC δ) (encCube P z)`.
* Guards: `1 ≤ w`, inputs fit `w` bits (then the outputs fit `w + δ` bits).
* Cost `C·(cvol (w + δ) v + w + δ + 1)` (one re-encoding scan; the header rebuild of Lemma 5.3 is
  caller data). -/
def LiftMachineStmt : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (w δ : ℕ) (v : List (List CInt)) (rest hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ w → CArrFits w v → BlkTerm rest →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 1) = hdrSyms [w, δ] ++ hrest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms (w + δ) (mapC (liftC δ) v) ++ rest))
        (fun _ => True) (C * (cvol (w + δ) v + w + δ + 1))

/-- **[CONTRACT] K3.2, exact lowering by `δ` fractional bits** (Proposition 5.5, `prop:cnot-batch`: "lowering from `q_*`
to `P` discards only zero bits"). The inverse of `LiftMachineStmt`: an array whose numerators are
multiples of `2^δ`, stored at width `w + δ`, i.e. `mapC (liftC δ) v`, becomes `v` at width `w`.
Named stacks, guards and cost as in `LiftMachineStmt`; `v` must fit `w` bits. -/
def LowerMachineStmt : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (w δ : ℕ) (v : List (List CInt)) (rest hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ w → CArrFits w v → BlkTerm rest →
      S (.inl 0) = carrSyms (w + δ) (mapC (liftC δ) v) ++ rest →
      S (.inl 1) = hdrSyms [w, δ] ++ hrest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms w v ++ rest))
        (fun _ => True) (C * (cvol (w + δ) v + w + δ + 1))

/-- **[CONTRACT] K3.3, one controlled flip by a two-digit permutation** (Lemma A.4(1),
`lem:transfer-streams`; used for leftover targets in Theorem 5.8, `thm:positional-perm`).
* Named stacks (`Fin 3`): `0` the cube array (in place), `1` the header `permHdr P d r w K m`,
  `2` the pair `pairsSyms [(c, t)]` (both restored).
* For `c ≠ t` the array becomes `cnotArr [(c, t)] z`: the record at address `x` moves to the
  address with `x_t ↦ x_t ⊕ x_c` (Lemma 5.4, `lem:cnot`). No value hypothesis is needed, since
  records move unchanged.
* Cost `C·(cvolCube m r w + (w + m + 1)^J + |permHdr|)` (the header is read). -/
def Cnot1MachineStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r w K m : ℕ) (c t : Fin m) (z : RArr (Cube m) r) (rest hrest prest : List Sym)
      (S : KLoc (Fin 3) E → List Sym),
      KClean S → c ≠ t → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube P z) ++ rest →
      S (.inl 1) = permHdr P d r w K m ++ hrest →
      S (.inl 2) = pairsSyms [(c, t)] ++ prest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms w (encCube P (cnotArr [(c, t)] z)) ++ rest))
        (fun _ => True) (C * (cvolCube m r w + (w + m + 1) ^ J + (permHdr P d r w K m).length))

/-- **[CONTRACT] K3.4, slice-batched controlled flips** (Proposition 5.5, `prop:cnot-batch`;
Lemmas 5.1–5.4).
* Named stacks (`Fin 3`): `0` the cube array (in place), `1` the header
  `sliceHdr P d r w K m j₀ D nS ρ` of the target slice, `2` the batch `pairsSyms pairs` (both
  restored).
* Hypotheses: the slice is one of Definition 5.6 (`j₀ + DK + nS = m`, `1 ≤ D ≤ d`, `ρ < K`);
  `P + 2 ≤ w`; the pairs are disjoint (`CnotPairsValid`: the `2s` positions are distinct, Section 5.2);
  every target lies in the slice (`targets pairs ⊆ slicePos m K j₀ D ρ`; controls anywhere else,
  Proposition 5.5); the lifted layer call is admissible (`Band (sliceRT …)`); `z` is a disk-grid array
  at precision `P`.
* Effect: the array becomes `cnotArr pairs z` (the record at `x` moves to the address with
  `x_{t_j} ↦ x_{t_j} ⊕ x_{c_j}` for all `j`), in the original `P`-grid format. The procedure (Proposition 5.5):
  lift to `P_* = P + 8d`, `w_* = w + 8d`; gadget `S_U, H_all, S_U, H_all, S_U, H_all`, scalar
  (Lemma 5.1, `lem:walsh-select`); the sign diagonal `CZ` (computed once per record, eq. `eq:walsh-CZ`); the gadget again;
  `×2^s`; exact lowering. Six completed layer calls (Proposition 5.5).
* Cost `C·(layerCost lam' (sliceRT …) + V_* + 2^m·(w + m + 1)^J + |sliceHdr|)`,
  `V_* = cvolCube m r (w + 8d)` (Proposition 5.5, `O(V d^{λ'})`; the six calls, the lift/lowering scans and
  the per-record phase and sign scans are absorbed into `C`; the per-record address work and the
  header reading are explicit; `d, K ≤ w + m` bound the header arithmetic). -/
def CnotBatchMachineStmt (Band : LayerRT → Prop) (lam' : ℝ) : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m)) (z : RArr (Cube m) r)
      (rest hrest prest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → j₀ + D * K + nS = m → 1 ≤ D → D ≤ d → ρ < K → P + 2 ≤ w → d ≤ w + m →
      K ≤ w + m → CnotPairsValid pairs → targets pairs ⊆ slicePos m K j₀ D ρ →
      Band (sliceRT P d r w K j₀ D nS ρ) → ArrOnDiskGrid P z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube P z) ++ rest →
      S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      S (.inl 2) = pairsSyms pairs ++ prest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms w (encCube P (cnotArr pairs z)) ++ rest))
        (fun _ => True)
        (C * (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + cvolCube m r (w + 8 * d) +
          2 ^ m * (w + m + 1) ^ J + (sliceHdr P d r w K m j₀ D nS ρ).length))

/-- **[CONTRACT] K3.5, positional permutations** (Theorem 5.8, `thm:positional-perm`;
Definition 5.6, `def:walsh-positional`; Lemma 5.7, `lem:walsh-involutions`).
* Named stacks (`Fin 3`): `0` the cube array (in place), `1` the header `permHdr P d r w K m`,
  `2` the map `permSyms π` (both restored).
* Hypotheses: `1 ≤ d`, `1 ≤ K`, `P + 2 ≤ w`, `d, K ≤ w + m`; every slice call the schedule can
  make is admissible (`SliceCallsBand Band P d r w K m`, the only form in which "the parameter
  family of Proposition A.11" in Theorem 5.8 enters; it is vacuous for `m < K`, where no layer call is
  made, and implies no global bound such as `m₀ = O(q)`: effect and cost hold for every `m`);
  `z` is a disk-grid array at precision `P` on the complete `m`-bit cube (Theorem 5.8).
* Effect: for every positional map `π` (a permutation of the `m` positions, move convention), the
  array becomes `posPermArr π z`: the induced record permutation, exactly, in the original grid
  and format (Theorem 5.8). The procedure (Section 5.3): the involutions `I₀`, `I₁` of
  Lemma 5.7, three stages each, the pairs of a stage batched by the slice of their target
  (`CnotBatchMachineStmt`), leftover targets by `Cnot1MachineStmt`; it follows
  `posPermProg` (`Math/Walsh/PositionalPerm.lean`).
* Cost `C·(permCost lam' J d r w K m + |permHdr|)` (eq. `eq:walsh-perm-cost`; the header is read, and
  `d, K ≤ w + m` bound the header arithmetic; `permCost`'s `2^m (w+m+1)^J` term pays the runtime
  schedule compiler, whose commands have length polynomial in `m` without assuming an `O(q)`-bit
  command bound).
* Not covered (Section 5.3): incomplete cubes, short records, arbitrary record
  permutations. -/
def PositionalPermMachineStmt (Band : LayerRT → Prop) (lam' : ℝ) : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r w K m : ℕ) (π : Equiv.Perm (Fin m)) (z : RArr (Cube m) r)
      (rest hrest prest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → 1 ≤ d → 1 ≤ K → P + 2 ≤ w → d ≤ w + m → K ≤ w + m →
      SliceCallsBand Band P d r w K m →
      ArrOnDiskGrid P z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube P z) ++ rest →
      S (.inl 1) = permHdr P d r w K m ++ hrest →
      S (.inl 2) = permSyms π ++ prest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms w (encCube P (posPermArr π z)) ++ rest))
        (fun _ => True) (C * (permCost lam' J d r w K m + (permHdr P d r w K m).length))

/-! ## 6. Sanity checks (`decide`) -/

/-- The index of `cubeOfNat` reads bits most significant first: `6 = 110₂` on `3` bits. -/
example : (List.finRange 3).map (cubeOfNat 3 6) = [true, true, false] := by decide

example : (cubeAddrs 2).map (fun x => (List.finRange 2).map x) =
    [[false, false], [false, true], [true, false], [true, true]] := by decide

end SubNLogN.Machine
