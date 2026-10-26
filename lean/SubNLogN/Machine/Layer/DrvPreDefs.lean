/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DriverSpec
import SubNLogN.Machine.Contracts.Arith

/-!
# Layer driver pre-phase: sub-kernel statements (`Machine/Layer/DrvPreDefs.lean`)

**Scope (honest summary).** Definitions and named statements (`def … : Prop`) only; nothing is
proved here. They are the hypotheses of the reduction `drvPre_of_parts`
(`Machine/Layer/DrvPre*.lean`), which derives `DrvPreStmt p` (`Machine/Layer/DriverSpec.lean`)
from these statements and the proved kernels `shl_holds`, `K1.c3LongRecordScan_holds`.

Pre-phase chronology (Section A.6 (`sec:transfer-layer`)): header and parameters; re-encode
(`×2^Δ`, width `w → w_g`); `𝒮_D` (a Lemma A.5 (`lem:transfer-long-record`) scan); `min(q₀, D)` kernels
(`DrvCKernelStmt`, one pass each); in the rows case the zero-row padding (`DrvPadStmt`); the piece
descriptors (`DrvDescStmt`).

All three statements are at the integer level (stored numerators, `Contracts/Records.lean` format:
`carrSyms w v`, each coefficient `twosBits w re ++ twosBits w im`, records terminated by `sep`, first
record on top). Their relation to the value-level semantics (`dgate`, `embedArr`, `drvDescSyms`) is the
reduction's business.
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-! ## Integer level: the individual kernel `C = aI + bX`, `a = (1+i)/2`, `b = (1-i)/2` -/

/-- First output of `C` on a pair of numerators `(a, b)`: `((a + b) + i(a − b))/2`, i.e.
`((a₀ + b₀) − (a₁ − b₁))/2 + i((a₁ + b₁) + (a₀ − b₀))/2`; the halving truncates toward zero
(it is exact in every use by the driver). -/
def cgate0 (a b : CInt) : CInt :=
  (tdivPow ((a.1 + b.1) - (a.2 - b.2)) 1, tdivPow ((a.2 + b.2) + (a.1 - b.1)) 1)

/-- Second output of `C` on `(a, b)`: `((a + b) − i(a − b))/2`, halving truncating toward zero. -/
def cgate1 (a b : CInt) : CInt :=
  (tdivPow ((a.1 + b.1) + (a.2 - b.2)) 1, tdivPow ((a.2 + b.2) - (a.1 - b.1)) 1)

/-- One block of `2W` records: records `i < W` are the halves `u_i` (selected bit `0`), records
`W + i` the halves `v_i` (selected bit `1`). The block becomes, coefficientwise,
`cgate0 u_i v_i` (records `i < W`) followed by `cgate1 u_i v_i` (records `W + i`). -/
def cgateBlock (W : ℕ) (blk : List (List CInt)) : List (List CInt) :=
  List.zipWith (List.zipWith cgate0) (blk.take W) (blk.drop W) ++
    List.zipWith (List.zipWith cgate1) (blk.take W) (blk.drop W)

/-- A valid block of the kernel pass: `2W` records, and records `i` and `W + i` have the same
number of coefficients. -/
def CGateBlockOK (W : ℕ) (blk : List (List CInt)) : Prop :=
  blk.length = 2 * W ∧ ∀ i < W, (blk.getD i []).length = (blk.getD (W + i) []).length

/-- A block followed by `Npad` zero records of `r` coefficients each. -/
def padBlock (Npad r : ℕ) (blk : List (List CInt)) : List (List CInt) :=
  blk ++ List.replicate Npad (List.replicate r (0, 0))

/-! ## Sub-kernel statements -/

/-- **[CONTRACT] Driver pre-phase, one individual-kernel pass** (Section A.6 (`sec:transfer-layer`),
Proposition A.11 (`prop:prop14-param`)). The array is a sequence of blocks of `2W` records (`W` = the record-index weight of the
selected bit of one chunk); every block becomes `cgateBlock W` of itself (the kernel
`C(u, v) = (au + bv, bu + av)` coefficientwise on the record pairs `(i, W + i)`).
* Named stacks (`Fin 3`): `0` the array (in place), `1` the counter `W`, `2` the width `w`
  (both restored).
* Guards: `1 ≤ W`, `1 ≤ w`, valid blocks, inputs and outputs fit `w` bits (`CArrFits`).
* Every other stack is unchanged (restored convention, arbitrary private scratch at entry).
* Cost `C·(V + N·(bitLen W + 1) + w + 1)`, `V = cvol w` of the input, `N` = number of records. -/
def DrvCKernelStmt : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (W w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 : List Sym)
      (S : KLoc (Fin 3) E → List Sym),
      1 ≤ W → 1 ≤ w → (∀ blk ∈ blks, CGateBlockOK W blk) →
      CArrFits w blks.flatten → CArrFits w (blks.map (cgateBlock W)).flatten →
      BlkTerm rest → TermOK r1 → TermOK r2 →
      S (.inl 0) = carrSyms w blks.flatten ++ rest → S (.inl 1) = natSyms W ++ r1 →
      S (.inl 2) = natSyms w ++ r2 →
      Runs Pr S
        (Function.update S (.inl 0) (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest))
        (fun _ => True)
        (C * (cvol w blks.flatten + blks.flatten.length * (bitLen W + 1) + w + 1))

/-- **[CONTRACT] Driver pre-phase, zero-row padding** (Section A.6 (`sec:transfer-layer`)).
The array is a sequence of blocks of `N0` records; after every block, `Npad` zero records of `r`
coefficients (every component numerator `0`, width `w`) are inserted.
* Named stacks (`Fin 5`): `0` the array (in place), `1` the counter `N0`, `2` the counter `Npad`,
  `3` the coefficient count `r`, `4` the width `w` (all restored).
* Guards: `1 ≤ N0` (empty blocks would be invisible in the input), `1 ≤ w`, every block has `N0`
  records.
* Every other stack is unchanged (restored convention).
* Cost `C·(V_out + (#blocks + 1)·(bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1))`,
  `V_out = cvol w` of the padded array. -/
def DrvPadStmt : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C Pr =>
    ∀ (N0 Npad r w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ N0 → 1 ≤ w → (∀ blk ∈ blks, blk.length = N0) → BlkTerm rest →
      TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = carrSyms w blks.flatten ++ rest → S (.inl 1) = natSyms N0 ++ r1 →
      S (.inl 2) = natSyms Npad ++ r2 → S (.inl 3) = natSyms r ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs Pr S
        (Function.update S (.inl 0) (carrSyms w (blks.map (padBlock Npad r)).flatten ++ rest))
        (fun _ => True)
        (C * (cvol w (blks.map (padBlock Npad r)).flatten +
          (blks.length + 1) * (bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1)))

/-- **[CONTRACT] Driver pre-phase, piece descriptors** (Section A.6 (`sec:transfer-layer`),
Proposition A.11 (`prop:prop14-param`)). From the layer header `t.hdr` (restored), push `drvDescSyms t` (the C-core
descriptors `(drvCtx t 0 pc).hdr` of the base-`m` pieces of `D - q₀`, first piece on top, then the
end tag `.tag 15`; just the end tag in the no-rows case) on top of the descriptor stack.
* Named stacks (`Fin 2`): `0` the header (restored; anything may lie below it), `1` the descriptor
  stack.
* Every other stack is unchanged (restored convention).
* Cost `C·((|hdr| + D·K + 1)^J + |drvDescSyms t|)` for one exponent `J` (the term `D·K` pays for
  `2^{q₀K}` in `padR` when `q₀ < D`). -/
def DrvDescStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
      S (.inl 0) = t.hdr ++ hrest →
      Runs Pr S (Function.update S (.inl 1) (drvDescSyms t ++ S (.inl 1)))
        (fun _ => True) (C * ((t.hdr.length + t.D * t.K + 1) ^ J + (drvDescSyms t).length))

end SubNLogN.Machine.Layer
