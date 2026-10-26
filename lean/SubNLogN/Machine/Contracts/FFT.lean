/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Walsh
import SubNLogN.Math.Walsh.Middle

/-!
# `SubNLogN.Machine` contracts, K4 (`Contracts/FFT.lean`): the direct FFT machine and the Walsh middle

**Scope (honest summary).** This file contains data-format definitions and kernel contract
*statements* (`def … : Prop`, `KContract` shape) for the machine part of Section 6 (`sec:direct-fft`)
of the paper: Theorem 6.5 (`thm:direct-fft`) and Corollary 6.6 (`cor:walsh-middle`). No kernel is
implemented here and nothing in this file asserts
that a contract holds.

Every output value uses the math-layer definition (`SubNLogN/Math/Walsh/*.lean`, frozen names):
`lastAxisFFT`, `posPermArr (layoutL …)`, `posPermArr (layoutU …)`, `roundsProg`, `twJ`,
`roundSet`, `phaseTable`, `walshMiddle`, run with `idealLayer` (every layer call returns
exactly `Q_P(Hz)`, which is what the machine layer `LayerMachineGenStmt` computes).

Statements (the four stages in the proof of Theorem 6.5, Section 6.4):
* `PhaseTableMachineStmt`: the `2r`-entry table of Lemma 6.1 (`lem:phase-table`).
* `RecordDIFStmt`: (i) per-record normalized DIF on the `r` coefficients, then bit reversal of the
  coefficient index (Theorem 6.5, stage (i)).
* `LayoutExecStmt Band lam' sel`: (ii) the positional map `L`, and (iv) `U = (LB)^{-1}`
  (Lemma 6.3, `lem:walsh-layout`), executed by Theorem 5.8 (`thm:positional-perm`).
* `PrefixRoundStmt`, `ChunkRoundStmt Band lam'`, `TwiddlePassStmt`: one record-axis round
  (Theorem 6.5, stage (iii)): exact butterflies then one `Q_q` (prefix rounds), one layer call (chunk
  rounds), then one combined twiddle per record `θ̃_{2J(x)}` with one `Q_q` (Section 6.3, `sec:direct-fft-twiddle`).
* `RoundsStmt Band lam'`: (iii) all rounds `v = ℓ-1, …, 0` (`roundsProg`).
* `WalshMiddleMachineGenStmt Band lam'`: Corollary 6.6, machine form: the encoded input tensor
  becomes the encoded `walshMiddle idealLayer q D ℓ K a U`. `WalshMiddleMachineStmt p` is its
  instance at Proposition A.11's bands.

## Conventions (decisions recorded here, in addition to `Contracts/Walsh.lean`)
* **Tensor format** (Section 6; Corollary 6.6, "natural axis order, last axis contiguous"). The
  tensor `U : Idx (fftShape a ℓ) → ℂ` is stored as the cube array `ofTensor a ℓ U`
  (`Math/Walsh/DirectFFT.lean`): record `x` = the last-axis line, `r = 2^ℓ` coefficients; records
  in cube index order, i.e. natural order with axis `0` most significant (flattened, this is
  `encFreq` order). Stack content `carrSyms w (encCube q (ofTensor a ℓ U))`, updated in place.
* **Header.** `midHdr q ℓ K w a = hdrSyms ([q, D, ℓ, K, w] ++ [a 0, …, a (D-1)])` (restored).
  `d = D + 1`, `r = 2^ℓ`, `m₀ = addrBits a`.
* **Phase table.** `tabSyms w q ℓ θ̃`: `2r` one-coefficient records `[θ̃_j]`, `j = 0, …, 2r-1`, at
  precision `q`, width `w`. Parts that read the table take it on named stack `2` (restored) for any
  disk-grid table (`TabOK`); the middle builds the concrete `phaseTable q ℓ` once (Section 6.4).
* **Round index.** Per-round parts read `v` as `natSyms v` on named stack `3` (restored).
* **Hypotheses.** `MidShapeOK` = the shape hypotheses of Theorem 6.5 (`thm:direct-fft`) at precision `q`
  (`q ≥ 8`, `d ≥ 2`, `2 ≤ ℓ < q`, `1 ≤ K ≤ ℓ-1`, `t_i ∈ {r/2, r}`) and `q + 2 ≤ w`.
  `MidCallsBand Band` = every layer call made is admissible (chunk rounds at `q`, CNOT batches at
  `q + 8d`); with `Band = LayerBands p P₀` this is where "the parameter family of
  Proposition A.11" and `dℓ ≤ C_ℓ q` enter (Theorem 6.5; Lemma 5.3, `lem:walsh-lift`, for `q + 8d`).
* **Costs.** `C * (explicit bound)`. Scalar products are charged through `mulW (2w + 1)`
  (`Contracts/Arith.lean`, the `mulBig` unit) per coefficient: `R·mulW(2w+1) ≈ V·𝗆(q)` with
  `R = 2^{m₀}·r`. Per-record address work is the explicit term `2^{m₀}·(w + m₀ + 1)^J` and table
  construction `2^ℓ·(w + 1)^J` (lower order: `M ≥ r/2` and `r ≫ poly(q)`, Section 6.4), with `J` fixed by
  the kernel before all runtime data. Reading the header is charged explicitly by its length
  `|midHdr q ℓ K w a|` (a stack machine must pop the earlier fields to reach a later one); every
  part assumes `MidShapeOK`, which bounds all header fields by `w + m₀`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## 1. Header, table, shape conditions -/

/-- Header of the direct FFT / Walsh middle: `[q, D, ℓ, K, w, a 0, …, a (D-1)]`. -/
def midHdr {D : ℕ} (q ℓ K w : ℕ) (a : Fin D → ℕ) : List Sym :=
  hdrSyms ([q, D, ℓ, K, w] ++ List.ofFn a)

/-- The phase table as data: `2r` one-coefficient records `[θ̃_j]`, `j < 2r = 2^{ℓ+1}`, at
precision `q`. -/
noncomputable def tabRecs (q ℓ : ℕ) (θt : ℕ → ℂ) : List (List CInt) :=
  (List.range (2 * 2 ^ ℓ)).map fun j => [gridInt q (θt j)]

/-- Stack content of the phase table at width `w`. -/
noncomputable def tabSyms (w q ℓ : ℕ) (θt : ℕ → ℂ) : List Sym := carrSyms w (tabRecs q ℓ θt)

/-- A disk-grid phase table: `θ̃_j ∈ 𝔻_q` for every `j < 2r` (part of `PhaseTableSpec`,
Lemma 6.1, `lem:phase-table`). -/
def TabOK (q ℓ : ℕ) (θt : ℕ → ℂ) : Prop := ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)

/-- **Shape hypotheses of Theorem 6.5 (`thm:direct-fft`) at precision `q`** and the width condition
`q + 2 ≤ w`: `q ≥ 8`, `d = D + 1 ≥ 2`, `2 ≤ ℓ < q`, `1 ≤ K ≤ ℓ - 1`,
`t_i = 2^{a_i} ∈ {r/2, r}`. (`ℓ ≤ q`, needed by Lemma 6.1, follows.) -/
def MidShapeOK {D : ℕ} (q ℓ K w : ℕ) (a : Fin D → ℕ) : Prop :=
  8 ≤ q ∧ 1 ≤ D ∧ 2 ≤ ℓ ∧ ℓ < q ∧ 1 ≤ K ∧ K ≤ ℓ - 1 ∧ (∀ i, a i = ℓ - 1 ∨ a i = ℓ) ∧ q + 2 ≤ w

/-- Every chunk-round call is admissible: the layer at precision `q` on every shape
`[2^{j₀}] × [2^K]^D × [2^{nS}]` of the `m₀`-bit cube (Lemma 6.3 and Theorem 6.5). -/
def ChunkCallsBand (Band : LayerRT → Prop) {D : ℕ} (q ℓ K w : ℕ) (a : Fin D → ℕ) : Prop :=
  ∀ j₀ nS ρ : ℕ, j₀ + D * K + nS = addrBits a → ρ < K →
    Band (layerRT q (D + 1) (2 ^ ℓ) w K j₀ D nS ρ)

/-- Every layer call of the middle is admissible: chunk rounds at `q`, and the CNOT batches of
the positional maps `L`, `U` at `q + 8d` (Corollary 6.6, `cor:walsh-middle`). -/
def MidCallsBand (Band : LayerRT → Prop) {D : ℕ} (q ℓ K w : ℕ) (a : Fin D → ℕ) : Prop :=
  ChunkCallsBand Band q ℓ K w a ∧ SliceCallsBand Band q (D + 1) (2 ^ ℓ) w K (addrBits a)

/-- The two positional maps of the direct FFT (Lemma 6.3). -/
inductive LayoutSel
  /-- the layout `L` (Section 6.2, Lemma 6.3, `lem:walsh-layout`) -/
  | L
  /-- natural-order restoration `U = (LB)^{-1}` (Lemma 6.3, eq. `eq:unshuffle`) -/
  | U
  deriving DecidableEq

/-- The positional map selected by `sel`: `layoutL ℓ K a` or `layoutU ℓ K a`. -/
def layoutMap (sel : LayoutSel) {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) :
    Fin (addrBits a) → Fin (addrBits a) :=
  match sel with
  | .L => layoutL ℓ K a
  | .U => layoutU ℓ K a

/-- A round `v` is a chunk round (`b₀ ≤ v ≤ ℓ - 2`, Lemma 6.3), as in `roundStep`. -/
def IsChunkRound (ℓ K v : ℕ) : Prop := 0 < K ∧ layoutB0 ℓ K ≤ v ∧ v + 2 ≤ ℓ

/-- First position `j₀ = n_P + ⌊(ℓ-2-v)/K⌋·D·K` of the chunks of round `v` (Lemma 6.3,
`lem:walsh-layout`; `roundStep`). -/
def roundJ0 {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) : ℕ :=
  prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K

/-- Selected bit `ρ = (v - b₀) mod K` of round `v` (Lemma 6.3, `lem:walsh-layout`). -/
def roundRho (ℓ K v : ℕ) : ℕ := (v - layoutB0 ℓ K) % K

/-! ## 2. Costs -/

/-- Cost bound of all record-axis rounds (Theorem 6.5, `thm:direct-fft`): `V_*·((D+1)·K + ℓ·⌈d^{λ'}⌉₊ + ℓ + 1)`
(at most `K` prefix rounds of `≤ D` butterfly passes at internal width `≤ w + D`, at most `ℓ`
chunk-round layer calls, `ℓ` twiddle passes) `+ ℓ·R·mulW(2w+1)` (the twiddle products)
`+ 2^{m₀}·(w + m₀ + 1)^J` (per-record address work), with the volume
`V_* = cvolCube m₀ r (w + 8d)` (it covers the widths `w` and `w + D`), `R = 2^{m₀}·r`,
`d = D + 1`. -/
noncomputable def roundsCost (lam' : ℝ) (J D ℓ K w m : ℕ) : ℕ :=
  cvolCube m (2 ^ ℓ) (w + 8 * (D + 1)) *
      ((D + 1) * K + ℓ * ⌈((D + 1 : ℕ) : ℝ) ^ lam'⌉₊ + ℓ + 1) +
    ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + 2 ^ m * (w + m + 1) ^ J

/-- **Cost bound of the Walsh middle** (Theorem 6.5, eq. `eq:direct-fft-cost`:
`O(V[dK + ℓ d^{λ'} + ℓ 𝖬(P+2)/P])`):
`V_*·((D+1)·K + ℓ·⌈d^{λ'}⌉₊ + ℓ + 1) + ℓ·R·mulW(2w+1) + 2^{m₀}·(w + m₀ + 1)^J + 2^ℓ·(w + 1)^J`,
with the lifted volume `V_* = cvolCube m₀ r (w + 8d)` (the positional maps run their CNOT batches
at width `w + 8d`; `V ≤ V_*`), `R = 2^{m₀}·r`, `r = 2^ℓ`, `d = D + 1`. The last two terms are the
explicit lower-order terms (per-record address work; table construction). -/
noncomputable def midCost (lam' : ℝ) (J D ℓ K w m : ℕ) : ℕ :=
  cvolCube m (2 ^ ℓ) (w + 8 * (D + 1)) *
      ((D + 1) * K + ℓ * ⌈((D + 1 : ℕ) : ℝ) ^ lam'⌉₊ + ℓ + 1) +
    ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + 2 ^ m * (w + m + 1) ^ J + 2 ^ ℓ * (w + 1) ^ J

/-! ## 3. Contracts: the parts of Theorem 6.5 -/

/-- **[CONTRACT] K4.1, the phase table** (Lemma 6.1, `lem:phase-table`; Section 6.4, "one master
`2r`-entry phase table serves all rounds").
* Named stacks (`Fin 3`): `1` the header `midHdr q ℓ K w a` (restored), `2` the table stack: it
  receives `tabSyms w q ℓ (phaseTable q ℓ)` on top of its old content. Stack `0` is unchanged.
* Hypotheses: `MidShapeOK q ℓ K w a` (it gives `8 ≤ q`, `ℓ ≤ q` of Lemma 6.1 and `q + 2 ≤ w`).
* The entries are the computable numerators `phaseTableNum q ℓ j`
  (`Math/Walsh/PhaseTable.lean`; `gridInt q (phaseTable q ℓ j) = phaseTableNum q ℓ j`), which use
  IntMul's certified evaluator `computableStdCharWithProgramCost`; W7 has a machine kernel for it
  (`W7_stdChar`, `Contracts/W7/Kernels.lean:31`, cost `C(q + |den| + 1)^4` per entry).
* Cost `C·(2^ℓ·(w + 1)^J + |midHdr|)` (`2r` entries, `poly(q)` each; Lemma 6.1 gives `O(q^3)` per entry,
  W7 gives `(q + ℓ + 9)^4`; plus reading the header). -/
def PhaseTableMachineStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      Runs Pr S (Function.update S (.inl 2) (tabSyms w q ℓ (phaseTable q ℓ) ++ S (.inl 2)))
        (fun _ => True) (C * (2 ^ ℓ * (w + 1) ^ J + (midHdr q ℓ K w a).length))

/-- **[CONTRACT] K4.2, the last axis** (stage (i) of Theorem 6.5, `thm:direct-fft`, Section 6.4,
"Last axis").
* Named stacks (`Fin 3`): `0` the cube array (in place), `1` the header `midHdr q ℓ K w a`, `2` the
  phase table `tabSyms w q ℓ θt` (both restored).
* Hypotheses: `MidShapeOK q ℓ K w a`, a disk-grid table (`TabOK q ℓ θt`), a disk-grid input at
  precision `q`.
* Effect: every record (length `r = 2^ℓ`) gets the rounded normalized DIF levels `s = 0, …, ℓ-1`
  (half-sum and half-difference exactly, then `Q_q`; the lower output times its table phase, exact
  product, then `Q_q`), then the bit reversal of the coefficient index: the array becomes
  `lastAxisFFT q ℓ θt z` (`Math/Walsh/DirectFFT.lean`).
* Cost `C·(ℓ·R·mulW(2w+1) + (ℓ + 1)·V + 2^ℓ·(w + 1)^J + |midHdr|)`, `V = cvolCube m₀ r w`,
  `R = 2^{m₀}·r`:
  `O(rq + r𝖬(q+2))` per record and level, `O(rqℓ)` for the reversal, with stage tables extracted
  once per level from the master table and replayed across blocks (Section 6.4). -/
def RecordDIFStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest trest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → TabOK q ℓ θt → ArrOnDiskGrid q z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      S (.inl 2) = tabSyms w q ℓ θt ++ trest →
      Runs Pr S
        (Function.update S (.inl 0) (carrSyms w (encCube q (lastAxisFFT q ℓ θt z)) ++ rest))
        (fun _ => True)
        (C * (ℓ * 2 ^ addrBits a * 2 ^ ℓ * mulW (2 * w + 1) +
          (ℓ + 1) * cvolCube (addrBits a) (2 ^ ℓ) w + 2 ^ ℓ * (w + 1) ^ J +
          (midHdr q ℓ K w a).length))

/-- **[CONTRACT] K4.3, the positional maps `L` and `U`** (stages (ii) and (iv) of Theorem 6.5,
`thm:direct-fft`; Lemma 6.3, `lem:walsh-layout`: "`L` and `U` are compiled in time polynomial in `q`
and executed exactly by Theorem 5.8").
* Named stacks (`Fin 3`): `0` the cube array (in place), `1` the header `midHdr q ℓ K w a`
  (restored); stack `2` is unchanged.
* Hypotheses: `MidShapeOK q ℓ K w a`; every CNOT-batch call is admissible
  (`SliceCallsBand Band q (D+1) (2^ℓ) w K m₀`); a disk-grid input at precision `q`.
* Effect: the array becomes `posPermArr (layoutMap sel ℓ K a) z` (exact record permutation;
  `layoutMap .L = layoutL`, `layoutMap .U = layoutU = (L ∘ B)^{-1}`, `Math/Walsh/Layout.lean`).
* Cost `C·(permCost lam' J (D+1) r w K m₀ + |midHdr|)` (Theorem 5.8 with `d = D + 1`; Section 6.4
  bound it by `O(Vℓ d^{λ'})` since `m₀/d ≤ ℓ`, `K ≤ ℓ - 1`), including the compilation of the map
  and reading the header. -/
def LayoutExecStmt (Band : LayerRT → Prop) (lam' : ℝ) (sel : LayoutSel) : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → SliceCallsBand Band q (D + 1) (2 ^ ℓ) w K (addrBits a) →
      ArrOnDiskGrid q z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (posPermArr (layoutMap sel ℓ K a) z)) ++ rest))
        (fun _ => True)
        (C * (permCost lam' J (D + 1) (2 ^ ℓ) w K (addrBits a) + (midHdr q ℓ K w a).length))

/-- **[CONTRACT] K4.4, a prefix round** (Theorem 6.5, `thm:direct-fft`, stage (iii): prefix rounds
apply exact individual butterflies before a single truncation).
* Named stacks (`Fin 4`): `0` the cube array (in place), `1` the header `midHdr q ℓ K w a`, `3` the
  round index `natSyms v` (both restored); stack `2` is unchanged.
* Hypotheses: `MidShapeOK q ℓ K w a`, `v < ℓ`, `v` is not a chunk round (`v = ℓ - 1` or
  `v < b₀`), a disk-grid input at precision `q`.
* Effect: all participating `H_0` factors exactly (positions `roundSet ℓ K a v`, `≤ D` of them),
  then one `Q_q`: the array becomes `truncArr q (hT (roundSet ℓ K a v) z)`
  (`WStep.butterflies`, the `roundStep` of a prefix round).
* Cost `C·((D + 1)·V_D + 2^{m₀}·(w + m₀ + 1)^J + |midHdr|)`, `V_D = cvolCube m₀ r (w + D)`: the
  exact butterflies need `q + D + O(1)` bits per component (Section 6.4), so each of the `≤ D + 1`
  passes runs at width `≤ w + D`. -/
def PrefixRoundStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 4) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest crest : List Sym) (S : KLoc (Fin 4) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → v < ℓ → ¬ IsChunkRound ℓ K v → ArrOnDiskGrid q z →
      BlkTerm rest → TermOK crest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      S (.inl 3) = natSyms v ++ crest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (truncArr q (hT (roundSet ℓ K a v) z))) ++ rest))
        (fun _ => True)
        (C * ((D + 1) * cvolCube (addrBits a) (2 ^ ℓ) (w + D) +
          2 ^ addrBits a * (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

/-- **[CONTRACT] K4.5, a chunk round = one layer call** (Theorem 6.5, `thm:direct-fft`, stage (iii);
Proposition A.11, `prop:prop14-param`; Lemma 6.3, `lem:walsh-layout`).
* Named stacks (`Fin 4`): `0` the cube array (in place), `1` the header `midHdr q ℓ K w a`, `3` the
  round index `natSyms v` (both restored); stack `2` is unchanged.
* Hypotheses: `MidShapeOK q ℓ K w a`; `v` is a chunk round (`b₀ ≤ v ≤ ℓ - 2`); its chunks fit in
  the address
  (`j₀ + DK ≤ m₀`, `j₀ = roundJ0 ℓ K a v`; part of Lemma 6.3,
  `WalshLayoutRoundSliceStmt`); the layer call on the shape `[2^{j₀}] × [2^K]^D × [2^{nS}]`,
  `nS = m₀ - j₀ - DK`, bit `ρ = roundRho ℓ K v`, at precision `q` is admissible; a disk-grid input.
* Effect: the array becomes `Q_q(H_T z)` with `T = slicePos m₀ K j₀ D ρ`; this is
  `WStep.run idealLayer r (roundStep q D ℓ K a v) z` by `sliceCall_eq`.
* Cost `C·(layerCost lam' t + (w + m₀ + 1)^J + |midHdr|)` (one layer call plus computing its
  header from `v`, the header and the named-slot table). -/
def ChunkRoundStmt (Band : LayerRT → Prop) (lam' : ℝ) : Prop :=
  ∃ J : ℕ, KContract (Fin 4) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest crest : List Sym) (S : KLoc (Fin 4) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → IsChunkRound ℓ K v →
      roundJ0 ℓ K a v + D * K ≤ addrBits a →
      Band (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
        (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) →
      ArrOnDiskGrid q z → BlkTerm rest → TermOK crest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      S (.inl 3) = natSyms v ++ crest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (truncArr q (hT (slicePos (addrBits a) K (roundJ0 ℓ K a v) D
            (roundRho ℓ K v)) z))) ++ rest))
        (fun _ => True)
        (C * (layerCost lam' (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
            (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) +
          (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

/-- **[CONTRACT] K4.6, one combined twiddle per record** (Section 6.3, `sec:direct-fft-twiddle`;
round protocol eq. `eq:round-protocol`; Lemma 6.2, `lem:disk-product`).
* Named stacks (`Fin 4`): `0` the cube array (in place), `1` the header `midHdr q ℓ K w a`, `2` the
  table `tabSyms w q ℓ θt`, `3` the round index `natSyms v` (all restored).
* Hypotheses: `MidShapeOK q ℓ K w a`, `v < ℓ`, a disk-grid table, a disk-grid input at
  precision `q`.
* Effect: for every record `x` the integer `J(x) = twJ ℓ K a v x` (exact, through the named-slot
  table, once per record) selects the single phase `θ̃_{2J(x)}`, which multiplies every coefficient
  of the record (exact product, then `Q_q`): the array becomes
  `truncArr q (diagArr (fun x => θt (2 * twJ ℓ K a v x)) z)` (`WStep.diag` then
  `WStep.trunc q` of `roundsProg`).
* Cost `C·(R·mulW(2w+1) + V + 2^{m₀}·(w + m₀ + 1)^J + |midHdr|)` (four integer products per
  coefficient; one table scan and the address arithmetic per record, Section 6.4). -/
def TwiddlePassStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 4) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest trest crest : List Sym) (S : KLoc (Fin 4) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → v < ℓ → TabOK q ℓ θt → ArrOnDiskGrid q z →
      BlkTerm rest → TermOK crest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      S (.inl 2) = tabSyms w q ℓ θt ++ trest →
      S (.inl 3) = natSyms v ++ crest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (truncArr q (diagArr (fun x => θt (2 * twJ ℓ K a v x)) z))) ++
            rest))
        (fun _ => True)
        (C * (2 ^ addrBits a * 2 ^ ℓ * mulW (2 * w + 1) + cvolCube (addrBits a) (2 ^ ℓ) w +
          2 ^ addrBits a * (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

/-- **[CONTRACT] K4.7, all record-axis rounds** (stage (iii) of Theorem 6.5, `thm:direct-fft`:
rounds at named slots `v = ℓ-1, …, 0`, each the round protocol `z ↦ Q_q(D̃ Q_q(Hz))`, eq. `eq:round-protocol`).
* Named stacks (`Fin 3`): `0` the cube array (in place), `1` the header `midHdr q ℓ K w a`, `2` the
  table `tabSyms w q ℓ θt` (both restored).
* Hypotheses: `MidShapeOK q ℓ K w a`, every chunk-round call admissible
  (`ChunkCallsBand Band q ℓ K w a`), a disk-grid table, a disk-grid input at precision `q`.
* Effect: the array becomes `runProg idealLayer r (roundsProg q D ℓ K a θt) z` (for each
  `v`, `roundStep` — a layer call or exact butterflies plus `Q_q` — then the diagonal
  `θ̃_{2J(x)}` and `Q_q`).
* Cost `C·(roundsCost lam' J D ℓ K w m₀ + |midHdr|)`.
* Intended proof: a runtime loop over `v` (counter on a private stack) calling
  `PrefixRoundStmt` or `ChunkRoundStmt`, then `TwiddlePassStmt`. -/
def RoundsStmt (Band : LayerRT → Prop) (lam' : ℝ) : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest trest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → ChunkCallsBand Band q ℓ K w a → TabOK q ℓ θt →
      ArrOnDiskGrid q z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      S (.inl 2) = tabSyms w q ℓ θt ++ trest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a θt) z)) ++
            rest))
        (fun _ => True) (C * (roundsCost lam' J D ℓ K w (addrBits a) + (midHdr q ℓ K w a).length))

/-! ## 4. Contracts: the Walsh middle (Corollary 6.6) -/

/-- **[CONTRACT] K4, the Walsh middle transform, machine form** (Corollary 6.6,
`cor:walsh-middle`, applying Theorem 6.5, `thm:direct-fft`, at precision `q`; generic in the layer's
admissible calls `Band` and its exponent `lam'`).
* Named stacks (`Fin 2`): `0` the tensor (in place), `1` the header `midHdr q ℓ K w a` (restored).
* Hypotheses: `MidShapeOK q ℓ K w a` (Theorem 6.5's shape hypotheses at `q`, `q + 2 ≤ w`);
  `MidCallsBand Band q ℓ K w a` (every layer call admissible: chunk rounds at `q`, CNOT batches at
  `q + 8d`); the input tensor `U` has every entry in the disk on the `q`-grid (Corollary 6.6; the
  bridge's prepared array has `‖U‖_∞ ≤ 1/8`).
* Effect: stack `0` goes from `carrSyms w (encCube q (ofTensor a ℓ U))` (natural axis order, last
  axis contiguous: records = last-axis lines) to
  `carrSyms w (encCube q (ofTensor a ℓ (walshMiddle idealLayer q D ℓ K a U)))` (natural frequency
  order, Corollary 6.6). There is no other change: no hidden positional map, phase or scalar at
  either boundary, and every other stack ends as it began (private scratch clean).
* Cost `C·(midCost lam' J D ℓ K w m₀ + |midHdr|)` (eq. `eq:direct-fft-cost`; plus reading the header,
  which under `MidShapeOK` has length at most `5(w + m₀ + 1)`, a lower-order term).
* Value-level consequence (`Math/Walsh/Proofs/Middle.lean`, `walsh_middle_ideal_of`, from
  `DirectFFTStmt`): `walshMiddle idealLayer (P+2) D ℓ K a` is a middle transform (Definition 4.5)
  with `E_mid = 12ℓ`, `δ_mid = 0`.
* Not stated here: the fixed network premises (Definition A.1, `def:fixed-network-premises`, entering
  only through the layer contract) and the value-level error bound. -/
def WalshMiddleMachineGenStmt (Band : LayerRT → Prop) (lam' : ℝ) : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (U : Idx (fftShape a ℓ) → ℂ) (rest hrest : List Sym)
      (S : KLoc (Fin 2) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → MidCallsBand Band q ℓ K w a →
      (∀ j, OnDiskGrid q (U j)) → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube q (ofTensor a ℓ U)) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (ofTensor a ℓ (walshMiddle idealLayer q D ℓ K a U))) ++ rest))
        (fun _ => True) (C * (midCost lam' J D ℓ K w (addrBits a) + (midHdr q ℓ K w a).length))

/-- **[CONTRACT] K4, the Walsh middle at Proposition A.11's bands** (Corollary 6.6, `cor:walsh-middle`):
`WalshMiddleMachineGenStmt` with `Band = LayerBands p P₀` (`Contracts/Layer.lean`) for some cutoff
`P₀`, and `lam' = p.lam'`. Since `MidCallsBand` asks the CNOT-batch calls at `q + 8d` to satisfy
the same bands, the caller instantiates `p` with the halved lower constants of Lemma 5.3
(`lem:walsh-lift`, Remark A.14, `rem:transfer-lift`). -/
def WalshMiddleMachineStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, WalshMiddleMachineGenStmt (LayerBands p P₀) p.lam'

end SubNLogN.Machine
