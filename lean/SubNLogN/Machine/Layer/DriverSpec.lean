/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.CCore
import SubNLogN.Math.Networks.AppCLayerProc

/-!
# Layer driver, part 1: stage functions and named leaf statements (`Machine/Layer/DriverSpec.lean`)

**Scope (honest summary).** Definitions and named statements (`def … : Prop`) only; nothing is
proved here. They are the hypotheses of the reduction `layerMachine_of_parts`
(`Machine/Layer/Driver.lean`), which derives `LayerMachineStmt p` (Proposition A.11, machine part)
from `CCoreStmt p βn βd` and these statements.

## Driver chronology (Proposition A.11 (`prop:prop14-param`), Section A.6 (`sec:transfer-layer`))
1. **Pre-phase** (`DrvPreStmt`, passes 0-4). Read the header. Re-encode to width
   `w_g = P + 2Δ + 3` at precision `P + Δ`, with `Δ = drvDelta t = P`. Apply phase 1 of the value-level
   `layerRun` (`𝒮_D`, then the individual kernels on the first `min q₀ D` chunks). In the rows case
   (`DrvRows`), reshape the first `q₀` chunks into the row field and pad the rows to `padR`.
   Push the piece descriptors on `desc`.
2. **Pieces** (in the reduction). For every base-`m` piece `(k, j0)` of the remaining `D - q₀`
   chunks (`piecesOf`), call the C-core (`CCoreStmt`), then drop the descriptor.
3. **Post-phase** (`DrvPostStmt`, passes 6-10). Unpad (`restrictArr`), apply phase 3 (`𝒮_D`,
   `b^D`, truncation `Q_P`), and write the result at the caller's width `w`.

The stage functions use the value-level semantics (`Math/Networks/AppCLayerProc.lean`: `layerPhase1`,
`embedArr`, `restrictArr`, `layerPhase3`, `piecesOf`, `q0Of`, `padR`, `useRows`) read through
`encodeArr`/`decodeArr`. The pieces use the same `cCoreVal` as `CCoreStmt` and
`CCoreProcCorrectStmt`. The math statements (`DrvFunctionalStmt`, `DrvCtxStmt`, `DrvCostStmt`) are
pure value/arithmetic facts. `DrvFunctionalStmt` follows from `Prop71LayerSpecStmt` (`Prop71` is the
earlier-draft identifier prefix for Proposition A.11 (`prop:prop14-param`), kept for stability),
`CCoreProcCorrectStmt` and `DecodeEncodeAddrStmt` (proved in `DrvFunctional.lean`).
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Machine
open SubNLogN.Math.Networks (q0Of padR piecesOf useRows layerPhase1 layerPhase3 topClass
  embedArr restrictArr encodeArr decodeArr cCoreVal)
open SubNLogN.Math.Networks.Model (ProcK)

/-! ## Parameters of the driver -/

/-- Guard allocation of the driver, `Δ = P`. The driver works at precision `2P` and width
`3P + 3`. -/
def drvDelta (t : LayerRT) : ℕ := t.P

/-- Guarded component width `w_g = P + 2Δ + 3`. -/
def drvWg (t : LayerRT) : ℕ := t.P + 2 * drvDelta t + 3

/-- The row-reshape case of the value-level `layerRun`: more than `q₀` chunks (and a positive padded range). -/
abbrev DrvRows (t : LayerRT) : Prop := useRows t.D t.K t.d

/-- Prefix range of the C-core stage, `A · padR`. -/
noncomputable abbrev drvA' (t : LayerRT) : ℕ := t.A * padR t.d t.K

/-- Chunk count of the C-core stage, `D - q₀`. -/
noncomputable abbrev drvD' (t : LayerRT) : ℕ := t.D - q0Of t.d

/-! ## Stage arrays (value-level semantics) -/

/-- Phase 1 of the value-level `layerRun` on `LayerAddr`: `𝒮_D`, then the individual kernels on the first
`min q₀ D` chunks. -/
noncomputable def drvA1 (t : LayerRT) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) :
    RArr (LayerAddr t.A t.K t.D t.S) t.r :=
  decodeArr (ProcK.run 0 (layerPhase1 t.A t.K t.D t.S t.r t.ρ t.d) (topClass t.A t.K t.D t.S)
    (encodeArr z))

/-- The C-core stage input (rows case): phase 1, then the row reshape with zero padding
(`embedArr`). -/
noncomputable def drvStageIn (t : LayerRT) (h : DrvRows t)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r :=
  decodeArr (embedArr h.2 h.1.le
    (ProcK.run 0 (layerPhase1 t.A t.K t.D t.S t.r t.ρ t.d) (topClass t.A t.K t.D t.S)
      (encodeArr z)))

/-- The stage output (rows case): unpad (`restrictArr`), then phase 3 (`𝒮_D`, `b^D`, `Q_P`). -/
noncomputable def drvStageOut (t : LayerRT) (h : DrvRows t)
    (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) : RArr (LayerAddr t.A t.K t.D t.S) t.r :=
  decodeArr (ProcK.run 0 (layerPhase3 t.A t.K t.D t.S t.r t.ρ t.P) (topClass t.A t.K t.D t.S)
    (restrictArr h.2 h.1.le (encodeArr y)))

/-- The output in the no-rows case: phase 3 applied to the phase-1 array. -/
noncomputable def drvSmallOut (t : LayerRT) (y : RArr (LayerAddr t.A t.K t.D t.S) t.r) :
    RArr (LayerAddr t.A t.K t.D t.S) t.r :=
  decodeArr (ProcK.run 0 (layerPhase3 t.A t.K t.D t.S t.r t.ρ t.P) (topClass t.A t.K t.D t.S)
    (encodeArr y))

/-! ## Pieces, contexts, descriptors -/

/-- The pieces of the C-core stage, as `(depth k, offset j0)`: `piecesOf (D - q₀)` in the rows
case, none otherwise. -/
noncomputable def drvPieces (t : LayerRT) : List (ℕ × ℕ) :=
  open Classical in if DrvRows t then piecesOf (drvD' t) else []

/-- The C-core call context of piece `pc` with growth bound `b`. Root context `(P, d, r, Δ)`, the
stage shape `[A·padR] × [2^K]^{D-q₀} × [S]` with row range `padR`, active group at `j0 = pc.2` of
size `m^{pc.1}`. -/
noncomputable def drvCtx (t : LayerRT) (b : ℕ) (pc : ℕ × ℕ) : CCoreRT where
  P := t.P
  d := t.d
  r := t.r
  Δ := drvDelta t
  A := drvA' t
  R := padR t.d t.K
  K := t.K
  D := drvD' t
  S := t.S
  j0 := pc.2
  k := pc.1
  ρ := t.ρ
  b := b

/-- One piece: `C^{⊗ m^k}` on chunks `j0, …, j0 + m^k - 1` (the identity if the piece does not
fit). -/
noncomputable def pieceStep (t : LayerRT) (hρ : t.ρ < t.K) (pc : ℕ × ℕ)
    (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) :
    RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r :=
  if hg : pc.2 + tripleM 100 ^ pc.1 ≤ drvD' t then cCoreVal ⟨t.ρ, hρ⟩ pc.2 (tripleM 100 ^ pc.1) hg y
  else y

/-- The stage array after the first `i` pieces, starting from `y₀`. -/
noncomputable def drvYs (t : LayerRT) (hρ : t.ρ < t.K)
    (y₀ : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) (i : ℕ) :
    RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r :=
  ((drvPieces t).take i).foldl (fun y pc => pieceStep t hρ pc y) y₀

/-- The growth bound before piece `i`: `q₀` for phase 1, plus `cDepth` of the earlier pieces. -/
noncomputable def drvB (t : LayerRT) (βn βd Estar i : ℕ) : ℕ :=
  q0Of t.d + (((drvPieces t).take i).map fun pc => cDepth t.d βn βd Estar pc.1).sum

/-- End tag below the piece descriptors on `desc`. It is fresh in `hdrSyms`. -/
def drvEndTag : Sym := .tag 15

/-- The content the pre-phase pushes on `desc`: the piece descriptors (first piece on top), then
the end tag. -/
noncomputable def drvDescSyms (t : LayerRT) : List Sym :=
  ((drvPieces t).map fun pc => (drvCtx t 0 pc).hdr).flatten ++ [drvEndTag]

/-- The array after the pre-phase, at the guarded width `w_g` and precision `P + Δ`: the stage
input in the rows case, the phase-1 array otherwise. -/
noncomputable def drvMidSyms (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) : List Sym :=
  open Classical in
  if h : DrvRows t then
    carrSyms (drvWg t) (encArr (t.P + drvDelta t)
      (layerAddrs (drvA' t) t.K (drvD' t) t.S (Nat.mul_pos hA h.2) hS) (drvStageIn t h z))
  else carrSyms (drvWg t) (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) (drvA1 t z))

/-- Cost bound of the pre-phase: `V·(q₀ + 1)` plus the pushed descriptors, plus `1`. -/
noncomputable def drvPreCost (t : LayerRT) : ℕ :=
  t.vol * (q0Of t.d + 1) + (drvDescSyms t).length + 1

/-- Cost bound of the post-phase: `V + 1`. -/
def drvPostCost (t : LayerRT) : ℕ := t.vol + 1

/-! ## Leaf machine statements -/

/-- **[CONTRACT] Driver pre-phase** (Section A.6 (`sec:transfer-layer`), Proposition A.11). One
closed program on `KLoc (Fin 3) E`: named stack `0` is the array (in place), `1` the layer header
(restored), `2` the descriptor stack, which receives `drvDescSyms t` on top of its old content.
For a layer call in the bands with a disk-grid input `z` at width `w ≥ P + 2`, the array becomes
`drvMidSyms t z` (phase 1, the reshape and the padding, at width `w_g` and precision `P + Δ`).
Every other stack is unchanged. Cost `C · (V·(q₀ + 1) + |drvDescSyms t| + 1)`. -/
def DrvPreStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r)
      (rest hrest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      LayerBands p P₀ t → t.P + 2 ≤ t.w → ArrOnDiskGrid t.P z → BlkTerm rest →
      S (.inl 0) = carrSyms t.w (encLayer hA hS t.P z) ++ rest → S (.inl 1) = t.hdr ++ hrest →
      Runs Pr S
        (Function.update (Function.update S (.inl 0) (drvMidSyms t hA hS z ++ rest)) (.inl 2)
          (drvDescSyms t ++ S (.inl 2)))
        (fun _ => True) (C * drvPreCost t)

/-- **[CONTRACT] Driver post-phase** (Section A.6 (`sec:transfer-layer`), Proposition A.11). One closed
program on `KLoc (Fin 2) E`: named stack `0` is the array (in place), `1` the layer header
(restored). In the rows case the array holds a stage array `y` at width `w_g` and precision `P + Δ`
and becomes `encLayer P (drvStageOut t h y)` at width `w` (unpad, `𝒮_D`, `b^D`, truncation toward
zero). In the no-rows case the array holds `y` on the original shape and becomes
`encLayer P (drvSmallOut t y)`. Hypotheses: the growth bound `b` of `y` leaves room for the `b^D`
halvings (`b + D ≤ Δ`), and the output is a disk-grid array (so it fits `w` bits). Every other stack
is unchanged. Cost `C · (V + 1)`. -/
def DrvPostStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (rest hrest : List Sym) (b : ℕ)
      (S : KLoc (Fin 2) E → List Sym),
      LayerBands p P₀ t → t.P + 2 ≤ t.w → BlkTerm rest → b + t.D ≤ drvDelta t →
      S (.inl 1) = t.hdr ++ hrest →
      (∀ (h : DrvRows t) (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r),
        ArrGrowth t.P b y → ArrOnDiskGrid t.P (drvStageOut t h y) →
        S (.inl 0) = carrSyms (drvWg t) (encArr (t.P + drvDelta t)
          (layerAddrs (drvA' t) t.K (drvD' t) t.S (Nat.mul_pos hA h.2) hS) y) ++ rest →
        Runs Pr S
          (Function.update S (.inl 0) (carrSyms t.w (encLayer hA hS t.P (drvStageOut t h y)) ++ rest))
          (fun _ => True) (C * drvPostCost t)) ∧
      (¬ DrvRows t → ∀ y : RArr (LayerAddr t.A t.K t.D t.S) t.r,
        ArrGrowth t.P b y → ArrOnDiskGrid t.P (drvSmallOut t y) →
        S (.inl 0) = carrSyms (drvWg t) (encArr (t.P + drvDelta t)
          (layerAddrs t.A t.K t.D t.S hA hS) y) ++ rest →
        Runs Pr S
          (Function.update S (.inl 0) (carrSyms t.w (encLayer hA hS t.P (drvSmallOut t y)) ++ rest))
          (fun _ => True) (C * drvPostCost t))

/-! ## Math statements (value level and arithmetic) -/

/-- **[MATH] Functional identity of the driver chain.** In the bands, on a disk-grid input: rows
case, `drvStageOut (pieces (drvStageIn z)) = Q_P(Hz)`; no-rows case,
`drvSmallOut (drvA1 z) = Q_P(Hz)`. Proved in `DrvFunctional.lean` from `Prop71LayerSpecStmt` (its
`layerRun` has exactly these phases), `CCoreProcCorrectStmt` (each piece is `cCoreVal`) and
`DecodeEncodeAddrStmt`. -/
def DrvFunctionalStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, ∀ (t : LayerRT) (hρ : t.ρ < t.K) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r),
    LayerBands p P₀ t → ArrOnDiskGrid t.P z →
    (∀ h : DrvRows t, drvStageOut t h (drvYs t hρ (drvStageIn t h z) (drvPieces t).length) =
      truncArr t.P (layerH ⟨t.ρ, hρ⟩ z)) ∧
    (¬ DrvRows t → drvSmallOut t (drvA1 t z) = truncArr t.P (layerH ⟨t.ρ, hρ⟩ z))

/-- **[MATH] Context facts of the driver.** Given the C-core's constants `E_*` and `P₀c`, there is a
cutoff above which: every piece context satisfies `CCoreBands p P₀c`; the array before piece `i`
has growth bound `drvB i` and `drvB i + cDepth(k_i) ≤ Δ`; the final stage array (rows case) or the
phase-1 array (no-rows case) has growth bound `drvB N`; and `drvB N + D ≤ Δ`. -/
def DrvCtxStmt (p : LayerParams) (βn βd : ℕ) : Prop :=
  ∀ Estar P₀c : ℕ, ∃ P₀ : ℕ, ∀ (t : LayerRT) (hρ : t.ρ < t.K)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r),
    LayerBands p P₀ t → ArrOnDiskGrid t.P z →
    (∀ h : DrvRows t,
      (∀ i (hi : i < (drvPieces t).length),
        CCoreBands p P₀c (drvCtx t (drvB t βn βd Estar i) ((drvPieces t).get ⟨i, hi⟩)) ∧
        ArrGrowth t.P (drvB t βn βd Estar i) (drvYs t hρ (drvStageIn t h z) i) ∧
        drvB t βn βd Estar i + cDepth t.d βn βd Estar ((drvPieces t).get ⟨i, hi⟩).1 ≤ drvDelta t) ∧
      ArrGrowth t.P (drvB t βn βd Estar (drvPieces t).length)
        (drvYs t hρ (drvStageIn t h z) (drvPieces t).length)) ∧
    (¬ DrvRows t → ArrGrowth t.P (drvB t βn βd Estar 0) (drvA1 t z)) ∧
    drvB t βn βd Estar (drvPieces t).length + t.D ≤ drvDelta t

/-- **[MATH] Cost summation of the driver.** For all component constants there are `C₁` and a
cutoff such that the driver's step count, in the form produced by the reduction, is at most
`C₁ · layerCost λ' t`. Per piece: the C-core bound, `5·|hdr|` for dropping the descriptor, and `4`
for the loop test and the peek. It is expected to hold when `σ + β(1-σ) < λ'` with `β = βn/βd`,
using `ceil_volF_le_root` and the piece count `≤ (m-1)(1 + ⌊log_m d⌋)`
(`Math/Cost/Recurrence.lean`). -/
def DrvCostStmt (p : LayerParams) (βn βd : ℕ) : Prop :=
  ∀ Cpre Cpost Ccore : ℕ, ∃ C₁ P₀ : ℕ, ∀ t : LayerRT, LayerBands p P₀ t → t.P + 2 ≤ t.w →
    Cpre * drvPreCost t + Cpost * drvPostCost t +
        ((drvPieces t).map fun pc =>
          Ccore * cCoreCost p βn βd (drvCtx t 0 pc) + 5 * (drvCtx t 0 pc).hdr.length + 4).sum + 8 ≤
      C₁ * layerCost p.lam' t
end SubNLogN.Machine.Layer
