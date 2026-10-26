/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvParamsDefs
import SubNLogN.Machine.Layer.DrvPostMath

/-!
# Layer driver pre-phase: value-bridge statements (`Machine/Layer/DrvPreMathDefs.lean`)

**Scope (honest summary).** Definitions and named statements (`def … : Prop`) only; nothing is
proved here. They are hypotheses of `drvPre_of_parts` (`Machine/Layer/DrvPre*.lean`) and relate
the value-level semantics of phase 1 and of the row reshape (`drvA1`, `drvStageIn`,
`Machine/Layer/DriverSpec.lean`) to integer-level list operations on the stored array
(`Contracts/Records.lean` format, lexicographic record order of `layerAddrs`):
* `ph1Int t`: `𝒮_D` (`phaseRec S K ρ D 0 0`), then for `j < min(q₀, D)` the kernel pass
  `ph1Step t · j`: blocks of `2·drvWj t j` consecutive records, each becoming `cgateBlock (drvWj t j)`
  of itself (`drvWj t j = S·2^{K(D-1-j)+ρ}` is the record-index weight of the selected bit of chunk
  `j`, so records `i` and `i + W` of a block differ exactly in that bit).
* `DrvPh1BridgeStmt`: for a disk-grid input and `min(q₀, D) ≤ Δ` (every halving of the kernels is
  exact at precision `P + Δ`), the stored `drvA1 t z` at precision `P + Δ` is `ph1Int t` of the
  stored `z` at precision `P + Δ`.
* `DrvPadBridgeStmt`: (rows case) the stored `drvStageIn t h z` is the stored `drvA1 t z` with
  `drvNpad t` zero records after every prefix block of `drvKeep t` records.
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh

/-- Record-index weight of the selected bit of chunk `j`: `S·2^{K(D-1-j)+ρ}`. -/
def drvWj (t : LayerRT) (j : ℕ) : ℕ := t.S * 2 ^ (t.K * (t.D - 1 - j) + t.ρ)

/-- Number of kernel blocks of chunk `j`: `A·2^{Kj + (K-1-ρ)}` (so that
`drvNBj t j · 2·drvWj t j = M` for `j < D`, `ρ < K`). -/
def drvNBj (t : LayerRT) (j : ℕ) : ℕ := t.A * 2 ^ (t.K * j + (t.K - 1 - t.ρ))

/-- One kernel pass of phase 1 on the stored array (chunk `j`). -/
def ph1Step (t : LayerRT) (v : List (List CInt)) (j : ℕ) : List (List CInt) :=
  ((DrvPPAux.chunksOf (2 * drvWj t j) (drvNBj t j) v).map (cgateBlock (drvWj t j))).flatten

/-- Phase 1 on the stored array: `𝒮_D`, then the kernel passes `j < min(q₀, D)`. -/
noncomputable def ph1Int (t : LayerRT) (v : List (List CInt)) : List (List CInt) :=
  (List.range (drvQ1 t)).foldl (ph1Step t) (v.mapIdx (phaseRec t.S t.K t.ρ t.D 0 0))

/-- **[MATH] Phase 1 on the stored array.** For a disk-grid input `z` at precision `P`, `ρ < K`,
`1 ≤ D` and `min(q₀, D) ≤ Δ`: the phase-1 array `drvA1 t z` (the value-level `𝒮_D` and individual kernels),
stored at precision `P + Δ`, is `ph1Int t` of `z` stored at precision `P + Δ`. -/
def DrvPh1BridgeStmt : Prop :=
  ∀ (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r),
    t.ρ < t.K → 1 ≤ t.D → drvQ1 t ≤ drvDelta t → ArrOnDiskGrid t.P z →
    encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) (drvA1 t z) =
      ph1Int t (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) z)

/-- **[MATH] The row reshape on the stored array** (rows case; any precision `F`). The stored stage
input `drvStageIn t h z` is the stored phase-1 array `drvA1 t z` with `drvNpad t` zero records
(`r` coefficients `(0, 0)`) inserted after every prefix block of `drvKeep t` records. -/
def DrvPadBridgeStmt : Prop :=
  ∀ (t : LayerRT) (h : DrvRows t) (hA : 0 < t.A) (hS : 0 < t.S) (F : ℕ)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r),
    encArr F (layerAddrs (drvA' t) t.K (drvD' t) t.S (Nat.mul_pos hA h.2) hS) (drvStageIn t h z) =
      ((DrvPPAux.chunksOf (drvKeep t) t.A
        (encArr F (layerAddrs t.A t.K t.D t.S hA hS) (drvA1 t z))).map
        (padBlock (drvNpad t) t.r)).flatten

end SubNLogN.Machine.Layer
