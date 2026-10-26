/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseDefs

/-!
# Layer driver: parameter kernels (`Machine/Layer/DrvParamsDefs.lean`)

**Scope (honest summary).** Definitions and named statements (`def … : Prop`) only; nothing is
proved here. Hypotheses of `drvPost_of_parts` / `drvPre_of_parts`: from the layer header
`t.hdr = hdrSyms [P, d, r, D, A, S, K, ρ+1, w]` (restored) the parameter kernels push the derived
runtime parameters of the post-phase (`DrvPostParamsStmt`) or the pre-phase (`DrvPreParamsStmt`)
on named stacks, each on top of the stack's old content (Section A.6 (`sec:transfer-layer`)).
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Math.Networks (padR q0Of)

/-! ## Derived parameters -/

/-- Records per prefix block of the unpadded array, `2^{KD}·S`. -/
def drvKeep (t : LayerRT) : ℕ := 2 ^ (t.K * t.D) * t.S

/-- Zero records per prefix block of the padding, `(padR − 2^{q₀K})·2^{K(D−q₀)}·S` in the rows
case, `0` otherwise. -/
noncomputable def drvNpad (t : LayerRT) : ℕ :=
  open Classical in
  if DrvRows t then
    (padR t.d t.K - 2 ^ (q0Of t.d * t.K)) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S)
  else 0

/-- The rows flag as one symbol. -/
noncomputable def drvRowsSym (t : LayerRT) : Sym :=
  open Classical in .bit (decide (DrvRows t))

/-- The post-phase phase offset `(4 − ⌊D/2⌋ mod 4) mod 4` (so that `i^{offset} = (−i)^{⌊D/2⌋}`). -/
def drvPostC (t : LayerRT) : ℕ := (4 - t.D / 2 % 4) % 4

/-- The post-phase total right shift `Δ + ⌊D/2⌋ + D mod 2`. -/
def drvPostShift (t : LayerRT) : ℕ := drvDelta t + t.D / 2 + t.D % 2

/-- The number of individual kernels of phase 1, `min(q₀, D)`. -/
noncomputable def drvQ1 (t : LayerRT) : ℕ := min (q0Of t.d) t.D

/-- The record-index weight of the selected bit of chunk `0`, `S·2^{K(D−1)+ρ}`. -/
def drvW0 (t : LayerRT) : ℕ := t.S * 2 ^ (t.K * (t.D - 1) + t.ρ)

/-! ## Statements -/

/-- Final stacks of `DrvPostParamsStmt`. -/
noncomputable def drvPostParamsPost {E : Type} (t : LayerRT) (S : KLoc (Fin 8) E → List Sym) :
    KLoc (Fin 8) E → List Sym := fun l =>
  match l with
  | .inl i =>
    if i.val = 1 then natSyms (drvKeep t) ++ S l
    else if i.val = 2 then natSyms (drvNpad t) ++ S l
    else if i.val = 3 then drvRowsSym t :: S l
    else if i.val = 4 then
      hdrSyms [t.S, t.K, t.ρ, t.D, drvPostC t, t.D % 2, drvWg t, drvWg t + 1] ++ S l
    else if i.val = 5 then natSyms (drvWg t + 1) ++ S l
    else if i.val = 6 then natSyms t.w ++ S l
    else if i.val = 7 then natSyms (drvPostShift t) ++ S l
    else S l
  | .inr _ => S l

/-- **[CONTRACT] Post-phase parameters** (Section A.6 (`sec:transfer-layer`)). Named stacks (`Fin 8`): `0` the
header `t.hdr` (restored; anything may lie below it); `1`…`7` receive, on top of their old content,
`natSyms (drvKeep t)`, `natSyms (drvNpad t)`, the rows flag `drvRowsSym t`, the phase-scan header
`hdrSyms [S, K, ρ, D, drvPostC t, D mod 2, w_g, w_g + 1]`, `natSyms (w_g + 1)`, `natSyms w`,
`natSyms (drvPostShift t)`. Every other stack is unchanged (restored convention). Cost
`C·(|hdr| + D·K + 1)^J` for one exponent `J`. -/
def DrvPostParamsStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 8) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 8) E → List Sym),
      S (.inl 0) = t.hdr ++ hrest →
      Runs Pr S (drvPostParamsPost t S) (fun _ => True)
        (C * (t.hdr.length + t.D * t.K + 1) ^ J)

/-- Final stacks of `DrvPreParamsStmt`. -/
noncomputable def drvPreParamsPost {E : Type} (t : LayerRT) (S : KLoc (Fin 12) E → List Sym) :
    KLoc (Fin 12) E → List Sym := fun l =>
  match l with
  | .inl i =>
    if i.val = 1 then natSyms t.w ++ S l
    else if i.val = 2 then natSyms (drvWg t) ++ S l
    else if i.val = 3 then natSyms (drvDelta t) ++ S l
    else if i.val = 4 then hdrSyms [t.S, t.K, t.ρ, t.D, 0, 0, drvWg t, drvWg t] ++ S l
    else if i.val = 5 then natSyms (drvQ1 t) ++ S l
    else if i.val = 6 then natSyms (drvW0 t) ++ S l
    else if i.val = 7 then natSyms t.K ++ S l
    else if i.val = 8 then drvRowsSym t :: S l
    else if i.val = 9 then natSyms (drvKeep t) ++ S l
    else if i.val = 10 then natSyms (drvNpad t) ++ S l
    else if i.val = 11 then natSyms t.r ++ S l
    else S l
  | .inr _ => S l

/-- **[CONTRACT] Pre-phase parameters** (Section A.6 (`sec:transfer-layer`)). Named stacks (`Fin 12`): `0` the
header `t.hdr` (restored; anything may lie below it); `1`…`11` receive, on top of their old
content, `natSyms w`, `natSyms w_g`, `natSyms Δ`, the phase-scan header
`hdrSyms [S, K, ρ, D, 0, 0, w_g, w_g]`, `natSyms (drvQ1 t)`, `natSyms (drvW0 t)`, `natSyms K`, the
rows flag `drvRowsSym t`, `natSyms (drvKeep t)`, `natSyms (drvNpad t)`, `natSyms r`. Every other stack
is unchanged (restored convention). Guards `ρ < K` and `1 ≤ D` (they make `drvW0 t` have at most
`K·D + bitLen S` bits; without them `natSyms (drvW0 t)` can be exponential in `|hdr|`). Cost
`C·(|hdr| + D·K + 1)^J` for one exponent `J`. -/
def DrvPreParamsStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 12) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 12) E → List Sym),
      t.ρ < t.K → 1 ≤ t.D → S (.inl 0) = t.hdr ++ hrest →
      Runs Pr S (drvPreParamsPost t S) (fun _ => True)
        (C * (t.hdr.length + t.D * t.K + 1) ^ J)

end SubNLogN.Machine.Layer
