/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelCode
import SubNLogN.Machine.Layer.DrvPreKDefs

/-!
# C-core phase leaf: the address-dependent signs `zSlot`/`zMask` (interface, `LeafPhaseMaskDefs.lean`)

**Scope (honest summary).** Definitions and two named statements; nothing is proved here. They
split off the address-dependent part of `PhaseStmt` (`CCore/SkelDefs.lean:257`) for the phase kinds
`zSlot sl` and `zMask a` (`SkelDefs.lean:125-146`; the value-level `zSlot`/`zMask`,
`Math/Networks/AppCCore.lean:63-70`):
* `MaskSelStmt` (machine): a closed kernel that selects, record by record, between two aligned
  record arrays `v` (the input) and `vn` (its negation `×i²`), by the sign bit `selBit` of the
  record index;
* `MaskValStmt` (value): `encArr` of `runSteps [phaseStep t κ] w` is that selection, for the
  slot set `kindSlots κ`.
The phase kernel (`LeafPhase*.lean`) moves the role stream to private scratch, forms `×i²` of it
with `RotIPowStmt` (`Machine/Layer/DrvPreKDefs.lean:42`), calls `MaskSelStmt`, and identifies the
result with `MaskValStmt`.

## Address conventions
A compact role array is stored in the lexicographic order `layerAddrs A K D S`
(`Contracts/Records.lean:96`): record `i` has the address `layerAddrOfIndex A K D S hA hS i`, whose
bit `t` of chunk `j` is `chunkBit K D S i j t` (definitionally). With `f = m^(k-1)`, slot `s` is
the chunk range `[j0 + s·f, j0 + (s+1)·f)`, and the sign of record `i` is
`(-1)^(Σ_{s ∈ ss} Σ_{c < f} bit ρ of chunk j0 + s·f + c)`.
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks SubNLogN.Machine.Layer.DrvPreK

/-- Bit `t` of chunk `j` of the layer address with lexicographic index `i` (exactly as in
`layerAddrOfIndex`, `Contracts/Records.lean:90`). -/
def chunkBit (K D S i j t : ℕ) : Bool :=
  ((i / S) % 2 ^ (K * D) / 2 ^ (K * (D - 1 - j)) % 2 ^ K).testBit t

/-- The slot set of a phase kind: `{sl}` for `zSlot sl`; the image under `cubeEquiv` of the
support of `u_a` for `zMask a`; empty otherwise. -/
noncomputable def kindSlots : PhaseKind → Finset (Fin mn)
  | .zSlot sl => {sl}
  | .zMask a => (Finset.univ.filter fun p : Cube 100 => ua a p = 1).image
      fun p => Fin.cast mH_eq_mn (cubeEquiv p)
  | _ => ∅

/-- The sign bit of record `i`: the parity of the selected bits `ρ` of the chunks of the slots in
`ss` (`f` chunks per slot, slot `s` starting at chunk `j0 + s·f`). -/
def selBit (ss : Finset (Fin mn)) (K D S j0 f ρ i : ℕ) : Bool :=
  decide (Odd (∑ s ∈ ss, ∑ c ∈ Finset.range f,
    (if chunkBit K D S i (j0 + s.val * f + c) ρ then 1 else 0)))

/-- Record-wise selection: record `i` is `vn[i]` if `b i`, else `v[i]` (length of `v`). -/
def selRecs {α : Type} [Inhabited α] (b : ℕ → Bool) (v vn : List α) : List α :=
  (List.range v.length).map fun i => if b i then vn.getD i default else v.getD i default

/-- **[CONTRACT, machine] Record-wise sign selection** (static slot set `ss`). Named stacks
(`Fin 9`): `0` the array `v` (consumed), `1` the aligned array `vn` (consumed), `2` the
destination (receives the selection on top of its old content), `3`-`8` the counters `K`, `D`,
`S`, `j0`, `k`, `ρ` (`natSyms`, restored). The private scratch is clean at entry (`KClean`), every
other stack is restored. Hypotheses: `1 ≤ k`, `ρ < K`, `j0 + m^k ≤ D`, `1 ≤ S`, equal lengths.
Record `i` of the output is `vn[i]` if `selBit ss K D S j0 (m^(k-1)) ρ i`, else `v[i]`.
Cost `C·(|v| + |vn| + 2^(K·D) + S + D + 1)` (`|·| = vol`). -/
def MaskSelStmt : Prop :=
  KContract (Fin 9) (Finset (Fin mn)) fun ss E _ _ _ C P =>
    ∀ (K D S j0 k ρ : ℕ) (v vn : List (List Bool)) (rx rxn r3 r4 r5 r6 r7 r8 : List Sym)
      (St : KLoc (Fin 9) E → List Sym),
      KClean St → 1 ≤ k → ρ < K → j0 + mn ^ k ≤ D → 1 ≤ S → v.length = vn.length →
      BlkTerm rx → BlkTerm rxn →
      TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 → TermOK r8 →
      St (.inl 0) = arrSyms v ++ rx → St (.inl 1) = arrSyms vn ++ rxn →
      St (.inl 3) = natSyms K ++ r3 → St (.inl 4) = natSyms D ++ r4 →
      St (.inl 5) = natSyms S ++ r5 → St (.inl 6) = natSyms j0 ++ r6 →
      St (.inl 7) = natSyms k ++ r7 → St (.inl 8) = natSyms ρ ++ r8 →
      Runs P St
        (Function.update (Function.update (Function.update St (.inl 0) rx) (.inl 1) rxn) (.inl 2)
          (arrSyms (selRecs (selBit ss K D S j0 (mn ^ (k - 1)) ρ) v vn) ++ St (.inl 2)))
        (fun _ => True) (C * (vol v + vol vn + 2 ^ (K * D) + S + D + 1))

/-- **[CONTRACT, value] The signs `zSlot`/`zMask` on the stored array.** For `κ = zSlot sl` or
`κ = zMask a`, at a node (`1 ≤ k`) with `ρ < K` and `j0 + m^k ≤ D`, and an input on the grid of
precision `P + Δ`, the stored array (lexicographic order, precision `P + Δ`) of
`runSteps [phaseStep t κ] w` is the record-wise selection between the stored input and its
negation (`rotIPowC 2`), by `selBit (kindSlots κ) K D S j0 (m^(k-1)) ρ`. -/
def MaskValStmt : Prop :=
  ∀ (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S) (κ : PhaseKind),
    ((∃ sl, κ = .zSlot sl) ∨ (∃ a, κ = .zMask a)) →
    1 ≤ t.k → t.ρ < t.K → t.j0 + mn ^ t.k ≤ t.D →
    ∀ w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r, (∀ x k, OnGrid (t.P + t.Δ) (w x k)) →
      encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) (runSteps [phaseStep t κ] w) =
        selRecs (selBit (kindSlots κ) t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
          (encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) w)
          (mapC (rotIPowC 2) (encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) w))

end SubNLogN.Machine.CCore.LeafScalarAux
