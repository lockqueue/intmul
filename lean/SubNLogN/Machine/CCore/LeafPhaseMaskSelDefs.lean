/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskDefs
import SubNLogN.Machine.Bridge.PrePostTherm

/-!
# C-core phase leaf, record-wise sign selection: interface of the parts (`LeafPhaseMaskSelDefs.lean`)

**Scope (honest summary).** Definitions and two named statements; nothing is proved here. They are
parts of the proof of `MaskSelStmt` (`CCore/LeafPhaseMaskDefs.lean`), whose kernel
(`LeafPhaseMaskSel*.lean`) works as follows:
1. emit the mask bits `maskMSB K ρ (membList ss j0 f D)` (`f = m^{k-1}`, MSB first) on a scratch
   stack `Msk`;
2. build the parity table `tab ms` on `Tb` by one refinement pass per mask bit (`tabProg`);
3. select record `i` from `vn` or `v` according to table entry `(i div S) mod 2^{KD}` (table read
   cyclically, `S` records per entry);
4. reverse the selected records onto the destination and clean up.

* `MaskTabStmt` (value): the table has `2^{KD}` entries and entry `(i div S) mod 2^{KD}` is
  `selBit ss K D S j0 f ρ i`.
* `TabProgStmt` (machine, any stack type): `tabProg Msk Tb Tb2` consumes the mask bits `ms` on `Msk`
  and replaces the table `L` on `Tb` by `ms.foldl (fun L m => refineT m L) L`.

## Conventions
The mask bits are MSB first: chunk `j = 0, …, D-1`, inside a chunk bit `t = K-1, …, 0`; the bit
`t = ρ` of chunk `j` carries the membership of `j` in a slot of `ss` (slot `s` = chunks
`j0 + s·f, …, j0 + s·f + f - 1`). One refinement step maps a table `L` to
`L.flatMap (y ↦ [y, y xor m])`, so after all steps entry `q` is the parity of the mask bits at the
`1` bits of `q` (the first mask bit is the most significant bit of `q`).
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP
open SubNLogN.Machine.CCore.LeafScalarAux

/-! ## Value level -/

/-- The chunk membership schedule: `j0` chunks outside, then slot `s = 0, …, m-1` occupies `f`
chunks with membership `s ∈ ss`, then `D - (j0 + m f)` chunks outside. -/
def membList (ss : Finset (Fin mn)) (j0 f D : ℕ) : List Bool :=
  List.replicate j0 false ++
    (List.finRange mn).flatMap (fun s => List.replicate f (decide (s ∈ ss))) ++
    List.replicate (D - (j0 + mn * f)) false

/-- The mask bits, MSB first: per chunk (membership `b`), bits `K-1, …, 0`, only bit `ρ` may be set. -/
def maskMSB (K ρ : ℕ) (mem : List Bool) : List Bool :=
  mem.flatMap fun b => List.replicate (K - 1 - ρ) false ++ b :: List.replicate ρ false

/-- One refinement step of the parity table by the mask bit `m`. -/
def refineT (m : Bool) (L : List Bool) : List Bool := L.flatMap fun y => [y, xor y m]

/-- The parity table of the mask bits `ms` (MSB first). -/
def tab (ms : List Bool) : List Bool := ms.foldl (fun L m => refineT m L) [false]

/-- **[CONTRACT, value] The parity table computes `selBit`.** -/
def MaskTabStmt : Prop :=
  ∀ (ss : Finset (Fin mn)) (K D S j0 k ρ i : ℕ), 1 ≤ k → ρ < K → j0 + mn ^ k ≤ D →
    (tab (maskMSB K ρ (membList ss j0 (mn ^ (k - 1)) D))).length = 2 ^ (K * D) ∧
    selBit ss K D S j0 (mn ^ (k - 1)) ρ i =
      (tab (maskMSB K ρ (membList ss j0 (mn ^ (k - 1)) D))).getD ((i / S) % 2 ^ (K * D)) false

/-! ## Machine: the table builder (register `PReg`, `Bridge/PrePostLoop.lean`) -/

variable {K : Type}

/-- Pop the top symbol of `k` into the register `o`. -/
def popO (k : K) : PProg K := .pop k fun v o => { v with o := o }

/-- One element of a refinement pass: pop `y` from `Tb`, push `y`, then `y xor m`, onto `Tb2`. -/
def refStep (m : Bool) (Tb Tb2 : K) : PProg K :=
  .seq (popO Tb) (.seq (.push Tb2 fun v => Sym.bit (bitOf v.o))
    (.push Tb2 fun v => Sym.bit (xor (bitOf v.o) m)))

/-- A refinement pass by the mask bit `m`: the whole table from `Tb` onto `Tb2` (refined, reversed),
then back onto `Tb` (`moveBlock` reverses). -/
def refPass (m : Bool) (Tb Tb2 : K) : PProg K :=
  .seq (.seq (peekT Tb) (.loop (fun v => isBitO v.t) (.seq (refStep m Tb Tb2) (peekT Tb))))
    ((moveBlock Tb2 Tb).liftRegs lensPO)

/-- **The table builder**: for each mask bit on `Msk` (consumed, top first), one refinement pass. -/
def tabProg (Msk Tb Tb2 : K) : PProg K :=
  .seq (peekT Msk) (.loop (fun v => isBitO v.t)
    (.seq (.seq (popO Msk) (.ite (fun v => bitOf v.o) (refPass true Tb Tb2) (refPass false Tb Tb2)))
      (peekT Msk)))

/-- **[CONTRACT, machine] The table builder**, as `Runs`: the mask bits `ms` on `Msk` are consumed,
the table `L` on `Tb` becomes `ms.foldl (fun L m => refineT m L) L`; `Tb2` (empty) is restored;
every other stack is unchanged. -/
def TabProgStmt : Prop :=
  ∀ {K : Type} [DecidableEq K] (Msk Tb Tb2 : K), Msk ≠ Tb → Msk ≠ Tb2 → Tb ≠ Tb2 →
    ∀ (ms L : List Bool) (S : K → List Sym),
      S Msk = ms.map Sym.bit → S Tb = L.map Sym.bit → S Tb2 = [] →
      Runs (tabProg Msk Tb Tb2) S
        (Function.update (Function.update S Msk []) Tb
          ((ms.foldl (fun L m => refineT m L) L).map Sym.bit))
        (fun _ => True) (30 * (2 ^ ms.length * (L.length + 1) + ms.length + 1))

end SubNLogN.Machine.CCore.PhaseMaskAux
