/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Net
import SubNLogN.Machine.AppC.C5Main
import SubNLogN.Machine.K1.DigitPairPermMix

/-!
# Proposition A.7 kit builder, part 1 (`AppC/C5KitDefs.lean`): chosen kernels, layout, embeddings

From the leaf hypotheses (`Leaves q D`: L2-L5 and the validity side conditions) and the proved
kernels (`k1PairPermMix_holds` for the level-`0` digit swap, `k2DistributeBlk_holds`,
`k2MergeBlk_holds`), choose one kernel per instance (`KPack.of`); lay out all named slots
(`Slot W`) and all kernel scratch on `KLoc (Fin 6) (KE hL)`, the six named stacks of
`C5InterchangeStmt` first; registers are the product of all kernel registers. Every kernel call is
`callInj` along an injective embedding `emb` (named stacks to slots, scratch to its own region). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus

/-- The type of a kernel spec with named stacks `N`. -/
abbrev KSpec (N : Type) : Type 1 :=
  (E : Type) → [Fintype E] → [DecidableEq E] → (R : Type) → ℕ → Prog (KLoc N E) (fun _ => Sym) R →
    Prop

/-- A chosen kernel meeting a spec. -/
structure KPack (N : Type) (spec : KSpec N) where
  E : Type
  instF : Fintype E
  instD : DecidableEq E
  R : Type
  P : Prog (KLoc N E) (fun _ => Sym) R
  C : ℕ
  finR : Finite R
  neR : Nonempty R
  closed : P.Closed
  spec : @spec E instF instD R C P

instance {N : Type} {spec : KSpec N} (p : KPack N spec) : Fintype p.E := p.instF
instance {N : Type} {spec : KSpec N} (p : KPack N spec) : DecidableEq p.E := p.instD
instance {N : Type} {spec : KSpec N} (p : KPack N spec) : Finite p.R := p.finR
instance {N : Type} {spec : KSpec N} (p : KPack N spec) : Nonempty p.R := p.neR

theorem KPack.nonempty {N Par : Type} {spec : Par → KSpec N} (h : KContract N Par spec)
    (p : Par) : Nonempty (KPack N (spec p)) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨E, iF, iD, R, P, h1, h2, h3, h4⟩ := hC p
  exact ⟨⟨E, iF, iD, R, P, C, h1, h2, h3, h4⟩⟩

/-- The chosen kernel of a `KContract` at parameter `p`. -/
noncomputable def KPack.of {N Par : Type} {spec : Par → KSpec N} (h : KContract N Par spec)
    (p : Par) : KPack N (spec p) :=
  Classical.choice (KPack.nonempty h p)

/-- **The leaf hypotheses of the Proposition A.7 kit** for a network instance `D` (L2-L5, plus the validity of
its stream operations and the distinctness of the roles of every XOR). -/
structure Leaves (q : ℕ) {W m : ℕ} (D : NetData W m) : Prop where
  stream : ∀ op : StreamOp m, C5StreamStmt q m op
  valid : ∀ o, ∀ op ∈ D.ops o, op.Valid q
  xor : C5XorStmt
  desc : ∀ i j : Fin m, C5DescStmt q m i j
  rowsz : C5RowSizeStmt q m
  gates_ne : ∀ g, ∀ p ∈ D.gates g, p.1 ≠ p.2

/-- Positions of elementary stream operations: (macro, index in the macro). -/
abbrev SIdx {W m : ℕ} (D : NetData W m) : Type := Σ o : Fin D.nOps, Fin (D.ops o).length

/-- The elementary stream operation at a position. -/
def SIdx.op {W m : ℕ} {D : NetData W m} (i : SIdx D) : StreamOp m := (D.ops i.1)[i.2.val]

theorem SIdx.op_mem {W m : ℕ} {D : NetData W m} (i : SIdx D) : i.op ∈ D.ops i.1 :=
  List.getElem_mem _

section Packs

variable {q W m : ℕ} {D : NetData W m} (hL : Leaves q D)

/-- L2 kernels, one per elementary stream position. -/
noncomputable def pkS (i : SIdx D) :=
  KPack.of (hL.stream i.op (hL.valid i.1 i.op (SIdx.op_mem i))) ()

/-- The L3 kernel. -/
noncomputable def pkX := KPack.of hL.xor ()

/-- L4 kernels, one per pivot. -/
noncomputable def pkD (ij : Fin m × Fin m) := KPack.of (hL.desc ij.1 ij.2) ()

/-- The L5 kernel. -/
noncomputable def pkR := KPack.of hL.rowsz ()

end Packs

/-- The level-`0` kernel: the digit-pair swap `K1PairPermMix` with `π = prodComm` (proved). -/
noncomputable def pkB (q : ℕ) [NeZero q] :=
  KPack.of (K1Digit.k1PairPermMix_holds q (Equiv.prodComm (Fin q) (Fin q))) ()

/-- The distribution kernel (proved). -/
noncomputable def pkDi (W : ℕ) := KPack.of (k2DistributeBlk_holds W) ()

/-- The merge kernel (proved). -/
noncomputable def pkMe (W : ℕ) (ρ : Equiv.Perm (Fin W)) := KPack.of (k2MergeBlk_holds W ρ) ()

/-- A lens on one component of a dependent function. -/
def piLens {ι : Type} [DecidableEq ι] (β : ι → Type) (i : ι) : Lens (∀ j, β j) (β i) where
  get f := f i
  set f x := Function.update f i x
  get_set f x := Function.update_self i x f
  set_get f := Function.update_eq_self i f
  set_set f x y := Function.update_idem x y f

section Layout

variable {q W m : ℕ} {D : NetData W m} (hL : Leaves q D) [NeZero q]

/-- Kernel scratch of the kit. -/
abbrev SC : Type :=
  (pkB q).E ⊕ ((Σ i : SIdx D, (pkS hL i).E) ⊕ ((pkX hL).E ⊕ ((Σ ij : Fin m × Fin m, (pkD hL ij).E) ⊕
    ((pkR hL).E ⊕ ((pkDi W).E ⊕ (pkMe W D.ρ).E)))))

/-- Decidable equality of the scratch, assembled in stages (a single instance search over the
whole sum times out). -/
noncomputable instance instDecEqSC : DecidableEq (SC hL) := by
  haveI h1 : DecidableEq (Σ i : SIdx D, (pkS hL i).E) := inferInstance
  haveI h2 : DecidableEq (Σ ij : Fin m × Fin m, (pkD hL ij).E) := inferInstance
  haveI h3 : DecidableEq ((pkDi W).E ⊕ (pkMe W D.ρ).E) := inferInstance
  haveI h4 : DecidableEq ((pkR hL).E ⊕ ((pkDi W).E ⊕ (pkMe W D.ρ).E)) := inferInstance
  haveI h5 : DecidableEq ((Σ ij : Fin m × Fin m, (pkD hL ij).E) ⊕
      ((pkR hL).E ⊕ ((pkDi W).E ⊕ (pkMe W D.ρ).E))) := inferInstance
  haveI h6 : DecidableEq ((pkX hL).E ⊕ ((Σ ij : Fin m × Fin m, (pkD hL ij).E) ⊕
      ((pkR hL).E ⊕ ((pkDi W).E ⊕ (pkMe W D.ρ).E)))) := inferInstance
  haveI h7 : DecidableEq ((Σ i : SIdx D, (pkS hL i).E) ⊕ ((pkX hL).E ⊕
      ((Σ ij : Fin m × Fin m, (pkD hL ij).E) ⊕ ((pkR hL).E ⊕ ((pkDi W).E ⊕ (pkMe W D.ρ).E))))) :=
    inferInstance
  exact instDecidableEqSum

/-- Private stacks of the kit: `tmp`, `tmp2`, `rsz`, the roles, and all kernel scratch. -/
abbrev KE : Type := (Fin 3 ⊕ Fin W) ⊕ SC hL

noncomputable instance instDecEqKE : DecidableEq (KE hL) := instDecidableEqSum

noncomputable instance instDecEqKK : DecidableEq (KLoc (Fin 6) (KE hL)) := instDecidableEqSum

/-- The kit layout: the six named stacks of `C5InterchangeStmt`, then `KE`. -/
abbrev KK : Type := KLoc (Fin 6) (KE hL)

/-- Registers: the `Option Sym` register of the macros, then all kernel registers. -/
abbrev RG : Type :=
  Option Sym × ((pkB q).R × ((∀ i : SIdx D, (pkS hL i).R) × ((pkX hL).R ×
    ((∀ ij : Fin m × Fin m, (pkD hL ij).R) × ((pkR hL).R × ((pkDi W).R × (pkMe W D.ρ).R))))))

/-- Placement of the named slots. -/
def slotK : Slot W → KK hL
  | .io => .inl 0
  | .ck => .inl 1
  | .cR => .inl 2
  | .cN1 => .inl 3
  | .cG => .inl 4
  | .cB => .inl 5
  | .tmp => .inr (.inl (.inl 0))
  | .tmp2 => .inr (.inl (.inl 1))
  | .rsz => .inr (.inl (.inl 2))
  | .role w => .inr (.inl (.inr w))

theorem slotK_inj : Function.Injective (slotK hL) := by
  intro a b h
  cases a <;> cases b <;> simp_all [slotK]

/-- Locate the role stacks. -/
def roleOfK : KK hL → Option (Fin W)
  | .inr (.inl (.inr w)) => some w
  | _ => none

theorem roleOfK_slot (x : Slot W) : roleOfK hL (slotK hL x) = x.roleIdx := by
  cases x <;> rfl

theorem roleOfK_eq_some (key : KK hL) (w : Fin W) (h : roleOfK hL key = some w) :
    key = slotK hL (.role w) := by
  rcases key with i | ((i | w') | e)
  · simp [roleOfK] at h
  · simp [roleOfK] at h
  · simp only [roleOfK, Option.some.injEq] at h
    subst h
    rfl
  · simp [roleOfK] at h

/-- Embedding of a kernel: named stacks to slots (through `f`), scratch to its region (`g`). -/
def emb {L E' : Type} (f : L → Slot W) (g : E' → SC hL) : KLoc L E' → KK hL :=
  Sum.elim (fun l => slotK hL (f l)) (fun e => .inr (.inr (g e)))

theorem emb_inj {L E' : Type} {f : L → Slot W} {g : E' → SC hL} (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (emb hL f g) := by
  refine Function.Injective.sumElim (fun a b h => hf (slotK_inj hL h))
    (fun a b h => hg (by simpa using h)) ?_
  intro a b h
  revert h
  cases f a <;> simp [slotK]

/-- The array slot of a stream op: `io` (`none`) or role `w`. -/
def arrSlot {W : ℕ} : Option (Fin W) → Slot W
  | none => .io
  | some w => .role w

end Layout

end SubNLogN.Machine.C5
