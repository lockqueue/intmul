/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimData
import SubNLogN.Math.Networks.Proofs.InterchangeCorrectNode

/-!
# Proposition A.7 network simulation, part 6: the raw schedule of a node (`AppC/C5NetSimShape.lean`)

`rawMain fac` is the pure-network serialized event list `nodeEvents .bit 100` (whose `evOps` image is
`bitNodeOps` minus its final relabelling, `InterchangeCorrect.nodeMainOps_eq_flatMap`) with every
primitive step replaced by one stream entry, every gate by its XOR list (`gateXors`), every child
call by a call entry. `forall₂_main` relates the two lists entrywise for any relation holding on the
leaf pairs (counts, validity: `C5NetSimShape2.lean`). The outer macros: `preOps` (`D ← D − H`),
`postOps` (`D ← H − D`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Step RoleOp ProcK Elem)

theorem forall₂_append {α γ : Type} {Rl : α → γ → Prop} {a c : List α} {b d : List γ}
    (h1 : List.Forall₂ Rl a b) (h2 : List.Forall₂ Rl c d) : List.Forall₂ Rl (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem forall₂_flatMap {ι α γ : Type} {Rl : α → γ → Prop} (l : List ι) (f : ι → List α)
    (g : ι → List γ) (h : ∀ x ∈ l, List.Forall₂ Rl (f x) (g x)) :
    List.Forall₂ Rl (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact forall₂_append (h x (List.mem_cons_self ..))
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- Raw lower-triangular steps (mirror of `lowerSteps`). -/
def rawLower (w : Fin Wb) (X : Chunk) (E : Matrix (Fin mH) (Fin mH) ℚ) : List (RawOp Wb mH) :=
  (List.finRange mH).reverse.flatMap fun i =>
    [.stream w (.unit X i (E i i)), .stream w (.lowShift X i (fun j => E i j))]

/-- Raw Lemma A.6 program of one edge (mirror of `shearOps`). -/
def rawShear (w : Fin Wb) (F : FacData) : List (RawOp Wb mH) :=
  rawLower w .D F.E₂ ++ rawLower w .H F.E₁' ++
    F.piv.flatMap (fun p => [.stream w (.hdShift p.1 p.2 false), .call w p.1 p.2,
      .stream w (.unit .D p.2 (-1)), .stream w (.hdShift p.1 p.2 false)]) ++
    rawLower w .H F.E₁ ++ rawLower w .D F.E₂'

/-- Raw program of the edge of `w` entering `v` (mirror of `edgeOpsB`). -/
noncomputable def rawEdge (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (w : Role .bit 100)
    (v : Vertex .bit 100) : List (RawOp Wb mH) :=
  match edgeInto w v with
  | some e => rawShear (roleIdxB w) (fac (edgeMatFin e))
  | none => []

/-- Raw entries of one event of the serialized node (mirror of `evOps`). -/
noncomputable def rawEv (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) :
    NodeEvent .bit 100 → List (RawOp Wb mH)
  | .edge w v => rawEdge fac w v
  | .row j ι r => [.gate (gateXors j ι r)]

/-- **The raw schedule of the bit-network node**: the pure-network event list `nodeEvents .bit 100` with every
event replaced by its raw entries (`bitNodeOps` minus its final relabelling is the same event list
with `evOps`, `InterchangeCorrect.bitNodeOps_eq`, `InterchangeCorrect.nodeMainOps_eq_flatMap`). -/
noncomputable def rawMain (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) : List (RawOp Wb mH) :=
  (nodeEvents .bit 100).flatMap (rawEv fac)

/-- The macro `D ← D − H` (`subHSteps`). -/
def preOps : List (StreamOp mH) := (List.finRange mH).map fun i => .hdShift i i true

/-- The macro `D ← H − D` (`hMinusDSteps`). -/
def postOps : List (StreamOp mH) :=
  (List.finRange mH).flatMap fun i => [.unit .D i (-1), .hdShift i i false]

section Shape

variable {L : Layout} {β : Type} {Child : Type} (Rl : RoleOp L β Wb Child → RawOp Wb mH → Prop)

theorem forall₂_lower (R t₀ b : ℕ) (w : Fin Wb) (X : Chunk) (E : Matrix (Fin mH) (Fin mH) ℚ)
    (hU : ∀ i : Fin mH, Rl (.prim w (.elem (.unit (blk t₀ b i).1 (blk t₀ b i).2
      (ratModNat R (E i i)) (ratModNat R (E i i)⁻¹)))) (.stream w (.unit X i (E i i))))
    (hS : ∀ i : Fin mH, Rl (.prim w (.elem (.shift (blk t₀ b i).1 (blk t₀ b i).2 (fun x =>
      ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
        ratModNat R (E i j) * L.blockVal (blk t₀ b j).1 (blk t₀ b j).2 x))))
      (.stream w (.lowShift X i (fun j => E i j)))) :
    List.Forall₂ Rl ((lowerSteps (L := L) (β := β) R t₀ b E).map (.prim w)) (rawLower w X E) := by
  unfold lowerSteps rawLower
  rw [List.map_flatMap]
  refine forall₂_flatMap _ _ _ fun i _ => ?_
  simp only [List.map_cons, List.map_nil]
  exact List.Forall₂.cons (hU i) (List.Forall₂.cons (hS i) List.Forall₂.nil)

theorem forall₂_shear (R h₀ d₀ b : ℕ) (w : Fin Wb) (F : FacData)
    (childOf : Fin mH → Fin mH → Child)
    (hLD : ∀ E, List.Forall₂ Rl ((lowerSteps (L := L) (β := β) R d₀ b E).map (.prim w))
      (rawLower w .D E))
    (hLH : ∀ E, List.Forall₂ Rl ((lowerSteps (L := L) (β := β) R h₀ b E).map (.prim w))
      (rawLower w .H E))
    (hP1 : ∀ p : Fin mH × Fin mH, Rl (.prim w (.elem (.shift (blk d₀ b p.2).1 (blk d₀ b p.2).2
      (fun x => L.blockVal (blk h₀ b p.1).1 (blk h₀ b p.1).2 x))))
      (.stream w (.hdShift p.1 p.2 false)))
    (hP2 : ∀ p : Fin mH × Fin mH, Rl (.call w (childOf p.1 p.2)) (.call w p.1 p.2))
    (hP3 : ∀ p : Fin mH × Fin mH, Rl (.prim w (.elem (.unit (blk d₀ b p.2).1 (blk d₀ b p.2).2
      (R - 1) (R - 1)))) (.stream w (.unit .D p.2 (-1)))) :
    List.Forall₂ Rl (shearOps R h₀ d₀ b w F childOf) (rawShear w F) := by
  unfold shearOps rawShear
  refine forall₂_append (forall₂_append (forall₂_append (forall₂_append (hLD _) (hLH _)) ?_)
    (hLH _)) (hLD _)
  refine forall₂_flatMap _ _ _ fun p _ => ?_
  exact .cons (hP1 p) (.cons (hP2 p) (.cons (hP3 p) (.cons (hP1 p) .nil)))

theorem forall₂_edge (R h₀ d₀ b : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (childOf : Fin mH → Fin mH → Child) (w : Role .bit 100) (v : Vertex .bit 100)
    (hsh : ∀ F, List.Forall₂ Rl (shearOps R h₀ d₀ b (roleIdxB w) F childOf)
      (rawShear (roleIdxB w) F)) :
    List.Forall₂ Rl (edgeOpsB R h₀ d₀ b fac childOf w v) (rawEdge fac w v) := by
  unfold edgeOpsB rawEdge
  cases edgeInto w v with
  | none => exact List.Forall₂.nil
  | some e => exact hsh _

end Shape

/-- **Entrywise correspondence** of the pure-network node operations (the event list with `evOps`) and the raw
schedule, for any relation holding on the leaf pairs. -/
theorem forall₂_main {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    (Rl : RoleOp L β Wb Child → RawOp Wb mH → Prop) (R h₀ d₀ b : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (childOf : Fin mH → Fin mH → Child)
    (hsh : ∀ (w : Role .bit 100) (F : FacData), List.Forall₂ Rl
      (shearOps R h₀ d₀ b (roleIdxB w) F childOf) (rawShear (roleIdxB w) F))
    (hG : ∀ j ι r, Rl (gateOpB j ι r) (.gate (gateXors j ι r))) :
    List.Forall₂ Rl ((nodeEvents .bit 100).flatMap
      (InterchangeCorrect.evOps (L := L) (β := β) R h₀ d₀ b fac childOf)) (rawMain fac) := by
  unfold rawMain
  refine forall₂_flatMap _ _ _ fun ev _ => ?_
  cases ev with
  | edge w v => exact forall₂_edge Rl R h₀ d₀ b fac childOf w v (hsh w)
  | row j ι r => exact List.Forall₂.cons (hG j ι r) List.Forall₂.nil

end SubNLogN.Machine.C5.NetAux
