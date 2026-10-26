/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelNode

/-!
# C-core reduction: interface definitions (`CCore/PartsDefs.lean`)

Definitions used by the `fix` induction of the C-core (`CCore/Parts.lean`). Nothing is proved
about the C-core here.

* `CoreTopSpecs`: the big-layout specifications of the header test and of the leaf kernel, with
  cost constants (the `HdrTestStmt` and `LeafStmt` leaves of `SkelDefs.lean` transported to the big
  layout; the layout plumbing `SkelLayout.lean` is meant to supply them).
* `SkelImpl p βn βd`: what the layout plumbing provides from the kernel leaves: a big layout, the
  programs `CoreProgs`, closedness, `CoreTopSpecs` and `NodeSpecs`.
* `CCoreMathInputs p βn βd`: the mathematical leaves and the value-level network premises at one valid choice
  of complex edge data.
* `PartsAux.CallData`, `PartsAux.CallData.Good`, `PartsAux.CallData.out`: the ghost data of one
  C-core call, its entry conditions (exactly the hypotheses of `CCoreStmt`) and its exit state.
* `PartsAux.visC`, `PartsAux.tailC`: a state split into its visible part (framed stacks emptied)
  and its frame tails (the content of `park` and the role stacks).
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-- **Big-layout specifications of the header test and the leaf kernel** of `L`, with cost
constants `cH`, `cL` (the leaves `HdrTestStmt` and `LeafStmt` of `SkelDefs.lean` on the big layout
`CL E`, in every environment `ρ`). -/
structure CoreTopSpecs {E σ : Type} [DecidableEq E] (p : LayerParams) (P₀ βn βd : ℕ)
    (L : CoreProgs E σ) (cH cL : ℕ) : Prop where
  hdr : ∀ (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (t : CCoreRT) (tdesc : List Sym)
    (S : CL E → List Sym),
    CCoreBands p P₀ t → KClean S → S descL = t.hdr ++ tdesc →
    Calculus.SafeRunsIn ccoreFramed ρ L.hdr S S
      (fun v => L.obs v = decide (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn)) (cH * t.volG)
  leaf : ∀ (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (hρ : t.ρ < t.K) (hg : t.j0 + t.e ≤ t.D) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r)
    (tio tdesc : List Sym) (S : CL E → List Sym),
    CCoreBands p P₀ t → ArrGrowth t.P t.b z → t.b + 8 * t.e ≤ t.Δ →
    (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn) → BlkTerm tio →
    S ioL = Enc t hA hS z ++ tio → S descL = t.hdr ++ tdesc →
    (∀ k, ccoreFramed k → S k = []) → KClean S →
    Calculus.SafeRunsIn ccoreFramed ρ L.leaf S
      (Function.update S ioL (Enc t hA hS (cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z) ++ tio))
      (fun _ => True) (cL * (t.e * t.volG))

/-- **What the layout plumbing provides** (`SkelLayout.lean`, from the kernel leaves): a finite
private scratch type `E`, a finite nonempty register type `σ`, closed programs `L` for every kernel
instance on the big layout, a cutoff `P₀`, the scalar-row depths `Erow`, and cost constants with
`CoreTopSpecs` and `NodeSpecs`. -/
def SkelImpl (p : LayerParams) (βn βd : ℕ) : Prop :=
  ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (σ : Type) (_ : Finite σ) (_ : Nonempty σ)
    (L : CoreProgs E σ) (P₀ : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ)
    (cH cL cS cC cPh cRA cG cR2I cPush cDrop cI2R : ℕ),
    L.Closed ∧ CoreTopSpecs p P₀ βn βd L cH cL ∧
      NodeSpecs p P₀ L Erow cS cC cPh cRA cG cR2I cPush cDrop cI2R

/-- **The mathematical inputs of the C-core reduction**, at one valid choice `cdat` of complex
edge data: the mathematical leaves `CCoreMathLeaves` (M1-M6 of `SkelMathDefs.lean`) and the
value-level network premises of the node value statement (M1). -/
def CCoreMathInputs (p : LayerParams) (βn βd : ℕ) : Prop :=
  ∃ cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData, ValidCdat cdat ∧
    CCoreMathLeaves p βn βd cdat ∧ ComplexNetCert ∧ RunEightSpecStmt ∧ PackedAgreeStmt ∧
    PackedProcCorrectStmt ∧ TranslationConjStmt

namespace PartsAux

/-- Whether a machine operation is a Lemma A.9 row addition. -/
def isRowAdd : MOp → Bool
  | .rowAdd _ _ _ => true
  | _ => false

/-- **Ghost data of one C-core call**: the context, the proof fields of `CCoreStmt`, the input
array, the tails of `io` and `desc`, and the state. -/
structure CallData (E : Type) where
  /-- the call context -/
  t : CCoreRT
  /-- `0 < A` -/
  hA : 0 < t.A
  /-- `0 < S` -/
  hS : 0 < t.S
  /-- `ρ < K` -/
  hρ : t.ρ < t.K
  /-- the active group fits -/
  hg : t.j0 + t.e ≤ t.D
  /-- the input array -/
  z : RArr (LayerAddr t.A t.K t.D t.S) t.r
  /-- the tail of `io` -/
  tio : List Sym
  /-- the tail of `desc` -/
  tdesc : List Sym
  /-- the entry state -/
  S : CL E → List Sym

variable {E : Type} [DecidableEq E]

/-- The entry conditions of a call: exactly the hypotheses of `CCoreStmt`. -/
def CallData.Good (p : LayerParams) (P₀ βn βd Estar : ℕ) (x : CallData E) : Prop :=
  CCoreBands p P₀ x.t ∧ ArrGrowth x.t.P x.t.b x.z ∧
    x.t.b + cDepth x.t.d βn βd Estar x.t.k ≤ x.t.Δ ∧ BlkTerm x.tio ∧
    x.S ioL = Enc x.t x.hA x.hS x.z ++ x.tio ∧ x.S descL = x.t.hdr ++ x.tdesc ∧
    (∀ k, ccoreFramed k → x.S k = []) ∧ KClean x.S

/-- The exit state of a call: the array replaced by `C^{⊗e} z`. -/
noncomputable def CallData.out (x : CallData E) : CL E → List Sym :=
  Function.update x.S ioL
    (Enc x.t x.hA x.hS (cCoreVal ⟨x.t.ρ, x.hρ⟩ x.t.j0 x.t.e x.hg x.z) ++ x.tio)

/-- The visible part of a state: the framed stacks (`park`, the role stacks) emptied. -/
def visC (B : CL E → List Sym) : CL E → List Sym
  | .inl .park => []
  | .inl (.role _) => []
  | k => B k

/-- The frame tails of a state: the content of `park` and the role stacks. -/
def tailC (B : CL E → List Sym) : CL E → List Sym
  | .inl .park => B (.inl .park)
  | .inl (.role i) => B (.inl (.role i))
  | _ => []

omit [DecidableEq E] in
theorem visC_framed (B : CL E → List Sym) : ∀ k, ccoreFramed k → visC B k = [] := by
  rintro ((_ | _ | _ | i) | e) h <;> simp_all [ccoreFramed, visC]

omit [DecidableEq E] in
theorem tailC_unframed (B : CL E → List Sym) : ∀ k, ¬ ccoreFramed k → tailC B k = [] := by
  rintro ((_ | _ | _ | i) | e) h <;> simp_all [ccoreFramed, tailC]

omit [DecidableEq E] in
theorem appendTail_visC (B : CL E → List Sym) : Calculus.appendTail (visC B) (tailC B) = B := by
  funext k
  rcases k with ((_ | _ | _ | i) | e) <;> simp [Calculus.appendTail, visC, tailC]

theorem appendTail_visC_update (B : CL E → List Sym) (X : List Sym) :
    Calculus.appendTail (Function.update (visC B) ioL X) (tailC B) = Function.update B ioL X := by
  funext k
  rcases k with ((_ | _ | _ | i) | e) <;> simp [Calculus.appendTail, visC, tailC, ioL]

end PartsAux

end SubNLogN.Machine.CCore
