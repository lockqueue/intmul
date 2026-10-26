/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.Calculus.FramePassSafe
import SubNLogN.Machine.Calculus.SafeFootprint
import SubNLogN.Machine.Calculus.Hdr
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# C-core leaves 8/10, shared machine base (`CCore/LeafPhaseBase.lean`)

**Scope (honest summary).** Shared definitions and lemmas for the phase kernel (`PhaseStmt`,
`CCore/SkelDefs.lean:257`) and the scalar-row kernel (`ScalarRowStmt`, `SkelDefs.lean:288`):
the private scratch names `PS`, the scratch-state helper `stv`, the register file `σ`, and the
safety bridges. Nothing about `PhaseStmt`/`ScalarRowStmt` is proved here.

## Design (plan; costs are `C·t.volG`)
* **Framing.** `ccoreFramed` frames only `park` and the role stacks (`Contracts/CCore.lean:209`).
  Private scratch, `io` and `desc` are unframed. Hence a closed `Runs` program that reads
  (peeks/pops) only scratch and `desc` is safe for free (`SafeRunsIn.of_runs_readsIn`). The only
  reads of a role stack are the certified passes of `Calculus/FramePassSafe.lean`, which stop at
  the role's owned `mark`.
* **Layout.** `BL Er = KLoc (CCoreN Wn) (PS ⊕ Er)`: the C-core named stacks, my scratch `PS`, and
  the private scratch `Er` of an embedded sub-kernel (`RotIPowStmt`). States are written
  `stv S sc`: the scratch part is the function `sc : PS → List Sym`, everything else is `S`.
* **Registers.** `σ Rr = NatArith.Reg × Rr`: the register file of the `NatArith` library (its first
  component is the `Option Sym` register of the `SProg` library programs) and the registers of the
  embedded sub-kernel.
* **Header.** `Calculus.copyHdr 12 desc H Ht` copies the descriptor `t.hdr` to scratch `H`; the
  fields are then moved one by one to counter stacks (`natSyms f ++ [mark]`) or dropped
  (count-controlled over the 12 fields; never a header-wide mark scan).
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

/-! ## Private scratch names -/

/-- The private scratch stacks of the phase and scalar-row kernels. -/
inductive PS where
  | H | Ht | cP | cDl | cK | cDD | cS | cJ | cKk | cRho | cA | cB | c3 | cW | t1 | t2 | t3
  | X | X2 | Xn | Y | Tm | Out | G | G2 | Gu | Sch | Tpl | Tpl2 | Us | Us2 | F | F2
  | ct | cU | cV
  deriving DecidableEq

instance : Fintype PS :=
  Fintype.ofList [PS.H, PS.Ht, PS.cP, PS.cDl, PS.cK, PS.cDD, PS.cS, PS.cJ, PS.cKk, PS.cRho, PS.cA, PS.cB, PS.c3, PS.cW, PS.t1, PS.t2, PS.t3, PS.X, PS.X2, PS.Xn, PS.Y, PS.Tm, PS.Out, PS.G, PS.G2, PS.Gu, PS.Sch, PS.Tpl, PS.Tpl2, PS.Us, PS.Us2, PS.F, PS.F2, PS.ct, PS.cU, PS.cV]
    (by intro x; cases x <;> decide)

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus


/-- The big layout: C-core named stacks, my scratch `PS`, a sub-kernel's private scratch `Er`. -/
abbrev BL (Er : Type) : Type := KLoc (CCoreN Wn) (PS ⊕ Er)

/-- Scratch stack `p`. -/
abbrev scr {Er : Type} (p : PS) : BL Er := .inr (.inl p)

/-- The state with scratch part `sc` and every other stack from `S`. -/
def stv {Er : Type} (S : BL Er → List Sym) (sc : PS → List Sym) : BL Er → List Sym
  | .inr (.inl p) => sc p
  | k => S k

section Stv

variable {Er : Type} [DecidableEq Er] (S : BL Er → List Sym) (sc : PS → List Sym)

@[simp] theorem stv_scr (p : PS) : stv S sc (scr p) = sc p := rfl

@[simp] theorem stv_inl (n : CCoreN Wn) : stv S sc (.inl n) = S (.inl n) := rfl

@[simp] theorem stv_inrr (e : Er) : stv S sc (.inr (.inr e)) = S (.inr (.inr e)) := rfl

theorem update_stv_scr (p : PS) (l : List Sym) :
    Function.update (stv S sc) (scr p) l = stv S (Function.update sc p l) := by
  funext k
  rcases k with n | q | e
  · simp [stv, Function.update_apply]
  · by_cases h : q = p
    · subst h; simp [stv]
    · simp [stv, Function.update_apply, h]
  · simp [stv, Function.update_apply]

theorem update_stv_inl (n : CCoreN Wn) (l : List Sym) :
    Function.update (stv S sc) (.inl n) l = stv (Function.update S (.inl n) l) sc := by
  funext k
  rcases k with m | q | e
  · by_cases h : m = n
    · subst h; simp [stv]
    · simp [stv, Function.update_apply, h]
  · simp [stv, Function.update_apply]
  · simp [stv, Function.update_apply]

theorem stv_of_clean (h : KClean S) : S = stv S (fun _ => []) := by
  funext k
  rcases k with n | q | e
  · rfl
  · exact h (.inl q)
  · rfl

theorem stv_stv (sc' : PS → List Sym) : stv (stv S sc) sc' = stv S sc' := by
  funext k
  rcases k with n | q | e <;> rfl

end Stv

/-! ## Registers -/

/-- The register file: the `NatArith` registers (the `Option Sym` register of the `SProg` library
first) and the registers `Rr` of an embedded sub-kernel. -/
abbrev σ (Rr : Type) : Type := NatArith.Reg × Rr

/-- Lens to the `NatArith` registers. -/
def lN (Rr : Type) : Lens (σ Rr) NatArith.Reg := Lens.fst _ _

/-- Lens to the `Option Sym` register. -/
def lO (Rr : Type) : Lens (σ Rr) (Option Sym) := (lN Rr).comp NatArith.lW

/-- Lens to the sub-kernel registers. -/
def lR (Rr : Type) : Lens (σ Rr) Rr := Lens.snd _ _

/-! ## Safety bridges -/

section Bridges

variable {Er Rr : Type} [DecidableEq Er]

/-- The read footprint "unframed stacks" of a C-core kernel. -/
abbrev Unfr {Er : Type} : BL Er → Prop := fun k => ¬ ccoreFramed k

theorem unfr_scr (p : PS) : Unfr (scr (Er := Er) p) := fun h => h

theorem unfr_desc : Unfr (descL (E := PS ⊕ Er)) := fun h => h

theorem unfr_inrr (e : Er) : Unfr (.inr (.inr e) : BL Er) := fun h => h

/-- A closed `SProg` with a `Runs` fact that reads only unframed stacks, lifted to `σ`. -/
theorem safe_liftO {p : SProg (BL Er)} {S S' : BL Er → List Sym} {T : ℕ}
    (h : Runs p S S' (fun _ => True) T) (hc : p.Closed) (hr : ReadsIn Unfr p) :
    SafeRunsIn ccoreFramed [] (p.liftRegs (lO Rr)) S S' (fun _ => True) T :=
  SafeRunsIn.of_runs_readsIn (WP.W0m.runs_liftRegs (lO Rr) h) (WP.W9comp.closed_liftRegs _ hc)
    (readsIn_liftRegs _ _ p hr) []

/-- A closed `NatArith` program with a `Runs` fact that reads only unframed stacks, lifted. -/
theorem safe_liftN {p : Prog (BL Er) (fun _ => Sym) NatArith.Reg} {S S' : BL Er → List Sym}
    {T : ℕ} (h : Runs p S S' (fun _ => True) T) (hc : p.Closed) (hr : ReadsIn Unfr p) :
    SafeRunsIn ccoreFramed [] (p.liftRegs (lN Rr)) S S' (fun _ => True) T :=
  SafeRunsIn.of_runs_readsIn (WP.W0m.runs_liftRegs (lN Rr) h) (WP.W9comp.closed_liftRegs _ hc)
    (readsIn_liftRegs _ _ p hr) []

/-- A closed `SProg` with an all-framed safe run (e.g. a certified pass), lifted to `σ`. -/
theorem safe_liftO_safe {p : SProg (BL Er)} {S S' : BL Er → List Sym} {Q : Option Sym → Prop}
    {T : ℕ} (h : SafeRunsIn (fun _ => True) [] p S S' Q T) (hc : p.Closed) :
    SafeRunsIn ccoreFramed [] (p.liftRegs (lO Rr)) S S' (fun _ => True) T :=
  SafeRunsIn.mono (SafeRunsIn.mono_framed (SafeRunsIn.liftRegs (lO Rr) hc h []) (fun _ _ => trivial))
    (fun _ _ => trivial) le_rfl

end Bridges

/-! ## The work layout of the scratch-only programs -/

/-- Identity lens. -/
def lid (α : Type) : Lens α α where
  get v := v
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The work layout of the scratch-only programs: `desc`, my scratch `PS`, the sub-kernel
scratch `Er`. It embeds into `BL Er` by `ιw` (into unframed stacks only). -/
abbrev Lw (Er : Type) : Type := Option PS ⊕ Er

/-- Scratch stack `p` of the work layout. -/
abbrev wS {Er : Type} (p : PS) : Lw Er := .inl (some p)

/-- The descriptor stack of the work layout. -/
abbrev wD {Er : Type} : Lw Er := .inl none

/-- The embedding of the work layout. -/
def ιw {Er : Type} : Lw Er → BL Er
  | .inl none => descL
  | .inl (some p) => scr p
  | .inr e => .inr (.inr e)

theorem ιw_injective {Er : Type} : Function.Injective (ιw (Er := Er)) := by
  rintro ((_ | p) | e) ((_ | q) | f) h <;> simp_all [ιw]

theorem ιw_unframed {Er : Type} (x : Lw Er) : ¬ ccoreFramed (ιw x) := by
  rcases x with (_ | p) | e <;> simp [ιw, ccoreFramed]

/-- A state of the work layout: `desc` content `d`, scratch `sc`, sub-kernel scratch `er`. -/
def wst {Er : Type} (d : List Sym) (sc : PS → List Sym) (er : Er → List Sym) : Lw Er → List Sym
  | .inl none => d
  | .inl (some p) => sc p
  | .inr e => er e

section Wst

variable {Er : Type} [DecidableEq Er] (d : List Sym) (sc : PS → List Sym) (er : Er → List Sym)

@[simp] theorem wst_S (p : PS) : wst d sc er (wS p) = sc p := rfl

@[simp] theorem wst_D : wst d sc er wD = d := rfl

@[simp] theorem wst_inr (e : Er) : wst d sc er (.inr e) = er e := rfl

theorem update_wst_S (p : PS) (l : List Sym) :
    Function.update (wst d sc er) (wS p) l = wst d (Function.update sc p l) er := by
  funext k
  rcases k with (_ | q) | e
  · simp [wst, Function.update_apply]
  · by_cases h : q = p
    · subst h; simp [wst]
    · simp [wst, Function.update_apply, h]
  · simp [wst, Function.update_apply]

theorem update_wst_D (l : List Sym) :
    Function.update (wst d sc er) wD l = wst l sc er := by
  funext k
  rcases k with (_ | q) | e
  · simp [wst]
  · simp [wst, Function.update_apply]
  · simp [wst, Function.update_apply]

theorem stv_comp_ιw (S0 : BL Er → List Sym) :
    stv S0 sc ∘ ιw = wst (S0 descL) sc (fun e => S0 (.inr (.inr e))) := by
  funext k
  rcases k with (_ | q) | e <;> rfl

end Wst

/-- **A scratch-only program, called in the big layout.** A closed program on the work layout
with an exact `Runs` fact from `wst d sc er` to `wst d sc' er` (descriptor and sub-kernel scratch
restored) is a safe run of its `callInj` embedding from `stv S0 sc` to `stv S0 sc'`. -/
theorem safe_callW {Er Rr : Type} [DecidableEq Er] {P : Prog (Lw Er) (fun _ => Sym) (σ Rr)}
    (hc : P.Closed) (S0 : BL Er → List Sym) (sc sc' : PS → List Sym) {Q : σ Rr → Prop} {T : ℕ}
    (h : Runs P (wst (S0 descL) sc (fun e => S0 (.inr (.inr e))))
      (wst (S0 descL) sc' (fun e => S0 (.inr (.inr e)))) Q T) :
    SafeRunsIn ccoreFramed [] (callInj ιw (lid (σ Rr)) P) (stv S0 sc) (stv S0 sc')
      (fun _ => True) T := by
  refine SafeRunsIn.callInj (framedL := fun _ => False) (Q := Q) ιw_injective
    (fun x hx => ιw_unframed x hx) (lid (σ Rr)) hc ?_ ?_ []
  · rw [stv_comp_ιw, stv_comp_ιw]
    exact SafeRunsIn.of_runsIn_unframed (RunsIn.iff_runs.mpr h)
  · intro k hk
    rcases k with n | q | e
    · rfl
    · exact absurd rfl (hk (.inl (some q)))
    · exact absurd rfl (hk (.inr e))

end SubNLogN.Machine.CCore.LeafScalarAux
