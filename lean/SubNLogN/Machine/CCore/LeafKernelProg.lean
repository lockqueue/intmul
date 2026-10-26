/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafKernelMath
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.AppC.C5StreamArith
import SubNLogN.Machine.Calculus.Hdr
import SubNLogN.Machine.Calculus.SafeFootprint
import WP.Inst.W3Ok

/-!
# C-core leaf kernel: the program (`CCore/LeafKernelProg.lean`)

The leaf program runs on its own layout `LI = Fin 2 ⊕ (Fin NS ⊕ E')` (`0 = io`, `1 = desc`, `NS`
named private stacks, the private scratch `E'` of the embedded kernels); `leafProg` embeds it into
`KLoc (CCoreN Wn) E` by `callInj` (image: `io`, `desc`, private scratch; none of them framed).

Phases (named stacks below):
* `phaseH`: copy the 12-field header from `desc` to `H` (`copyHdr`) and extract `P, Δ, K, D, S, j0,
  k, ρ` (`NatArith.copyN` + `dropField`).
* `phaseA`: `w_g = P + Δ + (Δ + 3)`, `e = 1·m^k` (`NatArith.powMulN`), `X0 = ρ + K·(D − j0 − 1)`
  (`subN`, W3 `decNat`, `mulN`, `addN`), `W = S·2^X0` (W3 `shlVar`); drop the auxiliaries.
* `phaseL`: `e` iterations of `{DrvC(io, W, w_g); W := W / 2^K (W3 shrVar); ctr -= 1 (decNat);
  peek ctr}`; the loop test is "the counter has a bit on top".
* `phaseC`: drop `W, w_g, K`.
-/

namespace SubNLogN.Machine.CCore.LeafKernelAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus
open SubNLogN.Machine.Layer

/-! ## Layout -/

/-- Number of named private stacks. -/
abbrev NS : ℕ := 26

/-- The inner layout: `io`, `desc`, the named stacks, the kernels' scratch. -/
abbrev LI (Ec : Type) (m1 m2 m3 : ℕ) : Type := Fin 2 ⊕ (Fin NS ⊕ (Ec ⊕ (Fin m1 ⊕ (Fin m2 ⊕ Fin m3))))

/-- The private scratch of the leaf kernel. -/
abbrev EL (Ec : Type) (m1 m2 m3 : ℕ) : Type := Fin NS ⊕ (Ec ⊕ (Fin m1 ⊕ (Fin m2 ⊕ Fin m3)))

@[simp] abbrev iH : Fin NS := 0
@[simp] abbrev iT0 : Fin NS := 1
@[simp] abbrev iP : Fin NS := 2
@[simp] abbrev iDl : Fin NS := 3
@[simp] abbrev iK : Fin NS := 4
@[simp] abbrev iD : Fin NS := 5
@[simp] abbrev iS : Fin NS := 6
@[simp] abbrev ij : Fin NS := 7
@[simp] abbrev ik : Fin NS := 8
@[simp] abbrev iRo : Fin NS := 9
@[simp] abbrev iWg : Fin NS := 10
@[simp] abbrev iCt : Fin NS := 11
@[simp] abbrev iW : Fin NS := 12
@[simp] abbrev iY1 : Fin NS := 13
@[simp] abbrev iY2 : Fin NS := 14
@[simp] abbrev iY3 : Fin NS := 15
@[simp] abbrev iY4 : Fin NS := 16
@[simp] abbrev iX0 : Fin NS := 17
@[simp] abbrev iC3 : Fin NS := 18
@[simp] abbrev iT1 : Fin NS := 19
@[simp] abbrev iT2 : Fin NS := 20
@[simp] abbrev iT3 : Fin NS := 21
@[simp] abbrev iT4 : Fin NS := 22
@[simp] abbrev iT5 : Fin NS := 23
@[simp] abbrev iT6 : Fin NS := 24
@[simp] abbrev iT7 : Fin NS := 25

section Layout

variable {Ec : Type} {m1 m2 m3 : ℕ}

/-- Named private stack `i`. -/
abbrev sc (i : Fin NS) : LI Ec m1 m2 m3 := .inr (.inl i)
/-- The array stack. -/
abbrev ioI : LI Ec m1 m2 m3 := .inl 0
/-- The descriptor stack. -/
abbrev dsI : LI Ec m1 m2 m3 := .inl 1

variable (Ec m1 m2 m3)

/-- DrvC: array `0 ↦ io`, `W ↦ sc iW`, `w ↦ sc iWg`. -/
def ιC : KLoc (Fin 3) Ec → LI Ec m1 m2 m3 :=
  Sum.elim ![ioI, sc iW, sc iWg] fun e => .inr (.inr (.inl e))

/-- W3 `shlVar`: number `sc iW`, counter `sc iX0`. -/
def ι1 : Loc 2 m1 → LI Ec m1 m2 m3 :=
  Sum.elim ![sc iW, sc iX0] fun j => .inr (.inr (.inr (.inl j)))

/-- W3 `shrVar`: number `sc iW`, counter `sc iK`. -/
def ι2 : Loc 2 m2 → LI Ec m1 m2 m3 :=
  Sum.elim ![sc iW, sc iK] fun j => .inr (.inr (.inr (.inr (.inl j))))

/-- W3 `decNat` on the named stack `N`. -/
def ι3 (N : Fin NS) : Loc 1 m3 → LI Ec m1 m2 m3 :=
  Sum.elim ![sc N] fun j => .inr (.inr (.inr (.inr (.inr j))))

/-- The embedding of the inner layout into `KLoc (CCoreN Wn) (EL …)`. -/
def ιO : LI Ec m1 m2 m3 → CL (EL Ec m1 m2 m3) :=
  Sum.elim ![ioL, descL] fun e => .inr e

theorem ιC_inj : Function.Injective (ιC Ec m1 m2 m3) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro a b h
    simpa using h
  · intro i e
    fin_cases i <;> simp

theorem ι1_inj : Function.Injective (ι1 Ec m1 m2 m3) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro a b h
    simpa using h
  · intro i e
    fin_cases i <;> simp

theorem ι2_inj : Function.Injective (ι2 Ec m1 m2 m3) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro a b h
    simpa using h
  · intro i e
    fin_cases i <;> simp

theorem ι3_inj (N : Fin NS) : Function.Injective (ι3 Ec m1 m2 m3 N) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j _
    exact Subsingleton.elim i j
  · intro a b h
    simpa using h
  · intro i e
    fin_cases i
    simp

theorem ιO_inj : Function.Injective (ιO Ec m1 m2 m3) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ioL, descL]
  · intro a b h
    simpa using h
  · intro i e
    fin_cases i <;> simp [ioL, descL]

/-- Nothing in the image of `ιO` is framed. -/
theorem ιO_unframed (x : LI Ec m1 m2 m3) : ¬ ccoreFramed (ιO Ec m1 m2 m3 x) := by
  rcases x with i | e
  · fin_cases i <;> simp [ιO, ioL, descL, ccoreFramed]
  · simp [ιO, ccoreFramed]

end Layout

/-! ## Registers and lenses -/

/-- Registers: work register, `NatArith` registers, DrvC, `shlVar`, `shrVar`, `decNat`. -/
abbrev σL (Rc R1 R2 R3 : Type) : Type := Option Sym × (NatArith.Reg × (Rc × (R1 × (R2 × R3))))

section Lenses

variable {Rc R1 R2 R3 : Type}

def lW : Lens (σL Rc R1 R2 R3) (Option Sym) := Lens.fst _ _
def lR : Lens (σL Rc R1 R2 R3) NatArith.Reg := (Lens.snd _ _).comp (Lens.fst _ _)
def lC : Lens (σL Rc R1 R2 R3) Rc := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def l1 : Lens (σL Rc R1 R2 R3) R1 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def l2 : Lens (σL Rc R1 R2 R3) R2 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def l3 : Lens (σL Rc R1 R2 R3) R3 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.snd _ _))))

end Lenses

/-- The identity lens. -/
def lensId (σ : Type) : Lens σ σ where
  get := id
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-! ## The program -/

/-- Programs on the inner layout. -/
abbrev PL (Ec : Type) (m1 m2 m3 : ℕ) (Rc R1 R2 R3 : Type) : Type :=
  Prog (LI Ec m1 m2 m3) (fun _ => Sym) (σL Rc R1 R2 R3)

section Prog

variable {Ec : Type} {m1 m2 m3 : ℕ} {Rc R1 R2 R3 : Type}

/-- Copy the top header field of `H` to `X`, then drop it from `H`. -/
def takeF (X : Fin NS) : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq ((NatArith.copyN (sc iH) (sc X) (sc iT0)).liftRegs lR) ((dropField (sc iH)).liftRegs lW)

/-- Drop the top header field of `H`. -/
def skipF : PL Ec m1 m2 m3 Rc R1 R2 R3 := (dropField (sc iH)).liftRegs lW

/-- Phase H: header copy and field extraction (`P, Δ, K, D, S, j0, k, ρ`). -/
def phaseH : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq ((copyHdr 12 dsI (sc iH) (sc iT0)).liftRegs lW)
    (.seq (takeF iP) (.seq skipF (.seq skipF (.seq (takeF iDl) (.seq skipF (.seq skipF
      (.seq (takeF iK) (.seq (takeF iD) (.seq (takeF iS) (.seq (takeF ij) (.seq (takeF ik)
        (takeF iRo))))))))))))

def addP (x y z : Fin NS) : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  (NatArith.addN (sc x) (sc y) (sc z) (sc iT1) (sc iT2) (sc iT3)).liftRegs lR

def subP (x y z : Fin NS) : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  (NatArith.subN (sc x) (sc y) (sc z) (sc iT1) (sc iT2) (sc iT3)).liftRegs lR

def dropP (x : Fin NS) : PL Ec m1 m2 m3 Rc R1 R2 R3 := (NatArith.dropN (sc x)).liftRegs lR

def pushP (x : Fin NS) (c : ℕ) : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  (NatArith.pushNat (sc x) c).liftRegs lR

def powP : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  (NatArith.powMulN (sc iCt) mn (sc ik) (sc iT1) (sc iT2) (sc iT3) (sc iT4) (sc iT5) (sc iT6)
    (sc iT7)).liftRegs lR

def mulP : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  (NatArith.mulN (sc iK) (sc iY3) (sc iY4) (sc iT1) (sc iT2) (sc iT3) (sc iT4)).liftRegs lR

def copySP : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  (NatArith.copyN (sc iS) (sc iW) (sc iT0)).liftRegs lR

/-- Drops at the end of phase A. -/
def dropsA : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq (dropP iP) (.seq (dropP iDl) (.seq (dropP iD) (.seq (dropP iS) (.seq (dropP ij)
    (.seq (dropP ik) (.seq (dropP iRo) (.seq (dropP iC3) (.seq (dropP iY1) (.seq (dropP iY2)
      (.seq (dropP iY3) (.seq (dropP iY4) (dropP iX0))))))))))))

/-- `w_g = (P + Δ) + (Δ + 3)` on `Wg` (auxiliaries `C3 = 3`, `Y1 = P + Δ`, `Y2 = Δ + 3`). -/
def stepA1 : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq (pushP iC3 3) (.seq (addP iP iDl iY1) (.seq (addP iDl iC3 iY2) (addP iY1 iY2 iWg)))

/-- `e = 1·m^k` on `Ct`. -/
def stepA2 : PL Ec m1 m2 m3 Rc R1 R2 R3 := .seq (pushP iCt 1) powP

/-- `X0 = ρ + K·(D − j0 − 1)` (auxiliaries `Y3 = D − j0 − 1`, `Y4 = K·Y3`). -/
def stepA3 (P3 : Prog (Loc 1 m3) (fun _ => Sym) R3) : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq (subP iD ij iY3) (.seq (callInj (ι3 Ec m1 m2 m3 iY3) l3 P3) (.seq mulP (addP iRo iY4 iX0)))

/-- `W = S·2^X0`. -/
def stepA4 (P1 : Prog (Loc 2 m1) (fun _ => Sym) R1) : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq copySP (callInj (ι1 Ec m1 m2 m3) l1 P1)

/-- Phase A: `w_g`, `e`, `X0`, `W`, then drop the auxiliaries. -/
def phaseA (P1 : Prog (Loc 2 m1) (fun _ => Sym) R1) (P3 : Prog (Loc 1 m3) (fun _ => Sym) R3) :
    PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq stepA1 (.seq stepA2 (.seq (stepA3 P3) (.seq (stepA4 P1) dropsA)))

/-- Loop test: the counter has a bit on top. -/
def loopTest (v : σL Rc R1 R2 R3) : Bool := optIsBit (lW.get v)

/-- One loop iteration. -/
def bodyL (Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc) (P2 : Prog (Loc 2 m2) (fun _ => Sym) R2)
    (P3 : Prog (Loc 1 m3) (fun _ => Sym) R3) : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq (callInj (ιC Ec m1 m2 m3) lC Pc) (.seq (callInj (ι2 Ec m1 m2 m3) l2 P2)
    (.seq (callInj (ι3 Ec m1 m2 m3 iCt) l3 P3) ((peekR (sc iCt)).liftRegs lW)))

/-- Phase L: the runtime loop. -/
def phaseL (Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc) (P2 : Prog (Loc 2 m2) (fun _ => Sym) R2)
    (P3 : Prog (Loc 1 m3) (fun _ => Sym) R3) : PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq ((peekR (sc iCt)).liftRegs lW) (.loop loopTest (bodyL Pc P2 P3))

/-- Phase C: cleanup. -/
def phaseC : PL Ec m1 m2 m3 Rc R1 R2 R3 := .seq (dropP iW) (.seq (dropP iWg) (dropP iK))

/-- The inner program. -/
def innerP (Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc) (P1 : Prog (Loc 2 m1) (fun _ => Sym) R1)
    (P2 : Prog (Loc 2 m2) (fun _ => Sym) R2) (P3 : Prog (Loc 1 m3) (fun _ => Sym) R3) :
    PL Ec m1 m2 m3 Rc R1 R2 R3 :=
  .seq phaseH (.seq (phaseA P1 P3) (.seq (phaseL Pc P2 P3) phaseC))

/-- **The leaf program** on `KLoc (CCoreN Wn) (EL …)`. -/
def leafProg (Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc) (P1 : Prog (Loc 2 m1) (fun _ => Sym) R1)
    (P2 : Prog (Loc 2 m2) (fun _ => Sym) R2) (P3 : Prog (Loc 1 m3) (fun _ => Sym) R3) :
    Prog (CL (EL Ec m1 m2 m3)) (fun _ => Sym) (σL Rc R1 R2 R3) :=
  callInj (ιO Ec m1 m2 m3) (lensId _) (innerP Pc P1 P2 P3)

end Prog

/-! ## Closedness and read footprint -/

section Closed

variable {Ec : Type} {m1 m2 m3 : ℕ} {Rc R1 R2 R3 : Type}

theorem closed_takeF (X : Fin NS) : (takeF X : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ (NatArith.closed_copyN _ _ _))
    (WP.W9comp.closed_liftRegs _ (closed_dropField _))

theorem closed_skipF : (skipF : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  WP.W9comp.closed_liftRegs _ (closed_dropField _)

theorem closed_phaseH : (phaseH : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed := by
  unfold phaseH
  exact WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ (closed_copyHdr _ _ _ _))
    ⟨closed_takeF _, closed_skipF, closed_skipF, closed_takeF _, closed_skipF, closed_skipF,
      closed_takeF _, closed_takeF _, closed_takeF _, closed_takeF _, closed_takeF _,
      closed_takeF _⟩

theorem closed_addP (x y z : Fin NS) : (addP x y z : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  WP.W9comp.closed_liftRegs _ (NatArith.closed_addN _ _ _ _ _ _)

theorem closed_subP (x y z : Fin NS) : (subP x y z : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  WP.W9comp.closed_liftRegs _ (NatArith.closed_subN _ _ _ _ _ _)

theorem closed_dropP (x : Fin NS) : (dropP x : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  WP.W9comp.closed_liftRegs _ (NatArith.closed_dropN _)

theorem closed_pushP (x : Fin NS) (c : ℕ) : (pushP x c : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  WP.W9comp.closed_liftRegs _ (NatArith.closed_pushNat _ _)

theorem closed_dropsA : (dropsA : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  ⟨closed_dropP _, closed_dropP _, closed_dropP _, closed_dropP _, closed_dropP _, closed_dropP _,
    closed_dropP _, closed_dropP _, closed_dropP _, closed_dropP _, closed_dropP _, closed_dropP _,
    closed_dropP _⟩

theorem closed_phaseA {P1 : Prog (Loc 2 m1) (fun _ => Sym) R1} {P3 : Prog (Loc 1 m3) (fun _ => Sym) R3}
    (h1 : P1.Closed) (h3 : P3.Closed) : (phaseA P1 P3 : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  ⟨⟨closed_pushP _ _, closed_addP _ _ _, closed_addP _ _ _, closed_addP _ _ _⟩,
    ⟨closed_pushP _ _, WP.W9comp.closed_liftRegs _ (NatArith.closed_powMulN _ _ _ _ _ _ _ _ _ _)⟩,
    ⟨closed_subP _ _ _, closed_callInj _ _ h3,
      WP.W9comp.closed_liftRegs _ (NatArith.closed_mulN _ _ _ _ _ _ _), closed_addP _ _ _⟩,
    ⟨WP.W9comp.closed_liftRegs _ (NatArith.closed_copyN _ _ _), closed_callInj _ _ h1⟩,
    closed_dropsA⟩

theorem closed_peekW (k : LI Ec m1 m2 m3) :
    (((peekR k).liftRegs lW : PL Ec m1 m2 m3 Rc R1 R2 R3)).Closed :=
  WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, peekR])

theorem closed_phaseL {Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc}
    {P2 : Prog (Loc 2 m2) (fun _ => Sym) R2} {P3 : Prog (Loc 1 m3) (fun _ => Sym) R3}
    (hc : Pc.Closed) (h2 : P2.Closed) (h3 : P3.Closed) :
    (phaseL Pc P2 P3 : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  ⟨closed_peekW _, closed_callInj _ _ hc, closed_callInj _ _ h2, closed_callInj _ _ h3,
    closed_peekW _⟩

theorem closed_phaseC : (phaseC : PL Ec m1 m2 m3 Rc R1 R2 R3).Closed :=
  ⟨closed_dropP _, closed_dropP _, closed_dropP _⟩

theorem closed_leafProg {Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc}
    {P1 : Prog (Loc 2 m1) (fun _ => Sym) R1} {P2 : Prog (Loc 2 m2) (fun _ => Sym) R2}
    {P3 : Prog (Loc 1 m3) (fun _ => Sym) R3} (hc : Pc.Closed) (h1 : P1.Closed) (h2 : P2.Closed)
    (h3 : P3.Closed) : (leafProg Pc P1 P2 P3).Closed :=
  closed_callInj _ _ ⟨closed_phaseH, closed_phaseA h1 h3, closed_phaseL hc h2 h3, closed_phaseC⟩

/-- Every program reads only stacks satisfying `True`. -/
theorem readsIn_true {K : Type} {Γ : K → Type} {σ : Type} :
    ∀ p : Prog K Γ σ, ReadsIn (fun _ => True) p
  | .push _ _ => trivial
  | .peek _ _ => trivial
  | .pop _ _ => trivial
  | .load _ => trivial
  | .seq p q => ⟨readsIn_true p, readsIn_true q⟩
  | .ite _ p q => ⟨readsIn_true p, readsIn_true q⟩
  | .loop _ p => readsIn_true p
  | .fix b => readsIn_true b
  | .recur _ => trivial

/-- **The leaf program reads only unframed stacks** (`io`, `desc`, private scratch). -/
theorem readsIn_leafProg (Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc)
    (P1 : Prog (Loc 2 m1) (fun _ => Sym) R1) (P2 : Prog (Loc 2 m2) (fun _ => Sym) R2)
    (P3 : Prog (Loc 1 m3) (fun _ => Sym) R3) :
    ReadsIn (fun k => ¬ ccoreFramed k) (leafProg Pc P1 P2 P3) :=
  readsIn_liftRegs _ _ _ (readsIn_mapStk _ _ _
    (readsIn_mono (fun x _ => ιO_unframed Ec m1 m2 m3 x) _ (readsIn_true _)))

end Closed

end SubNLogN.Machine.CCore.LeafKernelAux
