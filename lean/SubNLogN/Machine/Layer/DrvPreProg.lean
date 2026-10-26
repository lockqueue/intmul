/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPost
import SubNLogN.Machine.Layer.DrvPreMathDefs
import SubNLogN.Machine.Layer.DrvPreCostDefs
import SubNLogN.Machine.Arith.Shl
import SubNLogN.Machine.FFT.DIFBase

/-!
# Layer driver pre-phase, part 1: layout, program, states (`Machine/Layer/DrvPreProg.lean`)

**Scope (honest summary).** Proves `drvPre_of_parts`: from the parameter kernel
(`DrvPreParamsStmt`), the individual-kernel pass (`DrvCKernelStmt`), the padding (`DrvPadStmt`), the
descriptors (`DrvDescStmt`), the phase scan (`DrvPhaseScanStmt`), the value bridges
(`DrvPh1BridgeStmt`, `DrvPadBridgeStmt`) and the step count (`DrvPreCostStmt`), with `p.OK`,
`DrvPreStmt p` holds (the exact left shift is `Arith.shl_holds`). The program, on the array, header
and descriptor stacks plus sixteen own stacks and the kernels' private stacks:
1. `mark` floors; the parameter kernel pushes `w, w_g, Δ`, the scan header, `min(q₀, D)`, `W₀`, `K`,
   the rows flag, `drvKeep`, `drvNpad`, `r` on the own stacks `0, …, 10`;
2. exact left shift by `Δ` (array → own stack `11`), then on stack `11`: the phase scan `𝒮_D`, the
   first kernel pass, `min(q₀, D) - 1` times (halve the bit weight `W` by dropping `K` bits; kernel
   pass), the padding (unconditional: `drvNpad = 0` in the no-rows case);
3. the descriptors; two record-order reversals (stack `11` → `12` → array); drop everything.
Helpers live in `SubNLogN.Machine.Layer.DrvPPAux`.
-/

namespace SubNLogN.Machine.Layer.DrvPPAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks (padR q0Of)

/-! ## Layout -/

section QLayout

variable {Epar Eshl Esc Eck Epad Edsc : Type}

/-- Private stacks of the kernels (nested abbreviations keep instance terms small). -/
abbrev QE2 (Epad Edsc : Type) : Type := Epad ⊕ Edsc

/-- See `QE2`. -/
abbrev QE3 (Eck Epad Edsc : Type) : Type := Eck ⊕ QE2 Epad Edsc

/-- See `QE2`. -/
abbrev QE4 (Esc Eck Epad Edsc : Type) : Type := Esc ⊕ QE3 Eck Epad Edsc

/-- See `QE2`. -/
abbrev QE5 (Eshl Esc Eck Epad Edsc : Type) : Type := Eshl ⊕ QE4 Esc Eck Epad Edsc

/-- See `QE2`. -/
abbrev QE6 (Epar Eshl Esc Eck Epad Edsc : Type) : Type := Epar ⊕ QE5 Eshl Esc Eck Epad Edsc

/-- Private stacks of the pre-phase: sixteen own stacks, then the kernels' private stacks. -/
abbrev QE (Epar Eshl Esc Eck Epad Edsc : Type) : Type :=
  Fin 16 ⊕ QE6 Epar Eshl Esc Eck Epad Edsc

/-- Stacks of the pre-phase. -/
abbrev QLoc (Epar Eshl Esc Eck Epad Edsc : Type) : Type :=
  KLoc (Fin 3) (QE Epar Eshl Esc Eck Epad Edsc)

/-! Decidable equality, level by level (a direct search over the nested sums times out). -/

instance instDecEqQE2 [DecidableEq Epad] [DecidableEq Edsc] : DecidableEq (QE2 Epad Edsc) :=
  inferInstanceAs (DecidableEq (Epad ⊕ Edsc))

instance instDecEqQE3 [DecidableEq Eck] [DecidableEq Epad] [DecidableEq Edsc] :
    DecidableEq (QE3 Eck Epad Edsc) :=
  inferInstanceAs (DecidableEq (Eck ⊕ QE2 Epad Edsc))

instance instDecEqQE4 [DecidableEq Esc] [DecidableEq Eck] [DecidableEq Epad] [DecidableEq Edsc] :
    DecidableEq (QE4 Esc Eck Epad Edsc) :=
  inferInstanceAs (DecidableEq (Esc ⊕ QE3 Eck Epad Edsc))

instance instDecEqQE5 [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck] [DecidableEq Epad]
    [DecidableEq Edsc] : DecidableEq (QE5 Eshl Esc Eck Epad Edsc) :=
  inferInstanceAs (DecidableEq (Eshl ⊕ QE4 Esc Eck Epad Edsc))

instance instDecEqQE6 [DecidableEq Epar] [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck]
    [DecidableEq Epad] [DecidableEq Edsc] : DecidableEq (QE6 Epar Eshl Esc Eck Epad Edsc) :=
  inferInstanceAs (DecidableEq (Epar ⊕ QE5 Eshl Esc Eck Epad Edsc))

instance instDecEqQE [DecidableEq Epar] [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck]
    [DecidableEq Epad] [DecidableEq Edsc] : DecidableEq (QE Epar Eshl Esc Eck Epad Edsc) :=
  inferInstanceAs (DecidableEq (Fin 16 ⊕ QE6 Epar Eshl Esc Eck Epad Edsc))

instance instDecEqQLoc [DecidableEq Epar] [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck]
    [DecidableEq Epad] [DecidableEq Edsc] : DecidableEq (QLoc Epar Eshl Esc Eck Epad Edsc) :=
  inferInstanceAs (DecidableEq (Fin 3 ⊕ QE Epar Eshl Esc Eck Epad Edsc))

instance instFintypeQE2 [Fintype Epad] [Fintype Edsc] : Fintype (QE2 Epad Edsc) :=
  inferInstanceAs (Fintype (Epad ⊕ Edsc))

instance instFintypeQE3 [Fintype Eck] [Fintype Epad] [Fintype Edsc] :
    Fintype (QE3 Eck Epad Edsc) :=
  inferInstanceAs (Fintype (Eck ⊕ QE2 Epad Edsc))

instance instFintypeQE4 [Fintype Esc] [Fintype Eck] [Fintype Epad] [Fintype Edsc] :
    Fintype (QE4 Esc Eck Epad Edsc) :=
  inferInstanceAs (Fintype (Esc ⊕ QE3 Eck Epad Edsc))

instance instFintypeQE5 [Fintype Eshl] [Fintype Esc] [Fintype Eck] [Fintype Epad]
    [Fintype Edsc] : Fintype (QE5 Eshl Esc Eck Epad Edsc) :=
  inferInstanceAs (Fintype (Eshl ⊕ QE4 Esc Eck Epad Edsc))

instance instFintypeQE6 [Fintype Epar] [Fintype Eshl] [Fintype Esc] [Fintype Eck]
    [Fintype Epad] [Fintype Edsc] : Fintype (QE6 Epar Eshl Esc Eck Epad Edsc) :=
  inferInstanceAs (Fintype (Epar ⊕ QE5 Eshl Esc Eck Epad Edsc))

instance instFintypeQE [Fintype Epar] [Fintype Eshl] [Fintype Esc] [Fintype Eck]
    [Fintype Epad] [Fintype Edsc] : Fintype (QE Epar Eshl Esc Eck Epad Edsc) :=
  inferInstanceAs (Fintype (Fin 16 ⊕ QE6 Epar Eshl Esc Eck Epad Edsc))

/-- The array stack. -/
def qA : QLoc Epar Eshl Esc Eck Epad Edsc := .inl 0

/-- The header stack. -/
def qH : QLoc Epar Eshl Esc Eck Epad Edsc := .inl 1

/-- The descriptor stack. -/
def qD : QLoc Epar Eshl Esc Eck Epad Edsc := .inl 2

/-- Own stack `j`. -/
def qS (j : Fin 16) : QLoc Epar Eshl Esc Eck Epad Edsc := .inr (.inl j)

/-- The parameter kernel's stacks: header, own stacks `0, …, 10`. -/
def κPar : KLoc (Fin 12) Epar → QLoc Epar Eshl Esc Eck Epad Edsc
  | .inl i => if h : i.val = 0 then qH else qS ⟨i.val - 1, by have := i.isLt; omega⟩
  | .inr e => .inr (.inr (.inl e))

/-- The shift's stacks: array, own stacks `11, 0, 1, 2`. -/
def κShl : KLoc (Fin 5) Eshl → QLoc Epar Eshl Esc Eck Epad Edsc
  | .inl i => if i.val = 0 then qA else if i.val = 1 then qS 11 else if i.val = 2 then qS 0
    else if i.val = 3 then qS 1 else qS 2
  | .inr e => .inr (.inr (.inr (.inl e)))

/-- The phase scan's stacks: own stacks `11, 3`. -/
def κSc : KLoc (Fin 2) Esc → QLoc Epar Eshl Esc Eck Epad Edsc
  | .inl i => if i.val = 0 then qS 11 else qS 3
  | .inr e => .inr (.inr (.inr (.inr (.inl e))))

/-- The kernel pass's stacks: own stacks `11, 5, 1`. -/
def κCk : KLoc (Fin 3) Eck → QLoc Epar Eshl Esc Eck Epad Edsc
  | .inl i => if i.val = 0 then qS 11 else if i.val = 1 then qS 5 else qS 1
  | .inr e => .inr (.inr (.inr (.inr (.inr (.inl e)))))

/-- The padding's stacks: own stacks `11, 8, 9, 10, 1`. -/
def κPad : KLoc (Fin 5) Epad → QLoc Epar Eshl Esc Eck Epad Edsc
  | .inl i => if i.val = 0 then qS 11 else if i.val = 1 then qS 8 else if i.val = 2 then qS 9
    else if i.val = 3 then qS 10 else qS 1
  | .inr e => .inr (.inr (.inr (.inr (.inr (.inr (.inl e))))))

/-- The descriptor kernel's stacks: header, descriptor stack. -/
def κDsc : KLoc (Fin 2) Edsc → QLoc Epar Eshl Esc Eck Epad Edsc
  | .inl i => if i.val = 0 then qH else qD
  | .inr e => .inr (.inr (.inr (.inr (.inr (.inr (.inr e))))))

theorem κPar_injective :
    Function.Injective (κPar : KLoc (Fin 12) Epar → QLoc Epar Eshl Esc Eck Epad Edsc) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [κPar] at h
    split_ifs at h <;> simp_all [qA, qH, qD, qS]
    all_goals omega
  · simp only [κPar] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κPar] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κPar] at h
    simp_all

theorem κShl_injective :
    Function.Injective (κShl : KLoc (Fin 5) Eshl → QLoc Epar Eshl Esc Eck Epad Edsc) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [κShl] at h
    split_ifs at h <;> simp_all [qA, qH, qD, qS]
    all_goals omega
  · simp only [κShl] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κShl] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κShl] at h
    simp_all

theorem κSc_injective :
    Function.Injective (κSc : KLoc (Fin 2) Esc → QLoc Epar Eshl Esc Eck Epad Edsc) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [κSc] at h
    split_ifs at h <;> simp_all [qA, qH, qD, qS]
    all_goals omega
  · simp only [κSc] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κSc] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κSc] at h
    simp_all

theorem κCk_injective :
    Function.Injective (κCk : KLoc (Fin 3) Eck → QLoc Epar Eshl Esc Eck Epad Edsc) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [κCk] at h
    split_ifs at h <;> simp_all [qA, qH, qD, qS]
    all_goals omega
  · simp only [κCk] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κCk] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κCk] at h
    simp_all

theorem κPad_injective :
    Function.Injective (κPad : KLoc (Fin 5) Epad → QLoc Epar Eshl Esc Eck Epad Edsc) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [κPad] at h
    split_ifs at h <;> simp_all [qA, qH, qD, qS]
    all_goals omega
  · simp only [κPad] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κPad] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κPad] at h
    simp_all

theorem κDsc_injective :
    Function.Injective (κDsc : KLoc (Fin 2) Edsc → QLoc Epar Eshl Esc Eck Epad Edsc) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [κDsc] at h
    split_ifs at h <;> simp_all [qA, qH, qD, qS]
    all_goals omega
  · simp only [κDsc] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κDsc] at h
    split_ifs at h <;> simp [qA, qH, qD, qS] at h
  · simp only [κDsc] at h
    simp_all

end QLayout

/-! ## Registers and the program -/

section QRegs

variable (Rpar Rshl Rsc Rck Rpad Rdsc : Type)

/-- Registers of the pre-phase: a symbol register and the six kernels' registers. -/
abbrev QReg : Type := Option Sym × Rpar × Rshl × Rsc × Rck × Rpad × Rdsc

/-- Lens onto the symbol register. -/
def mO : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) (Option Sym) where
  get v := v.1
  set v w := (w, v.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the parameter kernel's registers. -/
def mPar : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) Rpar where
  get v := v.2.1
  set v w := (v.1, w, v.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the shift's registers. -/
def mShl : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) Rshl where
  get v := v.2.2.1
  set v w := (v.1, v.2.1, w, v.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the phase scan's registers. -/
def mSc : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) Rsc where
  get v := v.2.2.2.1
  set v w := (v.1, v.2.1, v.2.2.1, w, v.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the kernel pass's registers. -/
def mCk : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) Rck where
  get v := v.2.2.2.2.1
  set v w := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, w, v.2.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the padding's registers. -/
def mPad : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) Rpad where
  get v := v.2.2.2.2.2.1
  set v w := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, w, v.2.2.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the descriptor kernel's registers. -/
def mDsc : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) Rdsc where
  get v := v.2.2.2.2.2.2
  set v w := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

instance instFiniteQReg [Finite Rpar] [Finite Rshl] [Finite Rsc] [Finite Rck] [Finite Rpad]
    [Finite Rdsc] : Finite (QReg Rpar Rshl Rsc Rck Rpad Rdsc) :=
  have h2 : Finite (Rpad × Rdsc) := inferInstance
  have h3 : Finite (Rck × (Rpad × Rdsc)) := inferInstance
  have h4 : Finite (Rsc × (Rck × (Rpad × Rdsc))) := inferInstance
  have h5 : Finite (Rshl × (Rsc × (Rck × (Rpad × Rdsc)))) := inferInstance
  have h6 : Finite (Rpar × (Rshl × (Rsc × (Rck × (Rpad × Rdsc))))) := inferInstance
  inferInstanceAs (Finite (Option Sym × (Rpar × (Rshl × (Rsc × (Rck × (Rpad × Rdsc)))))))

end QRegs

section QProgram

variable {Epar Eshl Esc Eck Epad Edsc Rpar Rshl Rsc Rck Rpad Rdsc : Type}

/-- Push a `mark` on own stack `j`. -/
def pushQ (j : Fin 16) :
    Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym) (QReg Rpar Rshl Rsc Rck Rpad Rdsc) :=
  WP.W9comp.pushConst (qS j) Sym.mark

/-- Pop one symbol from own stack `j`. -/
def popQ (j : Fin 16) :
    Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym) (QReg Rpar Rshl Rsc Rck Rpad Rdsc) :=
  .pop (qS j) (fun v _ => v)

/-- Drop `n + 1` header fields from own stack `j`. -/
def dropQ (j : Fin 16) (n : ℕ) :
    Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym) (QReg Rpar Rshl Rsc Rck Rpad Rdsc) :=
  (DriverAux.dropHdr (qS j) n).liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc)

/-- The floors: own stacks `0, …, 6, 8, …, 15`. -/
def guardsQ :
    Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym) (QReg Rpar Rshl Rsc Rck Rpad Rdsc) :=
  .seq (pushQ 0) (.seq (pushQ 1) (.seq (pushQ 2) (.seq (pushQ 3) (.seq (pushQ 4) (.seq (pushQ 5)
    (.seq (pushQ 6) (.seq (pushQ 8) (.seq (pushQ 9) (.seq (pushQ 10) (.seq (pushQ 11)
    (.seq (pushQ 12) (.seq (pushQ 13) (.seq (pushQ 14) (pushQ 15))))))))))))))

/-- The cleanup. -/
def cleanQ :
    Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym) (QReg Rpar Rshl Rsc Rck Rpad Rdsc) :=
  .seq (dropQ 0 0) (.seq (dropQ 1 0) (.seq (dropQ 2 0) (.seq (dropQ 3 7) (.seq (popQ 3)
    (.seq (popQ 4) (.seq (dropQ 5 0) (.seq (dropQ 6 0) (.seq (popQ 7) (.seq (dropQ 8 0)
    (.seq (dropQ 9 0) (.seq (dropQ 10 0) (.seq (popQ 11) (.seq (popQ 12) (.seq (popQ 13)
    (.seq (popQ 14) (popQ 15))))))))))))))))

/-- Halve the bit weight on own stack `5`: copy `K` (stack `6`) to stack `14`, then drop `K` bits
of stack `5` (a countdown on stack `14`). -/
def halveQ :
    Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym) (QReg Rpar Rshl Rsc Rck Rpad Rdsc) :=
  .seq (FFT.DIF.copyBits (mO Rpar Rshl Rsc Rck Rpad Rdsc) (qS 6) (qS 14) (qS 13))
    (Calculus.countdown (mO Rpar Rshl Rsc Rck Rpad Rdsc) (qS 14) (qS 15) (popQ 5))

/-- **The pre-phase program.** -/
def preProg (Ppar : Prog (KLoc (Fin 12) Epar) (fun _ => Sym) Rpar)
    (Pshl : Prog (KLoc (Fin 5) Eshl) (fun _ => Sym) Rshl)
    (Psc : Prog (KLoc (Fin 2) Esc) (fun _ => Sym) Rsc)
    (Pck : Prog (KLoc (Fin 3) Eck) (fun _ => Sym) Rck)
    (Ppad : Prog (KLoc (Fin 5) Epad) (fun _ => Sym) Rpad)
    (Pdsc : Prog (KLoc (Fin 2) Edsc) (fun _ => Sym) Rdsc) :
    Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym) (QReg Rpar Rshl Rsc Rck Rpad Rdsc) :=
  .seq guardsQ (.seq (callInj κPar (mPar Rpar Rshl Rsc Rck Rpad Rdsc) Ppar)
    (.seq (callInj κShl (mShl Rpar Rshl Rsc Rck Rpad Rdsc) Pshl)
    (.seq (callInj κSc (mSc Rpar Rshl Rsc Rck Rpad Rdsc) Psc)
    (.seq (callInj κCk (mCk Rpar Rshl Rsc Rck Rpad Rdsc) Pck)
    (.seq ((Lib.dec (qS 4) (qS 15)).liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc))
    (.seq (Calculus.countdown (mO Rpar Rshl Rsc Rck Rpad Rdsc) (qS 4) (qS 15)
      (.seq halveQ (callInj κCk (mCk Rpar Rshl Rsc Rck Rpad Rdsc) Pck)))
    (.seq (callInj κPad (mPad Rpar Rshl Rsc Rck Rpad Rdsc) Ppad)
    (.seq (callInj κDsc (mDsc Rpar Rshl Rsc Rck Rpad Rdsc) Pdsc)
    (.seq ((Calculus.passR Sym.mark Sym.mark (qS 11) (qS 13) (qS 12)).liftRegs
      (mO Rpar Rshl Rsc Rck Rpad Rdsc))
    (.seq ((Calculus.passR Sym.mark Sym.mark (qS 12) (qS 13) qA).liftRegs
      (mO Rpar Rshl Rsc Rck Rpad Rdsc)) cleanQ))))))))))

theorem closed_guardsQ :
    (guardsQ : Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym)
      (QReg Rpar Rshl Rsc Rck Rpad Rdsc)).Closed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact WP.W9comp.closed_pushConst _ _

theorem closed_dropQ (j : Fin 16) (n : ℕ) :
    (dropQ j n : Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym)
      (QReg Rpar Rshl Rsc Rck Rpad Rdsc)).Closed :=
  WP.W9comp.closed_liftRegs _ (DriverAux.closed_dropHdr _ _)

theorem closed_cleanQ :
    (cleanQ : Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym)
      (QReg Rpar Rshl Rsc Rck Rpad Rdsc)).Closed :=
  ⟨closed_dropQ _ _, closed_dropQ _ _, closed_dropQ _ _, closed_dropQ _ _, trivial, trivial,
    closed_dropQ _ _, closed_dropQ _ _, trivial, closed_dropQ _ _, closed_dropQ _ _,
    closed_dropQ _ _, trivial, trivial, trivial, trivial, trivial⟩

theorem closed_halveQ :
    (halveQ : Prog (QLoc Epar Eshl Esc Eck Epad Edsc) (fun _ => Sym)
      (QReg Rpar Rshl Rsc Rck Rpad Rdsc)).Closed :=
  ⟨FFT.DIF.closed_copyBits _ _ _ _, Calculus.closed_countdown _ _ _ trivial⟩

theorem closed_preProg {Ppar : Prog (KLoc (Fin 12) Epar) (fun _ => Sym) Rpar}
    {Pshl : Prog (KLoc (Fin 5) Eshl) (fun _ => Sym) Rshl}
    {Psc : Prog (KLoc (Fin 2) Esc) (fun _ => Sym) Rsc}
    {Pck : Prog (KLoc (Fin 3) Eck) (fun _ => Sym) Rck}
    {Ppad : Prog (KLoc (Fin 5) Epad) (fun _ => Sym) Rpad}
    {Pdsc : Prog (KLoc (Fin 2) Edsc) (fun _ => Sym) Rdsc}
    (hpar : Ppar.Closed) (hshl : Pshl.Closed) (hsc : Psc.Closed) (hck : Pck.Closed)
    (hpad : Ppad.Closed) (hdsc : Pdsc.Closed) :
    (preProg Ppar Pshl Psc Pck Ppad Pdsc).Closed :=
  ⟨closed_guardsQ, closed_callInj _ _ hpar, closed_callInj _ _ hshl, closed_callInj _ _ hsc,
    closed_callInj _ _ hck, WP.W9comp.closed_liftRegs _ (Calculus.FramePassRAux.closed_dec _ _),
    Calculus.closed_countdown _ _ _ ⟨closed_halveQ, closed_callInj _ _ hck⟩,
    closed_callInj _ _ hpad, closed_callInj _ _ hdsc,
    WP.W9comp.closed_liftRegs _ (Calculus.closed_passR _ _ _ _ _),
    WP.W9comp.closed_liftRegs _ (Calculus.closed_passR _ _ _ _ _), closed_cleanQ⟩

end QProgram

/-! ## States -/

section QStates

variable {Epar Eshl Esc Eck Epad Edsc : Type}

/-- The state `S` with array `a`, the prefix `dp` on the descriptor stack and `pre j` on own
stack `j`. -/
def qst (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym
  | .inl i => if i.val = 0 then a else if i.val = 2 then dp ++ S (.inl i) else S (.inl i)
  | .inr (.inl j) => pre j ++ S (.inr (.inl j))
  | .inr (.inr e) => S (.inr (.inr e))

variable [DecidableEq Epar] [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck]
  [DecidableEq Epad] [DecidableEq Edsc]

theorem qst_upd_qS (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (j : Fin 16) (q : List Sym) :
    Function.update (qst S a dp pre) (qS j) (q ++ S (qS j)) =
      qst S a dp (Function.update pre j q) := by
  funext l
  rcases l with i | j' | e
  · simp [qst, qS, Function.update_apply]
  · by_cases h : j' = j
    · subst h
      simp [qst, qS]
    · simp [qst, qS, Function.update_apply, h]
  · simp [qst, qS, Function.update_apply]

theorem qst_upd_qA (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (a' : List Sym) :
    Function.update (qst S a dp pre) qA a' = qst S a' dp pre := by
  funext l
  rcases l with i | j | e
  · fin_cases i <;> simp [qst, qA, Function.update_apply]
  · simp [qst, qA, Function.update_apply]
  · simp [qst, qA, Function.update_apply]

theorem qst_upd_qD (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (dp' : List Sym) :
    Function.update (qst S a dp pre) qD (dp' ++ S qD) = qst S a dp' pre := by
  funext l
  rcases l with i | j | e
  · fin_cases i <;> simp [qst, qD, Function.update_apply]
  · simp [qst, qD, Function.update_apply]
  · simp [qst, qD, Function.update_apply]

theorem qst_nil (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym) :
    qst S a dp (fun _ => []) = Function.update (Function.update S qA a) qD (dp ++ S qD) := by
  funext l
  rcases l with i | j | e
  · fin_cases i <;> simp [qst, qA, qD, Function.update_apply]
  · simp [qst, qA, qD, Function.update_apply]
  · simp [qst, qA, qD, Function.update_apply]

theorem qst_init (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) :
    qst S (S qA) [] (fun _ => []) = S := by
  rw [qst_nil, List.nil_append, Function.update_eq_self, Function.update_eq_self]

end QStates

end SubNLogN.Machine.Layer.DrvPPAux
