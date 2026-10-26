/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPostMath
import SubNLogN.Machine.Layer.DrvPostCost
import SubNLogN.Machine.Arith.Shift
import SubNLogN.Machine.Calculus.FramePassR

/-!
# Layer driver post-phase: the reduction (`Machine/Layer/DrvPost.lean`)

**Scope (honest summary).** Proves `drvPost_of_parts (p) (hp : p.OK) (hParams : DrvPostParamsStmt)
(hUnpad : DrvUnpadStmt) (hScan : DrvPhaseScanStmt) : DrvPostStmt p`; the truncating shift is
`Arith.truncShift_holds` (proved). The program (`postProg`), on the array stack `0` and the header
stack `1` plus ten own stacks and the kernels' private stacks:
1. push a `mark` floor on the own stacks `0, 1, 3, …, 9`;
2. the parameter kernel (`DrvPostParamsStmt`) pushes `drvKeep`, `drvNpad`, the rows flag, the scan
   header, `w_g + 1`, `w`, `drvPostShift` on the own stacks `0, …, 6`; the flag is popped;
3. unpad (`DrvUnpadStmt`, blocks of `drvKeep + drvNpad` records; in the no-rows case `drvNpad = 0` and
   the blocks are the `A` prefix blocks, so it changes nothing);
4. the phase scan (`DrvPhaseScanStmt`: `𝒮_D`, the phase of `b^D` and its factor `1 - i`);
5. the truncating shift by `drvPostShift` (array → own stack `7`), and two record-order reversals
   (`Calculus.passR`, stack `7` → `8` → array);
6. drop the parameters and the floors.
The value bridge is `post_enc_rows` / `post_enc_small` (`DrvPostMath.lean`), the step count
`postSteps_le` (`DrvPostCost.lean`). Helpers live in `SubNLogN.Machine.Layer.DrvPPAux`.
-/

namespace SubNLogN.Machine.Layer.DrvPPAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks (padR q0Of)

/-! ## Layout -/

section Layout

variable {Epar Eun Esc Etr : Type}

/-- Private stacks of the post-phase: ten own stacks, then the four kernels' private stacks. -/
abbrev PE (Epar Eun Esc Etr : Type) : Type := Fin 10 ⊕ Epar ⊕ Eun ⊕ Esc ⊕ Etr

/-- Stacks of the post-phase. -/
abbrev PLoc (Epar Eun Esc Etr : Type) : Type := KLoc (Fin 2) (PE Epar Eun Esc Etr)

/-- The array stack. -/
def pA : PLoc Epar Eun Esc Etr := .inl 0

/-- The header stack. -/
def pH : PLoc Epar Eun Esc Etr := .inl 1

/-- Own stack `j`. -/
def pS (j : Fin 10) : PLoc Epar Eun Esc Etr := .inr (.inl j)

/-- The parameter kernel's stacks: header, own stacks `0, …, 6`. -/
def ιPar : KLoc (Fin 8) Epar → PLoc Epar Eun Esc Etr
  | .inl i => if h : i.val = 0 then pH else pS ⟨i.val - 1, by have := i.isLt; omega⟩
  | .inr e => .inr (.inr (.inl e))

/-- The unpad kernel's stacks: array, own stacks `0, 1`. -/
def ιUn : KLoc (Fin 3) Eun → PLoc Epar Eun Esc Etr
  | .inl i => if i.val = 0 then pA else if i.val = 1 then pS 0 else pS 1
  | .inr e => .inr (.inr (.inr (.inl e)))

/-- The phase scan's stacks: array, own stack `3`. -/
def ιSc : KLoc (Fin 2) Esc → PLoc Epar Eun Esc Etr
  | .inl i => if i.val = 0 then pA else pS 3
  | .inr e => .inr (.inr (.inr (.inr (.inl e))))

/-- The truncating shift's stacks: array, own stacks `7, 4, 5, 6`. -/
def ιTr : KLoc (Fin 5) Etr → PLoc Epar Eun Esc Etr
  | .inl i => if i.val = 0 then pA else if i.val = 1 then pS 7 else if i.val = 2 then pS 4
    else if i.val = 3 then pS 5 else pS 6
  | .inr e => .inr (.inr (.inr (.inr (.inr e))))

theorem ιPar_injective :
    Function.Injective (ιPar : KLoc (Fin 8) Epar → PLoc Epar Eun Esc Etr) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [ιPar] at h
    split_ifs at h <;> simp_all [pH, pS]
    all_goals omega
  · simp only [ιPar] at h
    split_ifs at h <;> simp [pH, pS] at h
  · simp only [ιPar] at h
    split_ifs at h <;> simp [pH, pS] at h
  · simp only [ιPar] at h
    simp_all

theorem ιUn_injective :
    Function.Injective (ιUn : KLoc (Fin 3) Eun → PLoc Epar Eun Esc Etr) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [ιUn] at h
    split_ifs at h <;> simp_all [pA, pS]
    all_goals omega
  · simp only [ιUn] at h
    split_ifs at h <;> simp [pA, pS] at h
  · simp only [ιUn] at h
    split_ifs at h <;> simp [pA, pS] at h
  · simp only [ιUn] at h
    simp_all

theorem ιSc_injective :
    Function.Injective (ιSc : KLoc (Fin 2) Esc → PLoc Epar Eun Esc Etr) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [ιSc] at h
    split_ifs at h <;> simp_all [pA, pS]
    all_goals omega
  · simp only [ιSc] at h
    split_ifs at h <;> simp [pA, pS] at h
  · simp only [ιSc] at h
    split_ifs at h <;> simp [pA, pS] at h
  · simp only [ιSc] at h
    simp_all

theorem ιTr_injective :
    Function.Injective (ιTr : KLoc (Fin 5) Etr → PLoc Epar Eun Esc Etr) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [ιTr] at h
    split_ifs at h <;> simp_all [pA, pS]
    all_goals omega
  · simp only [ιTr] at h
    split_ifs at h <;> simp [pA, pS] at h
  · simp only [ιTr] at h
    split_ifs at h <;> simp [pA, pS] at h
  · simp only [ιTr] at h
    simp_all

end Layout

/-! ## Registers and the program -/

section Regs

variable (Rpar Run Rsc Rtr : Type)

/-- Registers of the post-phase: a symbol register and the four kernels' registers. -/
abbrev PReg : Type := Option Sym × Rpar × Run × Rsc × Rtr

/-- Lens onto the symbol register. -/
def lO : Lens (PReg Rpar Run Rsc Rtr) (Option Sym) where
  get v := v.1
  set v w := (w, v.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the parameter kernel's registers. -/
def lPar : Lens (PReg Rpar Run Rsc Rtr) Rpar where
  get v := v.2.1
  set v w := (v.1, w, v.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the unpad kernel's registers. -/
def lUn : Lens (PReg Rpar Run Rsc Rtr) Run where
  get v := v.2.2.1
  set v w := (v.1, v.2.1, w, v.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the phase scan's registers. -/
def lSc : Lens (PReg Rpar Run Rsc Rtr) Rsc where
  get v := v.2.2.2.1
  set v w := (v.1, v.2.1, v.2.2.1, w, v.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the truncating shift's registers. -/
def lTr : Lens (PReg Rpar Run Rsc Rtr) Rtr where
  get v := v.2.2.2.2
  set v w := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

end Regs

section Program

variable {Epar Eun Esc Etr Rpar Run Rsc Rtr : Type}

/-- Push the `mark` floors on the own stacks `0, 1, 3, …, 9`. -/
def guardsP : Prog (PLoc Epar Eun Esc Etr) (fun _ => Sym) (PReg Rpar Run Rsc Rtr) :=
  .seq (WP.W9comp.pushConst (pS 0) Sym.mark) (.seq (WP.W9comp.pushConst (pS 1) Sym.mark)
    (.seq (WP.W9comp.pushConst (pS 3) Sym.mark) (.seq (WP.W9comp.pushConst (pS 4) Sym.mark)
    (.seq (WP.W9comp.pushConst (pS 5) Sym.mark) (.seq (WP.W9comp.pushConst (pS 6) Sym.mark)
    (.seq (WP.W9comp.pushConst (pS 7) Sym.mark) (.seq (WP.W9comp.pushConst (pS 8) Sym.mark)
      (WP.W9comp.pushConst (pS 9) Sym.mark))))))))

/-- Pop one symbol from own stack `j`. -/
def popP (j : Fin 10) : Prog (PLoc Epar Eun Esc Etr) (fun _ => Sym) (PReg Rpar Run Rsc Rtr) :=
  .pop (pS j) (fun v _ => v)

/-- Drop `n + 1` header fields from own stack `j`. -/
def dropP (j : Fin 10) (n : ℕ) : Prog (PLoc Epar Eun Esc Etr) (fun _ => Sym) (PReg Rpar Run Rsc Rtr) :=
  (DriverAux.dropHdr (pS j) n).liftRegs (lO Rpar Run Rsc Rtr)

/-- Drop the floors and the parameters. -/
def cleanP : Prog (PLoc Epar Eun Esc Etr) (fun _ => Sym) (PReg Rpar Run Rsc Rtr) :=
  .seq (popP 7) (.seq (popP 8) (.seq (popP 9) (.seq (dropP 0 0) (.seq (dropP 1 0)
    (.seq (dropP 3 7) (.seq (popP 3) (.seq (dropP 4 0) (.seq (dropP 5 0) (dropP 6 0)))))))))

/-- **The post-phase program.** -/
def postProg (Ppar : Prog (KLoc (Fin 8) Epar) (fun _ => Sym) Rpar)
    (Pun : Prog (KLoc (Fin 3) Eun) (fun _ => Sym) Run)
    (Psc : Prog (KLoc (Fin 2) Esc) (fun _ => Sym) Rsc)
    (Ptr : Prog (KLoc (Fin 5) Etr) (fun _ => Sym) Rtr) :
    Prog (PLoc Epar Eun Esc Etr) (fun _ => Sym) (PReg Rpar Run Rsc Rtr) :=
  .seq guardsP (.seq (callInj ιPar (lPar Rpar Run Rsc Rtr) Ppar) (.seq (popP 2)
    (.seq (callInj ιUn (lUn Rpar Run Rsc Rtr) Pun) (.seq (callInj ιSc (lSc Rpar Run Rsc Rtr) Psc)
    (.seq (callInj ιTr (lTr Rpar Run Rsc Rtr) Ptr)
    (.seq ((Calculus.passR Sym.mark Sym.mark (pS 7) (pS 9) (pS 8)).liftRegs (lO Rpar Run Rsc Rtr))
    (.seq ((Calculus.passR Sym.mark Sym.mark (pS 8) (pS 9) pA).liftRegs (lO Rpar Run Rsc Rtr))
      cleanP)))))))

theorem closed_guardsP :
    (guardsP : Prog (PLoc Epar Eun Esc Etr) (fun _ => Sym) (PReg Rpar Run Rsc Rtr)).Closed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact WP.W9comp.closed_pushConst _ _

theorem closed_cleanP :
    (cleanP : Prog (PLoc Epar Eun Esc Etr) (fun _ => Sym) (PReg Rpar Run Rsc Rtr)).Closed :=
  ⟨trivial, trivial, trivial, WP.W9comp.closed_liftRegs _ (DriverAux.closed_dropHdr _ _),
    WP.W9comp.closed_liftRegs _ (DriverAux.closed_dropHdr _ _),
    WP.W9comp.closed_liftRegs _ (DriverAux.closed_dropHdr _ _), trivial,
    WP.W9comp.closed_liftRegs _ (DriverAux.closed_dropHdr _ _),
    WP.W9comp.closed_liftRegs _ (DriverAux.closed_dropHdr _ _),
    WP.W9comp.closed_liftRegs _ (DriverAux.closed_dropHdr _ _)⟩

theorem closed_postProg {Ppar : Prog (KLoc (Fin 8) Epar) (fun _ => Sym) Rpar}
    {Pun : Prog (KLoc (Fin 3) Eun) (fun _ => Sym) Run}
    {Psc : Prog (KLoc (Fin 2) Esc) (fun _ => Sym) Rsc}
    {Ptr : Prog (KLoc (Fin 5) Etr) (fun _ => Sym) Rtr}
    (hpar : Ppar.Closed) (hun : Pun.Closed) (hsc : Psc.Closed) (htr : Ptr.Closed) :
    (postProg Ppar Pun Psc Ptr).Closed :=
  ⟨closed_guardsP, closed_callInj _ _ hpar, trivial, closed_callInj _ _ hun,
    closed_callInj _ _ hsc, closed_callInj _ _ htr,
    WP.W9comp.closed_liftRegs _ (Calculus.closed_passR _ _ _ _ _),
    WP.W9comp.closed_liftRegs _ (Calculus.closed_passR _ _ _ _ _), closed_cleanP⟩

end Program

/-! ## States: the array and prefixes on the own stacks -/

section States

variable {Epar Eun Esc Etr : Type}

/-- The state `S` with array `a` and the prefix `pre j` pushed on own stack `j`. -/
def pst (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (pre : Fin 10 → List Sym) :
    PLoc Epar Eun Esc Etr → List Sym
  | .inl i => if i.val = 0 then a else S (.inl i)
  | .inr (.inl j) => pre j ++ S (.inr (.inl j))
  | .inr (.inr e) => S (.inr (.inr e))

variable [DecidableEq Epar] [DecidableEq Eun] [DecidableEq Esc] [DecidableEq Etr]

theorem pst_pA (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (pre : Fin 10 → List Sym) :
    pst S a pre pA = a := rfl

theorem pst_upd_pS (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym)
    (pre : Fin 10 → List Sym) (j : Fin 10) (q : List Sym) :
    Function.update (pst S a pre) (pS j) (q ++ S (pS j)) = pst S a (Function.update pre j q) := by
  funext l
  rcases l with i | j' | e
  · simp [pst, pS, Function.update_apply]
  · by_cases h : j' = j
    · subst h
      simp [pst, pS]
    · simp [pst, pS, Function.update_apply, h]
  · simp [pst, pS, Function.update_apply]

theorem pst_upd_pA (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym)
    (pre : Fin 10 → List Sym) (a' : List Sym) :
    Function.update (pst S a pre) pA a' = pst S a' pre := by
  funext l
  rcases l with i | j | e
  · fin_cases i <;> simp [pst, pA, Function.update_apply]
  · simp [pst, pA, Function.update_apply]
  · simp [pst, pA, Function.update_apply]

theorem pst_nil (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) :
    pst S a (fun _ => []) = Function.update S pA a := by
  funext l
  rcases l with i | j | e
  · fin_cases i <;> simp [pst, pA, Function.update_apply]
  · simp [pst, pA, Function.update_apply]
  · simp [pst, pA, Function.update_apply]

theorem pst_init (S : PLoc Epar Eun Esc Etr → List Sym) : pst S (S pA) (fun _ => []) = S := by
  rw [pst_nil, Function.update_eq_self]

end States

/-! ## Steps -/

section Steps

variable {Epar Eun Esc Etr Rpar Run Rsc Rtr : Type}
variable [DecidableEq Epar] [DecidableEq Eun] [DecidableEq Esc] [DecidableEq Etr]

theorem step_push (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (pre : Fin 10 → List Sym)
    (j : Fin 10) :
    Calculus.RunsIn [] (WP.W9comp.pushConst (σ := PReg Rpar Run Rsc Rtr) (pS j) Sym.mark)
      (pst S a pre) (pst S a (Function.update pre j (Sym.mark :: pre j))) (fun _ => True) 1 := by
  have h := WP.W9comp.runs_pushConst (σ := PReg Rpar Run Rsc Rtr) (pS j) Sym.mark (pst S a pre)
  have e : Function.update (pst S a pre) (pS j) (Sym.mark :: pst S a pre (pS j)) =
      pst S a (Function.update pre j (Sym.mark :: pre j)) := by
    rw [← pst_upd_pS]
    rfl
  rw [e] at h
  exact Calculus.RunsIn.iff_runs.2 h

theorem step_pop (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (pre : Fin 10 → List Sym)
    (j : Fin 10) (d : Sym) (q : List Sym) (hj : pre j = d :: q) :
    Calculus.RunsIn [] (popP (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) j) (pst S a pre)
      (pst S a (Function.update pre j q)) (fun _ => True) 1 := by
  have h := DriverAux.runs_pop_of (σ := PReg Rpar Run Rsc Rtr) (pS j) (fun v _ => v) (pst S a pre)
  have e : Function.update (pst S a pre) (pS j) (pst S a pre (pS j)).tail =
      pst S a (Function.update pre j q) := by
    rw [← pst_upd_pS]
    show Function.update (pst S a pre) (pS j) (pre j ++ S (pS j)).tail = _
    rw [hj]
    rfl
  rw [e] at h
  exact Calculus.RunsIn.iff_runs.2 h

theorem step_drop (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (pre : Fin 10 → List Sym)
    (j : Fin 10) (n : ℕ) (fs : List ℕ) (q : List Sym) (hlen : fs.length = n + 1)
    (hj : pre j = hdrSyms fs ++ q) :
    Calculus.RunsIn [] (dropP (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) j n)
      (pst S a pre) (pst S a (Function.update pre j q)) (fun _ => True) (DriverAux.dropCost fs) := by
  have h := DriverAux.runs_dropHdr (pS j) n fs (q ++ S (pS j)) (pst S a pre) hlen
    (by show pre j ++ S (pS j) = _; rw [hj, List.append_assoc])
  rw [pst_upd_pS] at h
  exact Calculus.RunsIn.mono
    (Calculus.RunsIn.of_runs_liftRegs (lO Rpar Run Rsc Rtr) h (DriverAux.closed_dropHdr _ _) [])
    (fun _ _ => trivial) le_rfl

theorem step_passXY (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym)
    (pre : Fin 10 → List Sym) (v : List (List Bool)) (h7 : pre 7 = arrSyms v ++ [Sym.mark])
    (h9 : pre 9 = [Sym.mark]) :
    Calculus.RunsIn []
      ((Calculus.passR Sym.mark Sym.mark (pS 7) (pS 9) (pS 8)).liftRegs (lO Rpar Run Rsc Rtr))
      (pst S a pre)
      (pst S a (Function.update (Function.update pre 7 [Sym.mark]) 8 (arrSyms v.reverse ++ pre 8)))
      (fun _ => True) (8 * (arrSyms v).length + 2) := by
  have h := Calculus.runs_passR (g := Sym.mark) (gt := Sym.mark)
    (src := (pS 7 : PLoc Epar Eun Esc Etr)) (tmp := pS 9) (dst := pS 8)
    (by simp [pS]) (by simp [pS]) (by simp [pS]) rfl (by simp) rfl v (S (pS 7)) (S (pS 9))
    (pst S a pre)
    (by show pre 7 ++ S (pS 7) = _; rw [h7, List.append_assoc]; rfl)
    (by show pre 9 ++ S (pS 9) = _; rw [h9]; rfl)
  have e : Function.update (Function.update (pst S a pre) (pS 7) (Sym.mark :: S (pS 7))) (pS 8)
      (arrSyms v.reverse ++ pst S a pre (pS 8)) =
      pst S a (Function.update (Function.update pre 7 [Sym.mark]) 8 (arrSyms v.reverse ++ pre 8)) := by
    have e1 : Sym.mark :: S (pS 7) = [Sym.mark] ++ S (pS 7) := rfl
    have e2 : arrSyms v.reverse ++ pst S a pre (pS 8) = (arrSyms v.reverse ++ pre 8) ++ S (pS 8) :=
      (List.append_assoc _ _ _).symm
    rw [e1, pst_upd_pS, e2, pst_upd_pS]
  rw [e] at h
  exact Calculus.RunsIn.mono
    (Calculus.RunsIn.of_runs_liftRegs (lO Rpar Run Rsc Rtr) h (Calculus.closed_passR _ _ _ _ _) [])
    (fun _ _ => trivial) le_rfl

theorem step_passYA (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym)
    (pre : Fin 10 → List Sym) (v : List (List Bool)) (h8 : pre 8 = arrSyms v ++ [Sym.mark])
    (h9 : pre 9 = [Sym.mark]) :
    Calculus.RunsIn []
      ((Calculus.passR Sym.mark Sym.mark (pS 8) (pS 9) pA).liftRegs (lO Rpar Run Rsc Rtr))
      (pst S a pre) (pst S (arrSyms v.reverse ++ a) (Function.update pre 8 [Sym.mark]))
      (fun _ => True) (8 * (arrSyms v).length + 2) := by
  have h := Calculus.runs_passR (g := Sym.mark) (gt := Sym.mark)
    (src := (pS 8 : PLoc Epar Eun Esc Etr)) (tmp := pS 9) (dst := pA)
    (by simp [pS]) (by simp [pS, pA]) (by simp [pS, pA]) rfl (by simp) rfl v (S (pS 8)) (S (pS 9))
    (pst S a pre)
    (by show pre 8 ++ S (pS 8) = _; rw [h8, List.append_assoc]; rfl)
    (by show pre 9 ++ S (pS 9) = _; rw [h9]; rfl)
  have e : Function.update (Function.update (pst S a pre) (pS 8) (Sym.mark :: S (pS 8))) pA
      (arrSyms v.reverse ++ pst S a pre pA) =
      pst S (arrSyms v.reverse ++ a) (Function.update pre 8 [Sym.mark]) := by
    have e1 : Sym.mark :: S (pS 8) = [Sym.mark] ++ S (pS 8) := rfl
    rw [e1, pst_upd_pS, pst_pA, pst_upd_pA]
  rw [e] at h
  exact Calculus.RunsIn.mono
    (Calculus.RunsIn.of_runs_liftRegs (lO Rpar Run Rsc Rtr) h (Calculus.closed_passR _ _ _ _ _) [])
    (fun _ _ => trivial) le_rfl

/-- A kernel working in place on the array. -/
theorem step_inplace {L R : Type} [DecidableEq L] {ι : L → PLoc Epar Eun Esc Etr}
    (hι : Function.Injective ι) (l : Lens (PReg Rpar Run Rsc Rtr) R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {i0 : L} (hi0 : ι i0 = pA)
    (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (pre : Fin 10 → List Sym)
    (a' : List Sym) {T : ℕ} {Q : R → Prop}
    (hP : Runs P (pst S a pre ∘ ι) (Function.update (pst S a pre ∘ ι) i0 a') Q T) :
    Calculus.RunsIn [] (callInj ι l P) (pst S a pre) (pst S a' pre) (fun _ => True) T := by
  rw [← pst_upd_pA S a pre a']
  refine Calculus.RunsIn.of_callInj hι l hcl (Q := Q) ?_ ?_ []
  · rw [← hi0, Function.update_comp_eq_of_injective _ hι]
    exact hP
  · intro k hk
    exact Function.update_of_ne (fun h => hk i0 (hi0.trans h.symm)) _ _

/-- The truncating shift: array → own stack `7`. -/
theorem step_trunc {R : Type} (l : Lens (PReg Rpar Run Rsc Rtr) R)
    {P : Prog (KLoc (Fin 5) Etr) (fun _ => Sym) R} (hcl : P.Closed)
    (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (pre : Fin 10 → List Sym)
    (a' X : List Sym) {T : ℕ} {Q : R → Prop}
    (hP : Runs P (pst S a pre ∘ ιTr) (Function.update (Function.update (pst S a pre ∘ ιTr)
      (.inl 0) a') (.inl 1) (X ++ (pst S a pre ∘ ιTr) (.inl 1))) Q T) :
    Calculus.RunsIn [] (callInj ιTr l P) (pst S a pre)
      (pst S a' (Function.update pre 7 (X ++ pre 7))) (fun _ => True) T := by
  have h7 : X ++ pst S a pre (pS 7) = (X ++ pre 7) ++ S (pS 7) := (List.append_assoc _ _ _).symm
  have e : Function.update (Function.update (pst S a pre) pA a') (pS 7) (X ++ pst S a pre (pS 7)) =
      pst S a' (Function.update pre 7 (X ++ pre 7)) := by
    rw [pst_upd_pA, h7, pst_upd_pS]
  rw [← e]
  refine Calculus.RunsIn.of_callInj ιTr_injective l hcl (Q := Q) ?_ ?_ []
  · rw [show (pS 7 : PLoc Epar Eun Esc Etr) = ιTr (.inl 1) from rfl,
      show (pA : PLoc Epar Eun Esc Etr) = ιTr (.inl 0) from rfl,
      Function.update_comp_eq_of_injective _ ιTr_injective,
      Function.update_comp_eq_of_injective _ ιTr_injective]
    exact hP
  · intro k hk
    rw [Function.update_of_ne (show k ≠ pS 7 from fun h => hk (.inl 1) h.symm),
      Function.update_of_ne (show k ≠ pA from fun h => hk (.inl 0) h.symm)]

/-- Own-stack prefixes after the parameter kernel. -/
noncomputable def parPre (t : LayerRT) (pre : Fin 10 → List Sym) (j : Fin 10) : List Sym :=
  (if j.val = 0 then natSyms (drvKeep t) else if j.val = 1 then natSyms (drvNpad t)
    else if j.val = 2 then [drvRowsSym t] else if j.val = 3 then hdrSyms (scHdr t)
    else if j.val = 4 then natSyms (drvWg t + 1) else if j.val = 5 then natSyms t.w
    else if j.val = 6 then natSyms (drvPostShift t) else []) ++ pre j

/-- The parameter kernel. -/
theorem step_par {R : Type} (l : Lens (PReg Rpar Run Rsc Rtr) R)
    {P : Prog (KLoc (Fin 8) Epar) (fun _ => Sym) R} (hcl : P.Closed) (t : LayerRT)
    (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (pre : Fin 10 → List Sym)
    {T : ℕ} {Q : R → Prop}
    (hP : Runs P (pst S a pre ∘ ιPar) (drvPostParamsPost t (pst S a pre ∘ ιPar)) Q T) :
    Calculus.RunsIn [] (callInj ιPar l P) (pst S a pre) (pst S a (parPre t pre))
      (fun _ => True) T := by
  refine Calculus.RunsIn.of_callInj ιPar_injective l hcl (Q := Q) ?_ ?_ []
  · have e : pst S a (parPre t pre) ∘ ιPar = drvPostParamsPost t (pst S a pre ∘ ιPar) := by
      funext x
      rcases x with i | e
      · fin_cases i <;> simp [ιPar, drvPostParamsPost, pst, parPre, pS, pH, scHdr]
      · rfl
    rw [e]
    exact hP
  · intro k hk
    rcases k with i | j | e
    · rfl
    · fin_cases j
      · exact (hk (.inl 1) rfl).elim
      · exact (hk (.inl 2) rfl).elim
      · exact (hk (.inl 3) rfl).elim
      · exact (hk (.inl 4) rfl).elim
      · exact (hk (.inl 5) rfl).elim
      · exact (hk (.inl 6) rfl).elim
      · exact (hk (.inl 7) rfl).elim
      · rfl
      · rfl
      · rfl
    · rfl

/-- Own-stack prefixes after the floors. -/
def gPre (pre : Fin 10 → List Sym) (j : Fin 10) : List Sym :=
  if j.val = 2 then pre j else Sym.mark :: pre j

theorem runs_guards (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym)
    (pre : Fin 10 → List Sym) :
    Calculus.RunsIn [] (guardsP (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr))
      (pst S a pre) (pst S a (gPre pre)) (fun _ => True) 9 := by
  have h := (step_push (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) S a pre 0).seq
    ((step_push S a _ 1).seq ((step_push S a _ 3).seq ((step_push S a _ 4).seq
    ((step_push S a _ 5).seq ((step_push S a _ 6).seq ((step_push S a _ 7).seq
    ((step_push S a _ 8).seq (step_push S a _ 9))))))))
  refine Calculus.RunsIn.congr h ?_ le_rfl
  congr 1
  funext j
  fin_cases j <;> simp [gPre]

/-- Own-stack prefixes after the floors, the parameter kernel and the flag pop. -/
noncomputable def pre3 (t : LayerRT) (j : Fin 10) : List Sym :=
  if j.val = 0 then natSyms (drvKeep t) ++ [Sym.mark]
  else if j.val = 1 then natSyms (drvNpad t) ++ [Sym.mark]
  else if j.val = 2 then []
  else if j.val = 3 then hdrSyms (scHdr t) ++ [Sym.mark]
  else if j.val = 4 then natSyms (drvWg t + 1) ++ [Sym.mark]
  else if j.val = 5 then natSyms t.w ++ [Sym.mark]
  else if j.val = 6 then natSyms (drvPostShift t) ++ [Sym.mark]
  else [Sym.mark]

theorem pre3_eq (t : LayerRT) :
    Function.update (parPre t (gPre (fun _ => []))) 2 [] = pre3 t := by
  funext j
  fin_cases j <;> simp [parPre, gPre, pre3, Function.update_apply]

theorem runs_clean (S : PLoc Epar Eun Esc Etr → List Sym) (a : List Sym) (t : LayerRT) :
    Calculus.RunsIn [] (cleanP (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr))
      (pst S a (pre3 t)) (pst S a (fun _ => [])) (fun _ => True) (4 + cleanCost t) := by
  have h := (step_pop (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) S a (pre3 t) 7
      Sym.mark [] rfl).seq
    ((step_pop S a _ 8 Sym.mark [] (by simp [Function.update_apply, pre3])).seq
    ((step_pop S a _ 9 Sym.mark [] (by simp [Function.update_apply, pre3])).seq
    ((step_drop S a _ 0 0 [drvKeep t] [] rfl (by simp [Function.update_apply, pre3, hdrSyms])).seq
    ((step_drop S a _ 1 0 [drvNpad t] [] rfl (by simp [Function.update_apply, pre3, hdrSyms])).seq
    ((step_drop S a _ 3 7 (scHdr t) [Sym.mark] rfl (by simp [Function.update_apply, pre3])).seq
    ((step_pop S a _ 3 Sym.mark [] (by simp [Function.update_apply, pre3])).seq
    ((step_drop S a _ 4 0 [drvWg t + 1] [] rfl
        (by simp [Function.update_apply, pre3, hdrSyms])).seq
    ((step_drop S a _ 5 0 [t.w] [] rfl (by simp [Function.update_apply, pre3, hdrSyms])).seq
    (step_drop S a _ 6 0 [drvPostShift t] [] rfl
        (by simp [Function.update_apply, pre3, hdrSyms]))))))))))
  refine Calculus.RunsIn.congr h ?_ (by unfold cleanCost; omega)
  congr 1
  funext j
  fin_cases j <;> simp [Function.update_apply, pre3]

end Steps

/-! ## The chain -/

section Chain

/-- The unpadded array: the first `drvKeep t` records of every block. -/
def pv1 (t : LayerRT) (blks : List (List (List CInt))) : List (List CInt) :=
  (blks.map (List.take (drvKeep t))).flatten

/-- The array after the phase scan. -/
def pv2 (t : LayerRT) (blks : List (List (List CInt))) : List (List CInt) :=
  (pv1 t blks).mapIdx (phaseRec t.S t.K t.ρ t.D (drvPostC t) (t.D % 2))

/-- The array after the truncating shift. -/
def pout (t : LayerRT) (blks : List (List (List CInt))) : List (List CInt) :=
  mapC (truncShiftC (drvPostShift t)) (pv2 t blks)

/-- The parameter kernel's specification (the body of `DrvPostParamsStmt`). -/
def ParSpec {E R : Type} [DecidableEq E] (J C : ℕ) (Pr : Prog (KLoc (Fin 8) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 8) E → List Sym),
    S (.inl 0) = t.hdr ++ hrest →
    Runs Pr S (drvPostParamsPost t S) (fun _ => True) (C * (t.hdr.length + t.D * t.K + 1) ^ J)

/-- The unpad kernel's specification (the body of `DrvUnpadStmt`). -/
def UnSpec {E R : Type} [DecidableEq E] (C : ℕ) (Pr : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (N0 Npad w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 : List Sym)
    (S : KLoc (Fin 3) E → List Sym),
    (∀ blk ∈ blks, blk.length = N0 + Npad) → BlkTerm rest → TermOK r1 → TermOK r2 →
    S (.inl 0) = carrSyms w blks.flatten ++ rest → S (.inl 1) = natSyms N0 ++ r1 →
    S (.inl 2) = natSyms Npad ++ r2 →
    Runs Pr S
      (Function.update S (.inl 0) (carrSyms w (blks.map (List.take N0)).flatten ++ rest))
      (fun _ => True)
      (C * (cvol w blks.flatten + (blks.length + 1) * (bitLen N0 + bitLen Npad + 1)))

/-- The phase scan's specification (the body of `DrvPhaseScanStmt`). -/
def ScSpec {E R : Type} [DecidableEq E] (J C : ℕ) (Pr : Prog (KLoc (Fin 2) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (S K ρ D c o w1 w2 : ℕ) (v : List (List CInt)) (rest rp : List Sym)
    (St : KLoc (Fin 2) E → List Sym),
    1 ≤ S → ρ < K → o ≤ 1 → 1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v →
    CArrFits w2 (v.mapIdx (phaseRec S K ρ D c o)) → BlkTerm rest → TermOK rp →
    St (.inl 0) = carrSyms w1 v ++ rest →
    St (.inl 1) = hdrSyms [S, K, ρ, D, c, o, w1, w2] ++ rp →
    Runs Pr St
      (Function.update St (.inl 0) (carrSyms w2 (v.mapIdx (phaseRec S K ρ D c o)) ++ rest))
      (fun _ => True)
      (C * (cvol w1 v + cvol w2 v +
        (v.length + 1) * (bitLen v.length + (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length + 1) ^ J))

/-- The truncating shift's specification (the body of `TruncShiftStmt`). -/
def TrSpec {E R : Type} [DecidableEq E] (C : ℕ) (P : Prog (KLoc (Fin 5) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
    (S : KLoc (Fin 5) E → List Sym),
    1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (truncShiftC s) v) →
    BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
    S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
    S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
    Runs P S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w2 (mapC (truncShiftC s) v) ++ S (.inl 1)))
      (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

theorem termOK_mark (X : List Sym) : TermOK (Sym.mark :: X) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

theorem length_arrSyms_reverse (v : List (List Bool)) :
    (arrSyms v.reverse).length = (arrSyms v).length := by
  simp [arrSyms, blk, List.length_flatten, List.map_reverse, List.sum_reverse]

theorem length_arrSyms_crec (w : ℕ) (v : List (List CInt)) :
    (arrSyms (v.map (crecBits w))).length = cvol w v := rfl

theorem cvol_shape {w r : ℕ} {v : List (List CInt)} (h : ∀ cs ∈ v, cs.length = r) :
    cvol w v = cv w v.length r := by
  rw [cvol_eq]
  unfold ncoef cv
  rw [List.map_congr_left h, List.map_const', List.sum_replicate, smul_eq_mul]

theorem mem_pv1 {t : LayerRT} {blks : List (List (List CInt))} {cs : List CInt}
    (h : cs ∈ pv1 t blks) : cs ∈ blks.flatten := by
  unfold pv1 at h
  obtain ⟨l, hl, hcs⟩ := List.mem_flatten.1 h
  obtain ⟨blk, hblk, rfl⟩ := List.mem_map.1 hl
  exact List.mem_flatten.2 ⟨blk, hblk, List.mem_of_mem_take hcs⟩

theorem shape_pv2 {t : LayerRT} {blks : List (List (List CInt))} {r : ℕ}
    (h : ∀ cs ∈ pv1 t blks, cs.length = r) : ∀ cs ∈ pv2 t blks, cs.length = r := by
  intro cs hcs
  unfold pv2 at hcs
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hcs
  simp only [phaseRec, List.length_map]
  exact h _ (List.mem_iff_getElem.2 ⟨i, hi, rfl⟩)

theorem shape_pout {t : LayerRT} {blks : List (List (List CInt))} {r : ℕ}
    (h : ∀ cs ∈ pv2 t blks, cs.length = r) : ∀ cs ∈ pout t blks, cs.length = r := by
  intro cs hcs
  unfold pout mapC at hcs
  obtain ⟨cs', hcs', rfl⟩ := List.mem_map.1 hcs
  rw [List.length_map]
  exact h _ hcs'

/-- **The post-phase chain**: from the kernels' specifications, the program takes the array
`carrSyms w_g blks.flatten ++ rest` to `carrSyms w (pout t blks) ++ rest`, every other stack
unchanged, within `postSteps`. -/
theorem post_chain {Epar Eun Esc Etr Rpar Run Rsc Rtr : Type} [DecidableEq Epar]
    [DecidableEq Eun] [DecidableEq Esc] [DecidableEq Etr]
    {Ppar : Prog (KLoc (Fin 8) Epar) (fun _ => Sym) Rpar}
    {Pun : Prog (KLoc (Fin 3) Eun) (fun _ => Sym) Run}
    {Psc : Prog (KLoc (Fin 2) Esc) (fun _ => Sym) Rsc}
    {Ptr : Prog (KLoc (Fin 5) Etr) (fun _ => Sym) Rtr}
    (hclPar : Ppar.Closed) (hclUn : Pun.Closed) (hclSc : Psc.Closed) (hclTr : Ptr.Closed)
    {Jpar Cpar Cun Jsc Csc Ctr : ℕ}
    (hpar : ParSpec Jpar Cpar Ppar) (hun : UnSpec Cun Pun) (hsc : ScSpec Jsc Csc Psc)
    (htr : TrSpec Ctr Ptr)
    (t : LayerRT) (blks : List (List (List CInt))) (rest hrest : List Sym)
    (S : PLoc Epar Eun Esc Etr → List Sym)
    (hblk : ∀ blk ∈ blks, blk.length = drvKeep t + drvNpad t) (hrestT : BlkTerm rest)
    (hρ : t.ρ < t.K) (hS1 : 1 ≤ t.S) (hw : 1 ≤ t.w)
    (hshape : ∀ cs ∈ blks.flatten, cs.length = t.r) (hM : (pv1 t blks).length = t.M)
    (hf1 : CArrFits (drvWg t) (pv1 t blks)) (hf2 : CArrFits (drvWg t + 1) (pv2 t blks))
    (hf3 : CArrFits t.w (pout t blks))
    (h0 : S pA = carrSyms (drvWg t) blks.flatten ++ rest) (h1 : S pH = t.hdr ++ hrest) :
    Calculus.RunsIn [] (postProg Ppar Pun Psc Ptr) S
      (Function.update S pA (carrSyms t.w (pout t blks) ++ rest)) (fun _ => True)
      (postSteps Cpar Jpar Cun Csc Jsc Ctr t blks.flatten.length blks.length) := by
  have r1 := runs_guards (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) S (S pA)
    (fun _ => [])
  have r2 := step_par (lPar Rpar Run Rsc Rtr) hclPar t S (S pA) (gPre (fun _ => []))
    (hpar t hrest _ h1)
  have r3 := step_pop (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) S (S pA)
    (parPre t (gPre (fun _ => []))) 2 (drvRowsSym t) [] (by simp [parPre, gPre])
  rw [pre3_eq] at r3
  have r4 := step_inplace ιUn_injective (lUn Rpar Run Rsc Rtr) hclUn (i0 := .inl 0) rfl S (S pA)
    (pre3 t) (carrSyms (drvWg t) (pv1 t blks) ++ rest)
    (hun (drvKeep t) (drvNpad t) (drvWg t) blks rest (Sym.mark :: S (pS 0))
      (Sym.mark :: S (pS 1)) _ hblk hrestT (termOK_mark _) (termOK_mark _) h0
      (by show (natSyms (drvKeep t) ++ [Sym.mark]) ++ S (pS 0) = _; rw [List.append_assoc]; rfl)
      (by show (natSyms (drvNpad t) ++ [Sym.mark]) ++ S (pS 1) = _; rw [List.append_assoc]; rfl))
  have r5 := step_inplace ιSc_injective (lSc Rpar Run Rsc Rtr) hclSc (i0 := .inl 0) rfl S
    (carrSyms (drvWg t) (pv1 t blks) ++ rest) (pre3 t)
    (carrSyms (drvWg t + 1) (pv2 t blks) ++ rest)
    (hsc t.S t.K t.ρ t.D (drvPostC t) (t.D % 2) (drvWg t) (drvWg t + 1) (pv1 t blks) rest
      (Sym.mark :: S (pS 3)) _ hS1 hρ (by omega) (by unfold drvWg; omega) (by omega) hf1 hf2
      hrestT (termOK_mark _) rfl
      (by show (hdrSyms (scHdr t) ++ [Sym.mark]) ++ S (pS 3) = _; rw [List.append_assoc]; rfl))
  have r6 := step_trunc (lTr Rpar Run Rsc Rtr) hclTr S (carrSyms (drvWg t + 1) (pv2 t blks) ++ rest)
    (pre3 t) rest (carrSyms t.w (pout t blks))
    (htr (drvWg t + 1) t.w (drvPostShift t) (pv2 t blks) rest (Sym.mark :: S (pS 4))
      (Sym.mark :: S (pS 5)) (Sym.mark :: S (pS 6)) _ (by omega) hw hf2 hf3 hrestT
      (termOK_mark _) (termOK_mark _) (termOK_mark _) rfl
      (by show (natSyms (drvWg t + 1) ++ [Sym.mark]) ++ S (pS 4) = _; rw [List.append_assoc]; rfl)
      (by show (natSyms t.w ++ [Sym.mark]) ++ S (pS 5) = _; rw [List.append_assoc]; rfl)
      (by show (natSyms (drvPostShift t) ++ [Sym.mark]) ++ S (pS 6) = _
          rw [List.append_assoc]; rfl))
  have r7 := step_passXY (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) S rest
    (Function.update (pre3 t) 7 (carrSyms t.w (pout t blks) ++ pre3 t 7))
    ((pout t blks).map (crecBits t.w)) (by simp [Function.update_apply, pre3, carrSyms])
    (by simp [Function.update_apply, pre3])
  have r8 := step_passYA (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) S rest
    (Function.update (Function.update (Function.update (pre3 t) 7
      (carrSyms t.w (pout t blks) ++ pre3 t 7)) 7 [Sym.mark]) 8
      (arrSyms ((pout t blks).map (crecBits t.w)).reverse ++
        Function.update (pre3 t) 7 (carrSyms t.w (pout t blks) ++ pre3 t 7) 8))
    ((pout t blks).map (crecBits t.w)).reverse (by simp [Function.update_apply, pre3])
    (by simp [Function.update_apply, pre3])
  have r9 := runs_clean (Rpar := Rpar) (Run := Run) (Rsc := Rsc) (Rtr := Rtr) S
    (arrSyms ((pout t blks).map (crecBits t.w)).reverse.reverse ++ rest) t
  have e6 : Function.update (Function.update (Function.update (Function.update (pre3 t) 7
      (carrSyms t.w (pout t blks) ++ pre3 t 7)) 7 [Sym.mark]) 8
      (arrSyms ((pout t blks).map (crecBits t.w)).reverse ++
        Function.update (pre3 t) 7 (carrSyms t.w (pout t blks) ++ pre3 t 7) 8)) 8 [Sym.mark] =
      pre3 t := by
    funext j
    fin_cases j <;> simp [Function.update_apply, pre3]
  rw [← e6] at r9
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))
  rw [pst_init, pst_nil, List.reverse_reverse, length_arrSyms_reverse, length_arrSyms_crec] at hall
  refine Calculus.RunsIn.mono hall (fun _ _ => trivial) ?_
  have hsh1 : ∀ cs ∈ pv1 t blks, cs.length = t.r := fun cs h => hshape cs (mem_pv1 h)
  have hsh2 := shape_pv2 hsh1
  have hsh3 := shape_pout hsh2
  have hl2 : (pv2 t blks).length = t.M := by unfold pv2; rw [List.length_mapIdx, hM]
  have hl3 : (pout t blks).length = t.M := by unfold pout mapC; rw [List.length_map, hl2]
  rw [cvol_shape hshape, cvol_shape hsh1, cvol_shape hsh1, cvol_shape hsh2, cvol_shape hsh2,
    cvol_shape hsh3, hM, hl2, hl3]
  unfold postSteps scHdr
  omega

end Chain

/-! ## Data facts for the two cases -/

section Data

theorem encArr_length' {α : Type} {r : ℕ} (F : ℕ) (addrs : List α) (z : α → Fin r → ℂ) :
    (encArr F addrs z).length = addrs.length := by
  unfold encArr
  rw [List.length_map]

theorem encArr_shape {α : Type} {r : ℕ} (F : ℕ) (addrs : List α) (z : α → Fin r → ℂ) :
    ∀ cs ∈ encArr F addrs z, cs.length = r := by
  intro cs hcs
  unfold encArr at hcs
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hcs
  rw [List.length_map, List.length_finRange]

theorem layerAddrs_length' (A K D S : ℕ) (hA : 0 < A) (hS : 0 < S) :
    (layerAddrs A K D S hA hS).length = A * 2 ^ (K * D) * S := by
  unfold layerAddrs
  rw [List.length_map, List.length_range]

theorem length_pv1 (t : LayerRT) (blks : List (List (List CInt))) (n : ℕ)
    (hblk : ∀ blk ∈ blks, blk.length = drvKeep t + n) :
    (pv1 t blks).length = blks.length * drvKeep t := by
  unfold pv1
  rw [List.length_flatten, List.map_map]
  have h : ∀ blk ∈ blks, (List.length ∘ List.take (drvKeep t)) blk = drvKeep t := by
    intro blk hb
    rw [Function.comp_apply, List.length_take, hblk blk hb]
    omega
  rw [List.map_congr_left h, List.map_const', List.sum_replicate, smul_eq_mul]

theorem pv1_eq_flatten (t : LayerRT) (blks : List (List (List CInt)))
    (hblk : ∀ blk ∈ blks, blk.length = drvKeep t) : pv1 t blks = blks.flatten := by
  unfold pv1
  have h : blks.map (List.take (drvKeep t)) = blks := by
    conv_rhs => rw [← List.map_id blks]
    exact List.map_congr_left fun blk hb => List.take_of_length_le (le_of_eq (hblk blk hb))
  rw [h]

theorem postBlk_split (t : LayerRT) (hq : q0Of t.d ≤ t.D) :
    2 ^ (t.K * t.D) * t.S = 2 ^ (q0Of t.d * t.K) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) := by
  have e : t.K * t.D = q0Of t.d * t.K + t.K * (t.D - q0Of t.d) := by
    rw [Nat.mul_comm (q0Of t.d), ← Nat.mul_add, Nat.add_sub_cancel' hq]
  rw [e, pow_add, mul_assoc]

theorem postBlk_eq (t : LayerRT) (h : DrvRows t) : postBlk t = drvKeep t + drvNpad t := by
  have hle : 2 ^ (q0Of t.d * t.K) ≤ padR t.d t.K := by
    rw [Nat.mul_comm]
    exact le_padR t.d t.K
  unfold postBlk drvKeep drvNpad
  rw [if_pos h, postBlk_split t h.1.le, ← Nat.add_mul, Nat.add_sub_cancel' hle]

theorem postBlk_le (t : LayerRT) (h : DrvRows t) (hK : 1 ≤ t.K) : postBlk t ≤ 2 * drvKeep t := by
  have hp := DrvMathAux.padR_le t.d t.K hK
  unfold postBlk drvKeep
  rw [postBlk_split t h.1.le]
  calc padR t.d t.K * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S)
      ≤ 2 ^ (q0Of t.d * t.K + 1) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) :=
        Nat.mul_le_mul_right _ hp
    _ = 2 * (2 ^ (q0Of t.d * t.K) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S)) := by
        rw [pow_succ]
        ring

/-- Every stored component is at most `2^B` in absolute value. -/
def CAbs (B : ℕ) (v : List (List CInt)) : Prop :=
  ∀ cs ∈ v, ∀ c ∈ cs, |c.1| ≤ 2 ^ B ∧ |c.2| ≤ 2 ^ B

theorem fitsTwos_of_abs' {w q : ℕ} {a : ℤ} (h : |a| ≤ 2 ^ q) (hw : q + 2 ≤ w) : FitsTwos w a := by
  unfold FitsTwos
  have h1 : (2 : ℤ) ^ q * 2 ≤ 2 ^ (w - 1) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (0 : ℤ) < 2 ^ q := by positivity
  constructor
  · linarith [neg_abs_le a]
  · linarith [le_abs_self a]

theorem cArrFits_of_CAbs {B w : ℕ} {v : List (List CInt)} (h : CAbs B v) (hw : B + 2 ≤ w) :
    CArrFits w v :=
  fun cs hcs c hc => ⟨fitsTwos_of_abs' (h cs hcs c hc).1 hw, fitsTwos_of_abs' (h cs hcs c hc).2 hw⟩

theorem abs_gridInt_le {F B : ℕ} {z : ℂ} (hz : OnGrid F z) (hn : ‖z‖ ≤ 2 ^ B) :
    |(gridInt F z).1| ≤ 2 ^ (B + F) ∧ |(gridInt F z).2| ≤ 2 ^ (B + F) := by
  have hv := gridVal_gridInt' hz
  have hu : gridUnit F * (2 : ℝ) ^ F = 1 := gridUnit_mul_pow' F
  have hre : ((gridInt F z).1 : ℝ) = z.re * 2 ^ F := by
    have h' : ((gridInt F z).1 : ℝ) * gridUnit F = z.re := by rw [← gridVal_re, hv]
    rw [← h', mul_assoc, hu, mul_one]
  have him : ((gridInt F z).2 : ℝ) = z.im * 2 ^ F := by
    have h' : ((gridInt F z).2 : ℝ) * gridUnit F = z.im := by rw [← gridVal_im, hv]
    rw [← h', mul_assoc, hu, mul_one]
  have h2F : (0 : ℝ) < 2 ^ F := by positivity
  have key : ∀ y : ℝ, |y| ≤ ‖z‖ → |y * 2 ^ F| ≤ (2 : ℝ) ^ (B + F) := by
    intro y hy
    rw [abs_mul, abs_of_pos h2F, pow_add]
    exact mul_le_mul_of_nonneg_right (hy.trans hn) h2F.le
  constructor
  · have h3 := key _ (Complex.abs_re_le_norm z)
    rw [← hre] at h3
    exact_mod_cast h3
  · have h3 := key _ (Complex.abs_im_le_norm z)
    rw [← him] at h3
    exact_mod_cast h3

theorem CAbs_encArr {α : Type} {r : ℕ} {P b Δ : ℕ} (hb : b ≤ Δ) (addrs : List α)
    (y : α → Fin r → ℂ) (hy : ∀ x k, OnGrid (P + b) (y x k) ∧ ‖y x k‖ ≤ 2 ^ b) :
    CAbs (b + (P + Δ)) (encArr (P + Δ) addrs y) := by
  intro cs hcs c hc
  unfold encArr at hcs
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hcs
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
  exact abs_gridInt_le (OnGrid.mono (by omega) (hy x k).1) (hy x k).2

theorem CAbs_pv1 {B : ℕ} {t : LayerRT} {blks : List (List (List CInt))}
    (h : CAbs B blks.flatten) : CAbs B (pv1 t blks) :=
  fun cs hcs => h cs (mem_pv1 hcs)

theorem abs_rotC {B : ℕ} {c : CInt} (h : |c.1| ≤ 2 ^ B ∧ |c.2| ≤ 2 ^ B) (e : ℕ) :
    |(rotC e c).1| ≤ 2 ^ B ∧ |(rotC e c).2| ≤ 2 ^ B := by
  obtain ⟨h1, h2⟩ := h
  unfold rotC
  split_ifs <;> refine ⟨?_, ?_⟩ <;> (try simp only [abs_neg]) <;> assumption

theorem abs_omiC {B : ℕ} {c : CInt} (h : |c.1| ≤ 2 ^ B ∧ |c.2| ≤ 2 ^ B) :
    |(omiC c).1| ≤ 2 ^ (B + 1) ∧ |(omiC c).2| ≤ 2 ^ (B + 1) := by
  obtain ⟨h1, h2⟩ := h
  rw [abs_le] at h1 h2
  unfold omiC
  dsimp only
  rw [pow_succ]
  constructor <;> rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem CAbs_phase {B : ℕ} {v : List (List CInt)} (h : CAbs B v) (S K ρ D c o : ℕ) :
    CAbs (B + 1) (v.mapIdx (phaseRec S K ρ D c o)) := by
  intro cs hcs z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hcs
  unfold phaseRec at hz
  obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hz
  have h0 := h _ (List.mem_iff_getElem.2 ⟨i, hi, rfl⟩) z0 hz0
  have hr := abs_rotC h0 (selCount S K ρ D i + c)
  have hBB : (2 : ℤ) ^ B ≤ 2 ^ (B + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  split_ifs
  · exact abs_omiC hr
  · exact ⟨hr.1.trans hBB, hr.2.trans hBB⟩

theorem cArrFits_encLayer' {A K D S r P w : ℕ} (hA : 0 < A) (hS : 0 < S)
    {z : RArr (LayerAddr A K D S) r} (hz : ArrOnDiskGrid P z) (hw : P + 2 ≤ w) :
    CArrFits w (encLayer hA hS P z) := by
  refine cArrFits_of_CAbs (B := 0 + P) ?_ (by omega)
  intro cs hcs c hc
  unfold encLayer encArr at hcs
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hcs
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
  exact abs_gridInt_le (hz x k).1 (by simpa using (hz x k).2)

end Data

end SubNLogN.Machine.Layer.DrvPPAux

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine DrvPPAux

/-- **Proposition A.11 driver post-phase, from its parts.** With `p.OK`, the parameter kernel, the unpad
kernel and the phase scan give `DrvPostStmt p` (the truncating shift is `Arith.truncShift_holds`). -/
theorem drvPost_of_parts (p : LayerParams) (hp : p.OK) (hParams : DrvPostParamsStmt)
    (hUnpad : DrvUnpadStmt) (hScan : DrvPhaseScanStmt) : DrvPostStmt p := by
  obtain ⟨Jpar, Cpar, hParK⟩ := hParams
  obtain ⟨Cun, hUnK⟩ := hUnpad
  obtain ⟨Jsc, Csc, hScK⟩ := hScan
  obtain ⟨Ctr, hTrK⟩ := Arith.truncShift_holds
  obtain ⟨Epar, iFpar, iDpar, Rpar, Ppar, hfinPar, hnePar, hclPar, hspecPar⟩ := hParK ()
  obtain ⟨Eun, iFun, iDun, Run, Pun, hfinUn, hneUn, hclUn, hspecUn⟩ := hUnK ()
  obtain ⟨Esc, iFsc, iDsc, Rsc, Psc, hfinSc, hneSc, hclSc, hspecSc⟩ := hScK ()
  obtain ⟨Etr, iFtr, iDtr, Rtr, Ptr, hfinTr, hneTr, hclTr, hspecTr⟩ := hTrK ()
  have hpar : ParSpec Jpar Cpar Ppar := hspecPar
  have hun : UnSpec Cun Pun := hspecUn
  have hsc : ScSpec Jsc Csc Psc := hspecSc
  have htr : TrSpec Ctr Ptr := hspecTr
  obtain ⟨P₀, C, hcost⟩ := postSteps_le p hp Cpar Jpar Cun Csc Jsc Ctr
  obtain ⟨a0⟩ := hnePar
  obtain ⟨b0⟩ := hneUn
  obtain ⟨c0⟩ := hneSc
  obtain ⟨d0⟩ := hneTr
  refine ⟨P₀, C, fun _ => ⟨PE Epar Eun Esc Etr, inferInstance, inferInstance,
    PReg Rpar Run Rsc Rtr, postProg Ppar Pun Psc Ptr, inferInstance, ⟨(none, a0, b0, c0, d0)⟩,
    closed_postProg hclPar hclUn hclSc hclTr, ?_⟩⟩
  intro t hA hS rest hrest b St hband hw hrestT hbD h1
  have hρ : t.ρ < t.K := hband.2.2.2.2.2.2.2.2.2.2.1
  have hK1 : 1 ≤ t.K := by omega
  have hS1 : 1 ≤ t.S := hS
  have hw1 : 1 ≤ t.w := by omega
  have hb : b ≤ drvDelta t := by omega
  have hAM : t.A ≤ t.M := by
    unfold LayerRT.M
    calc t.A ≤ t.A * t.S := Nat.le_mul_of_pos_right _ hS
      _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hkM : t.A * drvKeep t = t.M := by
    unfold drvKeep LayerRT.M
    ring
  refine ⟨fun h y hy hdisk h0 => ?_, fun hn y hy hdisk h0 => ?_⟩
  · -- rows case
    have hA' : 0 < drvA' t := Nat.mul_pos hA h.2
    have hlen : (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y).length
        = postBlk t * t.A := by
      rw [encArr_length', layerAddrs_length']
      simp only [drvA', drvD', postBlk]
      ring
    have hflat := chunksOf_flatten _ _ _ hlen
    have hblk : ∀ blk ∈ chunksOf (postBlk t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y),
        blk.length = drvKeep t + drvNpad t := by
      intro blk hb'
      rw [chunksOf_length_mem _ _ _ hlen blk hb', postBlk_eq t h]
    have hnb := chunksOf_length (postBlk t) t.A
      (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y)
    have hshape : ∀ cs ∈ (chunksOf (postBlk t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y)).flatten,
        cs.length = t.r := by
      rw [hflat]
      exact encArr_shape _ _ _
    have hM : (pv1 t (chunksOf (postBlk t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y))).length =
        t.M := by
      rw [length_pv1 t _ _ hblk, hnb, hkM]
    have hout : pout t (chunksOf (postBlk t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y)) =
        encLayer hA hS t.P (drvStageOut t h y) :=
      (post_enc_rows t hA hS h hρ b hb y hy).symm
    have habs : CAbs (b + (t.P + drvDelta t)) (pv1 t (chunksOf (postBlk t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y))) := by
      apply CAbs_pv1
      rw [hflat]
      exact CAbs_encArr hb _ _ hy
    have hf1 := cArrFits_of_CAbs (w := drvWg t) habs (by unfold drvWg; omega)
    have hf2 := cArrFits_of_CAbs (w := drvWg t + 1)
      (CAbs_phase habs t.S t.K t.ρ t.D (drvPostC t) (t.D % 2)) (by unfold drvWg; omega)
    have hf3 : CArrFits t.w (pout t (chunksOf (postBlk t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y))) := by
      rw [hout]
      exact cArrFits_encLayer' hA hS hdisk hw
    have hchain := post_chain hclPar hclUn hclSc hclTr hpar hun hsc htr t _ rest hrest St hblk
      hrestT hρ hS1 hw1 hshape hM hf1 hf2 hf3 (by rw [hflat]; exact h0) h1
    rw [hout] at hchain
    have hNin : (chunksOf (postBlk t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y)).flatten.length
        ≤ 2 * t.M := by
      rw [hflat, hlen, ← hkM]
      calc postBlk t * t.A ≤ 2 * drvKeep t * t.A := Nat.mul_le_mul_right _ (postBlk_le t h hK1)
        _ = 2 * (t.A * drvKeep t) := by ring
    exact Calculus.RunsIn.iff_runs.1 (Calculus.RunsIn.mono hchain (fun _ _ => trivial)
      (hcost t _ _ hband hNin (by rw [hnb]; exact hAM)))
  · -- no-rows case
    have hlen : (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y).length =
        drvKeep t * t.A := by
      rw [encArr_length', layerAddrs_length']
      unfold drvKeep
      ring
    have hflat := chunksOf_flatten _ _ _ hlen
    have hnp : drvNpad t = 0 := by
      unfold drvNpad
      rw [if_neg hn]
    have hblk0 := chunksOf_length_mem _ _ _ hlen
    have hblk : ∀ blk ∈ chunksOf (drvKeep t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y),
        blk.length = drvKeep t + drvNpad t := by
      intro blk hb'
      rw [hnp, hblk0 blk hb', Nat.add_zero]
    have hnb := chunksOf_length (drvKeep t) t.A
      (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y)
    have hpv1 := (pv1_eq_flatten t _ hblk0).trans hflat
    have hshape : ∀ cs ∈ (chunksOf (drvKeep t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y)).flatten,
        cs.length = t.r := by
      rw [hflat]
      exact encArr_shape _ _ _
    have hM : (pv1 t (chunksOf (drvKeep t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y))).length = t.M := by
      rw [hpv1, hlen, Nat.mul_comm, hkM]
    have hout : pout t (chunksOf (drvKeep t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y)) =
        encLayer hA hS t.P (drvSmallOut t y) := by
      rw [post_enc_small t hA hS hρ b hb y hy]
      unfold pout pv2
      rw [hpv1]
      rfl
    have habs : CAbs (b + (t.P + drvDelta t)) (pv1 t (chunksOf (drvKeep t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y))) := by
      rw [hpv1]
      exact CAbs_encArr hb _ _ hy
    have hf1 := cArrFits_of_CAbs (w := drvWg t) habs (by unfold drvWg; omega)
    have hf2 := cArrFits_of_CAbs (w := drvWg t + 1)
      (CAbs_phase habs t.S t.K t.ρ t.D (drvPostC t) (t.D % 2)) (by unfold drvWg; omega)
    have hf3 : CArrFits t.w (pout t (chunksOf (drvKeep t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y))) := by
      rw [hout]
      exact cArrFits_encLayer' hA hS hdisk hw
    have hchain := post_chain hclPar hclUn hclSc hclTr hpar hun hsc htr t _ rest hrest St hblk
      hrestT hρ hS1 hw1 hshape hM hf1 hf2 hf3 (by rw [hflat]; exact h0) h1
    rw [hout] at hchain
    have hNin : (chunksOf (drvKeep t) t.A
        (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y)).flatten.length
        ≤ 2 * t.M := by
      rw [hflat, hlen, Nat.mul_comm, hkM]
      omega
    exact Calculus.RunsIn.iff_runs.1 (Calculus.RunsIn.mono hchain (fun _ _ => trivial)
      (hcost t _ _ hband hNin (by rw [hnb]; exact hAM)))

end SubNLogN.Machine.Layer
