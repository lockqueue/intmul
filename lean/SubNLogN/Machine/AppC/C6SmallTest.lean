/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6QLeaves
import SubNLogN.Machine.AppC.C7TopArith
import SubNLogN.Machine.K1.DigitBuild
import IntMulTM.Framework.Lib.CompareEval

/-!
# Lemma A.8 small-width test (`Machine/AppC/C6SmallTest.lean`)

Lemma A.8 (`lem:transfer12`, Appendix A.3;
small-width branch `e ≤ 34`): the radix-`q` interchange branches on `e ≤ 34`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Proved here (0 `sorry`, no pending hypotheses):** `c6SmallTest_holds : C6SmallTestStmt`
(statement in `Machine/AppC/C6QLeaves.lean`). The kernel pushes the constant `34` (above a guard)
on a private stack, compares it with the counter `e` by the library routine `cmpNum` (result in
the compare register), and drops the constant. The observation is `ordOf e 34 ≠ gt`, which is
`decide (e ≤ 34)`. Cost `≤ 110 · (|e| + 1)` (in fact at most `108` steps).
-/

namespace SubNLogN.Machine.AppC.C6SmallAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine Computability

/-- Stacks of the test: named `0` = the counter `e`; private `0` = the constant, `1`, `2` the
temporaries of `cmpNum`. -/
abbrev TT := KLoc (Fin 1) (Fin 3)

def tE : TT := .inl 0
def tP : TT := .inr 0
def tA : TT := .inr 1
def tB : TT := .inr 2

/-- Push a guard `mark`, then the bits of `34` (MSB first, so that the LSB ends on top). -/
def push34 : SProg TT :=
  .seq (pushC tP .mark) (.seq (pushC tP (.bit true)) (.seq (pushC tP (.bit false))
    (.seq (pushC tP (.bit false)) (.seq (pushC tP (.bit false)) (.seq (pushC tP (.bit true))
      (pushC tP (.bit false)))))))

/-- **The test kernel**: push `34`, compare, drop `34`. -/
def testProg : Prog TT (fun _ => Sym) (Option Sym × CReg) :=
  .seq (push34.liftRegs (Lens.fst _ _)) (.seq ((cmpNum tE tP tA tB).liftRegs (Lens.snd _ _))
    ((C7TopAux.dropTo tP .mark).liftRegs (Lens.fst _ _)))

/-- The observation: the comparison result is not `gt`. -/
def testObs (r : Option Sym × CReg) : Bool := r.2.2.2 != .gt

theorem natSyms_34 : natSyms 34 =
    [Sym.bit false, Sym.bit true, Sym.bit false, Sym.bit false, Sym.bit false, Sym.bit true] := by
  decide

theorem push34_runs (S : TT → List Sym) :
    Runs push34 S (Function.update S tP (natSyms 34 ++ Sym.mark :: S tP)) (fun _ => True) 7 := by
  have h := WP.W9comp.runs_seq (C7TopAux.pushC_runs tP Sym.mark S)
    (WP.W9comp.runs_seq (C7TopAux.pushC_runs tP (Sym.bit true) _)
    (WP.W9comp.runs_seq (C7TopAux.pushC_runs tP (Sym.bit false) _)
    (WP.W9comp.runs_seq (C7TopAux.pushC_runs tP (Sym.bit false) _)
    (WP.W9comp.runs_seq (C7TopAux.pushC_runs tP (Sym.bit false) _)
    (WP.W9comp.runs_seq (C7TopAux.pushC_runs tP (Sym.bit true) _)
      (C7TopAux.pushC_runs tP (Sym.bit false) _))))))
  refine WP.W9comp.runs_congr h ?_
  rw [natSyms_34]
  simp only [Function.update_idem, Function.update_self]
  rfl

theorem ordOf_ne_gt (a b : ℕ) : (ordOf a b != .gt) = decide (a ≤ b) := by
  unfold ordOf
  by_cases h1 : a < b
  · simp [h1, Nat.le_of_lt h1]
  · by_cases h2 : a = b
    · subst h2; simp
    · have h3 : ¬ a ≤ b := by omega
      simp [h1, h2, h3]

theorem testProg_runs (e : ℕ) (r1 : List Sym) (S : TT → List Sym) (hr1 : TermOK r1)
    (hS : S tE = natSyms e ++ r1) :
    Runs testProg S S (fun r => testObs r = decide (e ≤ 34)) 108 := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨x1, c1, hc1, e1⟩ := C7TopAux.runs_toEval (push34_runs S) v.1
  have e1' := Eval.liftRegs (Lens.fst (Option Sym) CReg) e1 v rfl
  have hA : Function.update S tP (natSyms 34 ++ Sym.mark :: S tP) tE =
      (encodeNat e).map Sym.bit ++ r1 := by
    rw [Function.update_of_ne (show tE ≠ tP by decide)]; exact hS
  have hB : Function.update S tP (natSyms 34 ++ Sym.mark :: S tP) tP =
      (encodeNat 34).map Sym.bit ++ (Sym.mark :: S tP) := by
    rw [Function.update_self]; rfl
  have e2 := cmpNum_eval (k₁ := tE) (k₂ := tP) (t₁ := tA) (t₂ := tB) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) v.2 (encodeNat e) (encodeNat 34) r1
    (Sym.mark :: S tP) _ hr1 (TermOK.cons rfl _) hA hB
  have e2' := Eval.liftRegs (Lens.snd (Option Sym) CReg) e2 (x1, v.2) rfl
  have r3 := C7TopAux.dropTo_runs tP Sym.mark (natSyms 34) (S tP)
    (Function.update S tP (natSyms 34 ++ Sym.mark :: S tP)) (by rw [natSyms_34]; decide)
    (Function.update_self _ _ _)
  rw [Function.update_idem, Function.update_eq_self] at r3
  obtain ⟨x3, c3, hc3, e3⟩ := C7TopAux.runs_toEval r3 x1
  have e3' := Eval.liftRegs (Lens.fst (Option Sym) CReg) e3
    (x1, (some Sym.mark, some Sym.mark, cmpAll .eq (encodeNat e) (encodeNat 34))) rfl
  refine ⟨_, _, Eval.seq e1' (Eval.seq e2' e3'), ?_, ?_⟩
  · show (cmpAll .eq (encodeNat e) (encodeNat 34) != Ordering.gt) = decide (e ≤ 34)
    rw [K1Digit.cmpAll_encodeNat, ordOf_ne_gt]
  · have h6 : (encodeNat 34).length = 6 := by decide
    have h6' : (natSyms 34).length = 6 := by rw [natSyms_34]; rfl
    have hmin : min (encodeNat e).length (encodeNat 34).length ≤ 6 := by omega
    rw [h6'] at hc3
    omega

theorem push34_closed : push34.Closed := by
  simp [push34, pushC, Prog.Closed, Prog.FreeBelow]

theorem testProg_closed : testProg.Closed :=
  ⟨WP.W9comp.closed_liftRegs _ push34_closed,
    WP.W9comp.closed_liftRegs _ (by
      simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs, cmpNum, cmpBody,
        restoreR, moveBits, moveBitsBody, popR, pushR, pushC, skip]),
    WP.W9comp.closed_liftRegs _ (C7TopAux.dropTo_closed _ _)⟩

end SubNLogN.Machine.AppC.C6SmallAux

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts AppC.C6SmallAux

/-- **[PROVED] Lemma A.8 small-width test** (`c6SmallTest_holds`, 0 `sorry`;
Lemma A.8 (`lem:transfer12`)): the kernel `testProg` (private stacks
`Fin 3`, registers `Option Sym × CReg`) restores all stacks and leaves `testObs r = decide (e ≤ 34)`
in its register, within `110 · (bitLen e + 1)` steps. -/
theorem c6SmallTest_holds : C6SmallTestStmt := by
  refine ⟨110, fun _ => ⟨Fin 3, inferInstance, inferInstance, Option Sym × CReg, testProg,
    inferInstance, ⟨(none, none, none, .eq)⟩, testProg_closed, testObs, ?_⟩⟩
  intro e r1 S hr1 hS
  exact WP.W9comp.runs_mono (testProg_runs e r1 S hr1 hS) (fun _ h => h) (by omega)

end SubNLogN.Machine
