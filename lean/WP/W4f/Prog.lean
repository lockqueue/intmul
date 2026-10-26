import WP.W4f.Math
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W4f.Prog — the bitwise Hensel-lift program and its atoms

Stacks (generic `K`): `kK` = `k`, `kU` = `u2` (both restored), `kD` = destination; scratch `kS`
(residual `s`, LSB on top), `kT` (counter, then sum bits), `kV` (saved bits of `u2`, Lib temp),
`kY` (output bits, MSB on top). Every scratch stack gets a `mark` first, popped at the end.
Registers `Reg = Option Sym × Bool × Bool`: symbol slot, saved residual bit `a`, carry `c`.

* `k = 0`: push `1`.
* `k ≥ 1`: `s := 1^k` (unary expansion of a copy of `k` with Lib `dec`); while `s ≠ []`: pop its
  LSB `x`, push `x` on `kY`, and if `x = 1` set `s := (s + u2) mod 2^|s|` in place (`addPhase`,
  reading only the low `|s|` bits of `u2`); finally drop the high zeros of `kY`, move it onto `kD`.
-/

namespace WP.W4f

open TMFw TMFw.Lib TMFw.Contracts

/-- Registers: symbol slot, saved residual bit, carry. -/
abbrev Reg := Option Sym × Bool × Bool

/-- Programs over stacks `K`, alphabet `Sym`, registers `Reg`. -/
abbrev RProg (K : Type) := Prog K (fun _ => Sym) Reg

/-- States. -/
abbrev RSt (K : Type) := St K (fun _ => Sym) Reg

section Programs

variable {K : Type}

/-- Peek `k` into the symbol slot. -/
def pk (k : K) : RProg K := .peek k (fun v o => (o, v.2))
/-- Pop `k` into the symbol slot. -/
def pp (k : K) : RProg K := .pop k (fun v o => (o, v.2))
/-- Pop `k`, discarding the symbol. -/
def pd (k : K) : RProg K := .pop k (fun v _ => v)
/-- Push a constant onto `k`. -/
def pc (k : K) (x : Sym) : RProg K := .push k (fun _ => x)
/-- Push the symbol slot onto `k` (default `sep`). -/
def pr (k : K) : RProg K := .push k (fun v => v.1.getD .sep)
/-- Run a seed-library routine (`SProg`) on the symbol slot. -/
def lift (p : SProg K) : RProg K := p.liftRegs (Lens.fst (Option Sym) (Bool × Bool))
/-- Is the symbol slot a bit? -/
def symBit (v : Reg) : Bool := optIsBit v.1
/-- Pop the residual's bit into `a`. -/
def popA (kS : K) : RProg K := .pop kS (fun v o => (v.1, optBit o, v.2.2))
/-- Push the sum bit of `a`, the slot's bit and `c` onto `kT`. -/
def pushSum (kT : K) : RProg K := .push kT (fun v => .bit (xor3 v.2.1 (optBit v.1) v.2.2))
/-- Update the carry. -/
def setC : RProg K := .load (fun v => (v.1, v.2.1, maj3 v.2.1 (optBit v.1) v.2.2))
/-- Clear the carry. -/
def clrC : RProg K := .load (fun v => (v.1, v.2.1, false))
/-- Read the next bit of `u2` into the slot (a non-bit reads as `0`); a bit is saved on `kV`. -/
def readU (kU kV : K) : RProg K := .seq (pk kU) (.ite symBit (.seq (pp kU) (pr kV)) skip)
/-- One step of `s += u2`: pop `s`'s bit, read `u2`'s bit, push the sum bit on `kT`. -/
def addBody (kS kU kV kT : K) : RProg K :=
  .seq (popA kS) (.seq (readU kU kV) (.seq (pushSum kT) (.seq setC (pk kS))))
/-- The addition loop (runs while `kS` shows a bit). -/
def addLoop (kS kU kV kT : K) : RProg K := .loop symBit (addBody kS kU kV kT)
/-- `s := (s + u2) mod 2^|s|` in place; the sum bits and the read bits of `u2` are moved back. -/
def addPhase (kS kU kV kT : K) : RProg K :=
  .seq clrC (.seq (pk kS) (.seq (addLoop kS kU kV kT)
    (.seq (lift (moveBlock kT kS)) (lift (moveBlock kV kU)))))
/-- One lifting step: pop the residual's LSB `x`, push it on `kY`; if `x = 1`, add `u2`. -/
def mainBody (kS kU kV kT kY : K) : RProg K :=
  .seq (pp kS) (.seq (pr kY)
    (.seq (.ite (fun v => optBit v.1) (addPhase kS kU kV kT) skip) (pk kS)))
/-- The lifting loop (runs while `kS` shows a bit). -/
def mainLoop (kS kU kV kT kY : K) : RProg K := .loop symBit (mainBody kS kU kV kT kY)
/-- Unary expansion step: decrement the counter on `kT`, push a `1` on `kS`. -/
def initBody (kS kT kV : K) : RProg K :=
  .seq (lift (dec kT kV)) (.seq (pc kS (.bit true)) (pk kT))
/-- Unary expansion loop. -/
def initLoop (kS kT kV : K) : RProg K := .loop symBit (initBody kS kT kV)
/-- Drop the leading (high) zeros of the MSB-first block on `kY`. -/
def dropLoop (kY : K) : RProg K := .loop (fun v => isBitR false v.1) (.seq (pd kY) (pk kY))
/-- Marks on the scratch stacks, copy of `k` onto `kT`. -/
def setup (kK kS kT kV kY : K) : RProg K :=
  .seq (pc kS .mark) (.seq (pc kY .mark) (.seq (pc kT .mark) (.seq (pc kV .mark)
    (.seq (lift (copyBlock kK kT kV)) (pk kT)))))
/-- Remove the marks, normalize the output and move it onto `kD`. -/
def cleanup (kD kS kT kV kY : K) : RProg K :=
  .seq (pd kS) (.seq (pd kT) (.seq (pd kV) (.seq (pk kY) (.seq (dropLoop kY)
    (lift (moveBits kY kD))))))
/-- The lift for `k ≥ 1`. -/
def algo (kK kU kD kS kT kV kY : K) : RProg K :=
  .seq (setup kK kS kT kV kY) (.seq (initLoop kS kT kV) (.seq (pk kS)
    (.seq (mainLoop kS kU kV kT kY) (cleanup kD kS kT kV kY))))
/-- The whole program (generic stacks): `k = 0 ↦ 1`, else the lift. -/
def oddProgG (kK kU kD kS kT kV kY : K) : RProg K :=
  .seq (pk kK) (.ite symBit (algo kK kU kD kS kT kV kY) (pc kD (.bit true)))

theorem oddProgG_closed (kK kU kD kS kT kV kY : K) : (oddProgG kK kU kD kS kT kV kY).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, oddProgG, algo, setup, cleanup, initLoop, initBody, mainLoop,
    mainBody, addPhase, addLoop, addBody, readU, dropLoop, pk, pp, pd, pc, pr, popA, pushSum, setC,
    clrC, skip, lift, Prog.liftRegs, moveBlock, moveBits, moveBitsBody, restoreR, copyBlock,
    moveBitsDup, dupBody, dec, decFix, scanLoop, scanBody, pushC, popR, pushR, peekR]

end Programs

/-! ## Atoms -/

section Atoms

variable {K : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem st_eq {v v' : Reg} {S S' : K → List Sym} (hv : v = v') (hS : S = S') :
    (⟨v, S⟩ : RSt K) = ⟨v', S'⟩ := by
  subst hv
  subst hS
  rfl

theorem pk_eval (k : K) (v : Reg) (S : K → List Sym) (l : List Sym) (h : S k = l) :
    Eval [] (pk k) ⟨v, S⟩ ⟨(l.head?, v.2), S⟩ 1 := by
  refine (Eval.peek [] k _ v S).of_eq ?_ rfl
  rw [h]

theorem pp_eval (k : K) (v : Reg) (S : K → List Sym) (x : Sym) (l : List Sym)
    (h : S k = x :: l) : Eval [] (pp k) ⟨v, S⟩ ⟨(some x, v.2), Function.update S k l⟩ 1 := by
  refine (Eval.pop [] k _ v S).of_eq ?_ rfl
  rw [h]
  rfl

theorem pd_eval (k : K) (v : Reg) (S : K → List Sym) (x : Sym) (l : List Sym)
    (h : S k = x :: l) : Eval [] (pd k) ⟨v, S⟩ ⟨v, Function.update S k l⟩ 1 := by
  refine (Eval.pop [] k _ v S).of_eq ?_ rfl
  rw [h]
  rfl

theorem pc_eval (k : K) (x : Sym) (v : Reg) (S : K → List Sym) :
    Eval [] (pc k x) ⟨v, S⟩ ⟨v, Function.update S k (x :: S k)⟩ 1 :=
  Eval.push [] k _ v S

theorem pr_eval (k : K) (x : Sym) (w : Bool × Bool) (S : K → List Sym) :
    Eval [] (pr k) ⟨(some x, w), S⟩ ⟨(some x, w), Function.update S k (x :: S k)⟩ 1 :=
  Eval.push [] k _ _ S

theorem popA_eval (kS : K) (o : Option Sym) (a c b : Bool) (S : K → List Sym) (l : List Sym)
    (h : S kS = Sym.bit b :: l) :
    Eval [] (popA kS) ⟨(o, a, c), S⟩ ⟨(o, b, c), Function.update S kS l⟩ 1 := by
  refine (Eval.pop [] kS _ _ S).of_eq ?_ rfl
  rw [h]
  rfl

theorem pushSum_eval (kT : K) (o : Option Sym) (a c : Bool) (S : K → List Sym) :
    Eval [] (pushSum kT) ⟨(o, a, c), S⟩
      ⟨(o, a, c), Function.update S kT (Sym.bit (xor3 a (optBit o) c) :: S kT)⟩ 1 :=
  Eval.push [] kT _ _ S

theorem setC_eval (o : Option Sym) (a c : Bool) (S : K → List Sym) :
    Eval [] (setC (K := K)) ⟨(o, a, c), S⟩ ⟨(o, a, maj3 a (optBit o) c), S⟩ 1 :=
  Eval.load [] _ _ S

theorem clrC_eval (o : Option Sym) (a c : Bool) (S : K → List Sym) :
    Eval [] (clrC (K := K)) ⟨(o, a, c), S⟩ ⟨(o, a, false), S⟩ 1 :=
  Eval.load [] _ _ S

theorem lift_eval {p : SProg K} {S S' : K → List Sym} {r r' : Option Sym} {t : ℕ}
    (h : Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t) (v : Reg) (hv : v.1 = r) :
    Eval [] (lift p) ⟨v, S⟩ ⟨(r', v.2), S'⟩ t :=
  Eval.liftRegs (Lens.fst _ _) h v hv

theorem optBit_head?_of_termOK {rest : List Sym} (h : TermOK rest) :
    optBit rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    have := h d rfl
    cases d <;> simp_all [optBit]

theorem symBit_termOK {rest : List Sym} (h : TermOK rest) (w : Bool × Bool) :
    symBit (rest.head?, w) = false :=
  optIsBit_head?_of_termOK h

theorem optBit_headU {r1 : List Sym} (hr1 : TermOK r1) (u : List Bool) :
    optBit (u.map Sym.bit ++ r1).head? = u.headD false := by
  cases u with
  | nil => exact optBit_head?_of_termOK hr1
  | cons x u' => rfl

end Atoms

#assert_std_axioms oddProgG_closed st_eq pk_eval pp_eval pd_eval pc_eval pr_eval popA_eval
  pushSum_eval setC_eval clrC_eval lift_eval optBit_head?_of_termOK symBit_termOK optBit_headU

end WP.W4f
