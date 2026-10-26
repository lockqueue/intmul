/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseScanMath
import SubNLogN.Machine.K1.RotateBase

/-!
# Layer driver phase scan: layout and the adder step (`Machine/Layer/DrvPhaseScanStep.lean`)

**Scope (honest summary).** The stack layout and registers of the phase-scan kernel
(`DrvPhaseScanStmt`, `Machine/Layer/DrvPhaseDefs.lean:63`) and the exact evaluation of one step of
the bit-serial signed adder (`stepProg_eval`); no `sorry`.

## Design (whole kernel)
Named stacks: `0` the array `A` (in place), `1` the header `H` (restored). Private stacks `Scr`.
Registers: four symbol registers (`r0` is the work register of the lifted library programs).
* Setup: the header fields go to the parameter counters `pS … pW2`; `Y := 0` (`y = x / S`),
  `Rr := S - 1` (records left in the current block of `S`).
* Record loop: compute `e = (c + selCount) mod 4` by scanning the bits of `y` (`T`, `Jc` counters,
  count on `Cnt`); push the tag `e + 4·o` on `Est`; per coefficient read `a`, `b` (`w1` bits each)
  into `A2`, `B2` above a sign guard, run `w2` adder steps (`stepProg`) emitting `re'` to `U` and
  `im'` to `I`, then move `I` to `U` through `I2`; move the record end to `U`; update `Y`, `Rr`.
* End: rewind `U` (the outputs, reversed) onto `A`; drop the counters.

## The adder step (`stepProg`)
Registers after the reads: `r1` = tag `e + 4·o` (on `Est`), `r2` = carry tag (on `Cr`: carries
`(cR, cI) ∈ [-2,1]²` coded in `Fin 16`), `r3` = top of `A2`, `r0` = top of `B2`. The step pops
`A2`/`B2` only if their top is a bit (else it reads the sign guard: sign extension), pushes the
output bits `re'`, `im'` onto `U`, `I`, and replaces the carry tag.
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine Computability

/-! ## Layout -/

/-- Private stacks of the phase-scan kernel (named below). -/
abbrev Scr : Type := Fin 25

/-- Stacks of the kernel. -/
abbrev PL : Type := KLoc (Fin 2) Scr

/-- Registers of the kernel: four symbol registers. -/
abbrev PReg : Type := Option Sym × Option Sym × Option Sym × Option Sym

/-- Lens onto the work register `r0`. -/
def pl : Lens PReg (Option Sym) := Lens.fst _ _

/-- A library program on the work register. -/
abbrev wk (p : SProg PL) : Prog PL (fun _ => Sym) PReg := p.liftRegs pl

/-- The array (named `0`). -/
abbrev sA : PL := .inl 0
/-- The header (named `1`). -/
abbrev sH : PL := .inl 1
/-- Private: output staging (reversed outputs). -/
abbrev kU : PL := .inr 0
/-- Private: parameter `S`. -/
abbrev kPS : PL := .inr 1
/-- Private: parameter `K`. -/
abbrev kPK : PL := .inr 2
/-- Private: parameter `ρ`. -/
abbrev kPR : PL := .inr 3
/-- Private: parameter `D`. -/
abbrev kPD : PL := .inr 4
/-- Private: parameter `c`. -/
abbrev kPC : PL := .inr 5
/-- Private: parameter `o`. -/
abbrev kPO : PL := .inr 6
/-- Private: parameter `w1`. -/
abbrev kPW1 : PL := .inr 7
/-- Private: parameter `w2`. -/
abbrev kPW2 : PL := .inr 8
/-- Private: counter `y = x / S`. -/
abbrev kY : PL := .inr 9
/-- Private: records left in the current block of `S`. -/
abbrev kRr : PL := .inr 10
/-- Private: header stash. -/
abbrev kHs : PL := .inr 11
/-- Private: temporary of library programs. -/
abbrev kTm : PL := .inr 12
/-- Private: tag `e + 4·o` of the current record. -/
abbrev kEst : PL := .inr 13
/-- Private: scan: positions to the next selected one. -/
abbrev kT : PL := .inr 14
/-- Private: scan: selected positions left. -/
abbrev kJc : PL := .inr 15
/-- Private: scan: count mod 4. -/
abbrev kCnt : PL := .inr 16
/-- Private: scan: bits of `y` already read. -/
abbrev kY2 : PL := .inr 17
/-- Private: loop counter. -/
abbrev kKc : PL := .inr 18
/-- Private: field buffer. -/
abbrev kAb : PL := .inr 19
/-- Private: first operand (LSB on top, sign guard below). -/
abbrev kA2 : PL := .inr 20
/-- Private: second operand. -/
abbrev kB2 : PL := .inr 21
/-- Private: imaginary output buffer. -/
abbrev kI : PL := .inr 22
/-- Private: second imaginary buffer. -/
abbrev kI2 : PL := .inr 23
/-- Private: carry tag. -/
abbrev kCr : PL := .inr 24

/-! ## Register views of the adder step -/

/-- Value of a tag symbol (`0` otherwise). -/
def tagN : Option Sym → ℕ
  | some (.tag t) => t.val
  | _ => 0

/-- A bit read with sign extension: a bit, or the sign guard (`neg` reads `1`). -/
def symBit : Option Sym → Bool
  | some (.bit b) => b
  | some .neg => true
  | _ => false

/-- The sign guard of a field whose most significant bit is in the register. -/
def sgSym (o : Option Sym) : Sym := if o = some (.bit true) then .neg else .pos

/-- Code of a carry pair in `[-2, 1]²`. -/
def encC (a b : ℤ) : Fin 16 :=
  ⟨((a + 2).toNat + 4 * (b + 2).toNat) % 16, Nat.mod_lt _ (by norm_num)⟩

/-- The real-part carry of a code. -/
def cReOf (t : ℕ) : ℤ := ((t % 4 : ℕ) : ℤ) - 2

/-- The imaginary-part carry of a code. -/
def cImOf (t : ℕ) : ℤ := ((t / 4 % 4 : ℕ) : ℤ) - 2

theorem cReOf_encC {a b : ℤ} (ha : -2 ≤ a ∧ a ≤ 1) (hb : -2 ≤ b ∧ b ≤ 1) :
    cReOf (encC a b).val = a := by
  unfold cReOf encC
  simp only
  omega

theorem cImOf_encC {a b : ℤ} (ha : -2 ≤ a ∧ a ≤ 1) (hb : -2 ≤ b ∧ b ≤ 1) :
    cImOf (encC a b).val = b := by
  unfold cImOf encC
  simp only
  omega

/-- The exponent `e` of the tag `e + 4·o`. -/
def vE (v : PReg) : ℕ := tagN v.2.1 % 4

/-- The flag `o` of the tag `e + 4·o`. -/
def vO (v : PReg) : Bool := decide (tagN v.2.1 / 4 % 2 = 1)

/-- The column sum of the real part. -/
def vSR (v : PReg) : ℤ :=
  sstep (kRe (vE v) (vO v)).1 (kRe (vE v) (vO v)).2 (cReOf (tagN v.2.2.1)) (symBit v.2.2.2)
    (symBit v.1)

/-- The column sum of the imaginary part. -/
def vSI (v : PReg) : ℤ :=
  sstep (kIm (vE v) (vO v)).1 (kIm (vE v) (vO v)).2 (cImOf (tagN v.2.2.1)) (symBit v.2.2.2)
    (symBit v.1)

/-! ## The step program -/

/-- Read with sign extension: peek `k` into a register (via `f`), pop it only if it is a bit. -/
def rdExt (k : PL) (f : PReg → Option Sym → PReg) (g : PReg → Option Sym) :
    Prog PL (fun _ => Sym) PReg :=
  .seq (.peek k f) (.ite (fun v => optIsBit (g v)) (.pop k fun v _ => v) skip)

/-- The stack after a read with sign extension. -/
def rdSt (L : List Sym) : List Sym := if optIsBit L.head? then L.tail else L

/-- **One adder step.** -/
def stepProg : Prog PL (fun _ => Sym) PReg :=
  .seq (.peek kEst fun v o => (v.1, o, v.2.2))
  (.seq (.peek kCr fun v o => (v.1, v.2.1, o, v.2.2.2))
  (.seq (rdExt kA2 (fun v o => (v.1, v.2.1, v.2.2.1, o)) fun v => v.2.2.2)
  (.seq (rdExt kB2 (fun v o => (o, v.2)) fun v => v.1)
  (.seq (.push kU fun v => .bit (decide (vSR v % 2 = 1)))
  (.seq (.push kI fun v => .bit (decide (vSI v % 2 = 1)))
  (.seq (.pop kCr fun v _ => v)
    (.push kCr fun v => .tag (encC (vSR v / 2) (vSI v / 2)))))))))

theorem closed_stepProg : stepProg.Closed := by
  simp [stepProg, rdExt, skip, Prog.Closed, Prog.FreeBelow]

theorem rdExt_eval (k : PL) (f : PReg → Option Sym → PReg) (g : PReg → Option Sym)
    (hg : ∀ v o, g (f v o) = o) (v : PReg) (S : PL → List Sym) :
    Eval [] (rdExt k f g) ⟨v, S⟩ ⟨f v (S k).head?, Function.update S k (rdSt (S k))⟩ 3 := by
  have e1 := Eval.peek [] k f v S
  by_cases hb : optIsBit (S k).head? = true
  · have e2 : Eval [] (.ite (fun v => optIsBit (g v)) (.pop k fun v _ => v) skip)
        ⟨f v (S k).head?, S⟩ ⟨f v (S k).head?, Function.update S k (rdSt (S k))⟩ 2 := by
      have ep := Eval.pop [] k (fun v _ => v) (f v (S k).head?) S
      refine (Eval.ite_true (by simp only [hg]; exact hb) ep).of_eq ?_ rfl
      simp only [rdSt, hb, if_true]
    exact (Eval.seq e1 e2).of_eq rfl rfl
  · have hb' : optIsBit (S k).head? = false := by simpa using hb
    have e2 : Eval [] (.ite (fun v => optIsBit (g v)) (.pop k fun v _ => v) skip)
        ⟨f v (S k).head?, S⟩ ⟨f v (S k).head?, Function.update S k (rdSt (S k))⟩ 2 := by
      have es := skip_eval (K := PL) [] (⟨f v (S k).head?, S⟩ : St PL (fun _ => Sym) PReg)
      refine (Eval.ite_false (by simp only [hg]; exact hb') es).of_eq ?_ rfl
      simp only [rdSt, hb', Bool.false_eq_true, if_false, Function.update_eq_self]
    exact (Eval.seq e1 e2).of_eq rfl rfl

/-- The registers after the reads of a step. -/
def stepRegs (S : PL → List Sym) : PReg :=
  ((S kB2).head?, (S kEst).head?, (S kCr).head?, (S kA2).head?)

/-- The stacks after a step. -/
def stepSt (S : PL → List Sym) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    kA2 (rdSt (S kA2))) kB2 (rdSt (S kB2)))
    kU (.bit (decide (vSR (stepRegs S) % 2 = 1)) :: S kU))
    kI (.bit (decide (vSI (stepRegs S) % 2 = 1)) :: S kI))
    kCr (.tag (encC (vSR (stepRegs S) / 2) (vSI (stepRegs S) / 2)) :: (S kCr).tail)

/-- **One adder step, exact.** -/
theorem stepProg_eval (v : PReg) (S : PL → List Sym) :
    Eval [] stepProg ⟨v, S⟩ ⟨stepRegs S, stepSt S⟩ 12 := by
  have hBA : (kB2 : PL) ≠ kA2 := by simp
  have e1 := Eval.peek [] kEst (fun (v : PReg) o => (v.1, o, v.2.2)) v S
  have e2 := Eval.peek [] kCr (fun (v : PReg) o => (v.1, v.2.1, o, v.2.2.2))
    (v.1, (S kEst).head?, v.2.2) S
  have e3 := rdExt_eval kA2 (fun v o => (v.1, v.2.1, v.2.2.1, o)) (fun v => v.2.2.2)
    (fun _ _ => rfl) (v.1, (S kEst).head?, (S kCr).head?, v.2.2.2) S
  have h1B : Function.update S kA2 (rdSt (S kA2)) kB2 = S kB2 :=
    Function.update_of_ne hBA _ _
  have e4 := rdExt_eval kB2 (fun v o => (o, v.2)) (fun v => v.1) (fun _ _ => rfl)
    (v.1, (S kEst).head?, (S kCr).head?, (S kA2).head?)
    (Function.update S kA2 (rdSt (S kA2)))
  rw [h1B] at e4
  have e5 := Eval.push [] kU (fun v : PReg => Sym.bit (decide (vSR v % 2 = 1)))
    (stepRegs S) (Function.update (Function.update S kA2 (rdSt (S kA2))) kB2
      (rdSt (S kB2)))
  have e6 := Eval.push [] kI (fun v : PReg => Sym.bit (decide (vSI v % 2 = 1)))
    (stepRegs S) (Function.update (Function.update (Function.update S kA2
      (rdSt (S kA2))) kB2 (rdSt (S kB2))) kU
      (Sym.bit (decide (vSR (stepRegs S) % 2 = 1)) :: Function.update (Function.update S kA2
        (rdSt (S kA2))) kB2 (rdSt (S kB2)) kU))
  set S4 := Function.update (Function.update (Function.update (Function.update S kA2
      (rdSt (S kA2))) kB2 (rdSt (S kB2))) kU
      (Sym.bit (decide (vSR (stepRegs S) % 2 = 1)) :: Function.update (Function.update S kA2
        (rdSt (S kA2))) kB2 (rdSt (S kB2)) kU)) kI
      (Sym.bit (decide (vSI (stepRegs S) % 2 = 1)) :: Function.update (Function.update
        (Function.update S kA2 (rdSt (S kA2))) kB2 (rdSt (S kB2))) kU
        (Sym.bit (decide (vSR (stepRegs S) % 2 = 1)) :: Function.update (Function.update S
          kA2 (rdSt (S kA2))) kB2 (rdSt (S kB2)) kU) kI) with hS4
  have e7 := Eval.pop [] kCr (fun (v : PReg) _ => v) (stepRegs S) S4
  have e8 := Eval.push [] kCr
    (fun v : PReg => Sym.tag (encC (vSR v / 2) (vSI v / 2))) (stepRegs S)
    (Function.update S4 kCr (S4 kCr).tail)
  have hall := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 e8))))))
  refine hall.of_eq ?_ rfl
  have hC : S4 kCr = S kCr := by
    rw [hS4]; simp [Function.update_apply]
  congr 1
  rw [Function.update_idem, hC]
  funext k
  simp only [stepSt, hS4, Function.update_apply]
  split_ifs <;> simp_all

theorem runs_stepProg (S : PL → List Sym) : Runs stepProg S (stepSt S) (fun _ => True) 12 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 12, stepProg_eval v stk, ⟨rfl, trivial⟩, le_rfl⟩

/-! ## Reading the register views -/

/-- The tag `e + 4·o` of a record. -/
def eoTag (e : ℕ) (o : Bool) : Fin 16 := ⟨e % 4 + 4 * o.toNat, by cases o <;> simp <;> omega⟩

theorem vE_eoTag (e : ℕ) (o : Bool) (a c b : Option Sym) :
    vE (b, some (.tag (eoTag e o)), c, a) = e % 4 := by
  cases o <;> simp [vE, tagN, eoTag] <;> omega

theorem vO_eoTag (e : ℕ) (o : Bool) (a c b : Option Sym) :
    vO (b, some (.tag (eoTag e o)), c, a) = o := by
  have h4 : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  cases o <;> simp [vO, tagN, eoTag] <;> omega

theorem vSR_eq (e : ℕ) (o : Bool) (cR cI : ℤ) (hR : -2 ≤ cR ∧ cR ≤ 1) (hI : -2 ≤ cI ∧ cI ≤ 1)
    (a b : Option Sym) :
    vSR (b, some (.tag (eoTag e o)), some (.tag (encC cR cI)), a) =
      sstep (kRe e o).1 (kRe e o).2 cR (symBit a) (symBit b) := by
  have hk : kRe (e % 4) o = kRe e o := by simp [kRe, Nat.mod_mod]
  simp only [vSR, vE_eoTag, vO_eoTag, hk]
  congr 1
  exact cReOf_encC hR hI

theorem vSI_eq (e : ℕ) (o : Bool) (cR cI : ℤ) (hR : -2 ≤ cR ∧ cR ≤ 1) (hI : -2 ≤ cI ∧ cI ≤ 1)
    (a b : Option Sym) :
    vSI (b, some (.tag (eoTag e o)), some (.tag (encC cR cI)), a) =
      sstep (kIm e o).1 (kIm e o).2 cI (symBit a) (symBit b) := by
  have hk : kIm (e % 4) o = kIm e o := by simp [kIm, Nat.mod_mod]
  simp only [vSI, vE_eoTag, vO_eoTag, hk]
  congr 1
  exact cImOf_encC hR hI

end SubNLogN.Machine.Layer.DrvPhaseScanAux
