import WP.W9d.Basic
import WP.W7k2.Ops
import WP.W9dR.Contract
import Contracts.W9.Pre

/-!
# WP.W9d.Inst — instances, host stacks and call rules of the twist kernel

* `WP.W9dR.W9d_roundShift` (WP W9dR): the signed round-shift subroutine
  `z += intSyms (divRoundPow2 v s)`, a mini machine contract.
* `Spec*`: the bodies of the contracts the kernel calls, for one extracted instance (`exists_inst`
  produces them by definitional unfolding).
* `TwInst`: the instances; `TwInst.Reg` the kernel registers (one component per instance plus a
  symbol register); `TwInst.Spec J Mul D`: all instances meet their bodies with ONE constant `D`.
* Host stacks `TwL = Loc 4 10`: named `W0, TR, TL, C0` (mapped to layout B), scratch
  `E, P1..P4, RE, IM, R2, O, K`.
* Call rules `HT.mulI`, `HT.addI`, `HT.subI`, `HT.rndI`, `HT.incI` on the host.
-/

namespace WP.W9d

open TMFw TMFw.Contracts WP.W7k2 Computability TMFw.Lib

/-! ## Instance bodies -/

/-- Body of `W5_mulAt Mul`. -/
def SpecMul (Mul : ℕ → ℕ) (I : Inst 3 8 Unit) (C : ℕ) : Prop :=
  ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym),
    bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
    S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
      (C * Mul w + C)

/-- Body of `W3_addInt`. -/
def SpecAddInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W3_subInt`. -/
def SpecSubInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `WP.W9dR.W9d_roundShift`. -/
def SpecRnd (I : Inst 3 6 Unit) (C : ℕ) : Prop :=
  ∀ (v : ℤ) (s : ℕ) (rx rc : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = intSyms v ++ rx → S (.inl 1) = natSyms s ++ rc →
    Runs I.P S (Function.update S (.inl 2) (intSyms (IntMul.divRoundPow2 v s) ++ S (.inl 2)))
      (fun _ => True) (C * (bitLen v.natAbs + s + 1))

/-- Body of `W3_incNat`. -/
def SpecInc (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (encodeNat a) + 1))

/-! ## Monotonicity in the constant -/

theorem SpecMul.mono {Mul : ℕ → ℕ} {I : Inst 3 8 Unit} {C D : ℕ} (h : SpecMul Mul I C)
    (hCD : C ≤ D) : SpecMul Mul I D := fun w a b ra rb S h1 h2 h3 h4 h5 h6 =>
  Triple.cost_mono (h w a b ra rb S h1 h2 h3 h4 h5 h6)
    (Nat.add_le_add (Nat.mul_le_mul_right _ hCD) hCD)

theorem SpecAddInt.mono {I : Inst 3 4 Unit} {C D : ℕ} (h : SpecAddInt I C) (hCD : C ≤ D) :
    SpecAddInt I D := fun a b rx ry S h1 h2 h3 h4 =>
  Triple.cost_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hCD)

theorem SpecSubInt.mono {I : Inst 3 4 Unit} {C D : ℕ} (h : SpecSubInt I C) (hCD : C ≤ D) :
    SpecSubInt I D := fun a b rx ry S h1 h2 h3 h4 =>
  Triple.cost_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hCD)

theorem SpecRnd.mono {I : Inst 3 6 Unit} {C D : ℕ} (h : SpecRnd I C) (hCD : C ≤ D) :
    SpecRnd I D := fun v s rx rc S h1 h2 h3 h4 =>
  Triple.cost_mono (h v s rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hCD)

theorem SpecInc.mono {I : Inst 1 4 Unit} {C D : ℕ} (h : SpecInc I C) (hCD : C ≤ D) :
    SpecInc I D := fun a rx S h1 h2 =>
  Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hCD)

theorem SpecCopy.mono {I : Inst 2 4 Unit} {C D : ℕ} (h : SpecCopy I C) (hCD : C ≤ D) :
    SpecCopy I D := fun a rx S h1 h2 =>
  Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hCD)

theorem SpecShlConst.mono {k : ℕ} {I : Inst 1 4 Unit} {C D : ℕ} (h : SpecShlConst k I C)
    (hCD : C ≤ D) : SpecShlConst k I D := fun a rx S h1 h2 =>
  Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hCD)

/-! ## The instances and the kernel registers -/

/-- The instances the twist kernels call. -/
structure TwInst where
  mul : Inst 3 8 Unit
  add : Inst 3 4 Unit
  sub : Inst 3 4 Unit
  rnd : Inst 3 6 Unit
  cp : Inst 2 4 Unit
  shl1 : Inst 1 4 Unit
  inc : Inst 1 4 Unit

namespace TwInst

variable (J : TwInst)

/-- Registers: one component per instance, then the symbol register. -/
abbrev Reg : Type :=
  J.mul.R × J.add.R × J.sub.R × J.rnd.R × J.cp.R × J.shl1.R × J.inc.R × Option Sym

def lMul : Lens J.Reg J.mul.R := Lens.fst _ _
def lAdd : Lens J.Reg J.add.R := (Lens.snd _ _).comp (Lens.fst _ _)
def lSub : Lens J.Reg J.sub.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lRnd : Lens J.Reg J.rnd.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lCp : Lens J.Reg J.cp.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lShl1 : Lens J.Reg J.shl1.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
def lInc : Lens J.Reg J.inc.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
def lS : Lens J.Reg (Option Sym) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))))))

theorem reg_finite : Finite J.Reg := by
  haveI := J.mul.fin; haveI := J.add.fin; haveI := J.sub.fin; haveI := J.rnd.fin
  haveI := J.cp.fin; haveI := J.shl1.fin; haveI := J.inc.fin
  infer_instance

theorem reg_nonempty : Nonempty J.Reg := by
  haveI := J.mul.ne; haveI := J.add.ne; haveI := J.sub.ne; haveI := J.rnd.ne
  haveI := J.cp.ne; haveI := J.shl1.ne; haveI := J.inc.ne
  infer_instance

/-- All instances meet their contract bodies with one constant `D`. -/
structure Spec (Mul : ℕ → ℕ) (D : ℕ) : Prop where
  mul : SpecMul Mul J.mul D
  add : SpecAddInt J.add D
  sub : SpecSubInt J.sub D
  rnd : SpecRnd J.rnd D
  cp : SpecCopy J.cp D
  shl1 : SpecShlConst 1 J.shl1 D
  inc : SpecInc J.inc D

end TwInst

/-! ## Host stacks -/

/-- Host stacks of the twist kernels: named `0 W0, 1 TR, 2 TL, 3 C0`; ten scratch stacks. -/
abbrev TwL : Type := Loc 4 10

abbrev W0 : TwL := .inl 0
abbrev TR : TwL := .inl 1
abbrev TL : TwL := .inl 2
abbrev C0 : TwL := .inl 3
abbrev sE : TwL := .inr 0
abbrev sP1 : TwL := .inr 1
abbrev sP2 : TwL := .inr 2
abbrev sP3 : TwL := .inr 3
abbrev sP4 : TwL := .inr 4
abbrev sRE : TwL := .inr 5
abbrev sIM : TwL := .inr 6
abbrev sR2 : TwL := .inr 7
abbrev sO : TwL := .inr 8
abbrev sK : TwL := .inr 9

/-! ## Call rules on the host -/

section Rules

variable {σ : Type}

theorem HT.mulI {Mul : ℕ → ℕ} {I : Inst 3 8 Unit} {D : ℕ} (hI : SpecMul Mul I D)
    (l : Lens σ I.R) (x y z : TwL) (hnd : [x, y, z].Nodup) (B : TwL → List Sym) (w : ℕ)
    (p q : ℤ) (rx ry : List Sym) (hp : bitLen p.natAbs ≤ w) (hq : bitLen q.natAbs ≤ w)
    (hrx : TermOK rx) (hry : TermOK ry) (hx : B x = intSyms p ++ rx)
    (hy : B y = intSyms q ++ ry) :
    HT [] B (callI I [x, y, z] (.inl 0) l) (Function.update B z (intSyms (p * q) ++ B z))
      (D * Mul w + D) :=
  HT.callI_upd I [x, y, z] (.inl 0) hnd rfl (by decide) l B (.inl 2) _
    (hI w p q rx ry _ hp hq hrx hry hx hy) []

theorem HT.addI {I : Inst 3 4 Unit} {D : ℕ} (hI : SpecAddInt I D) (l : Lens σ I.R)
    (x y z : TwL) (hnd : [x, y, z].Nodup) (B : TwL → List Sym) (p q : ℤ) (rx ry : List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) (hx : B x = intSyms p ++ rx)
    (hy : B y = intSyms q ++ ry) :
    HT [] B (callI I [x, y, z] (.inl 0) l) (Function.update B z (intSyms (p + q) ++ B z))
      (D * (bitLen p.natAbs + bitLen q.natAbs + 1)) :=
  HT.callI_upd I [x, y, z] (.inl 0) hnd rfl (by decide) l B (.inl 2) _
    (hI p q rx ry _ hrx hry hx hy) []

theorem HT.subI {I : Inst 3 4 Unit} {D : ℕ} (hI : SpecSubInt I D) (l : Lens σ I.R)
    (x y z : TwL) (hnd : [x, y, z].Nodup) (B : TwL → List Sym) (p q : ℤ) (rx ry : List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) (hx : B x = intSyms p ++ rx)
    (hy : B y = intSyms q ++ ry) :
    HT [] B (callI I [x, y, z] (.inl 0) l) (Function.update B z (intSyms (p - q) ++ B z))
      (D * (bitLen p.natAbs + bitLen q.natAbs + 1)) :=
  HT.callI_upd I [x, y, z] (.inl 0) hnd rfl (by decide) l B (.inl 2) _
    (hI p q rx ry _ hrx hry hx hy) []

theorem HT.rndI {I : Inst 3 6 Unit} {D : ℕ} (hI : SpecRnd I D) (l : Lens σ I.R)
    (x c z : TwL) (hnd : [x, c, z].Nodup) (B : TwL → List Sym) (v : ℤ) (s : ℕ)
    (rx rc : List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hx : B x = intSyms v ++ rx)
    (hc : B c = natSyms s ++ rc) :
    HT [] B (callI I [x, c, z] (.inl 0) l)
      (Function.update B z (intSyms (IntMul.divRoundPow2 v s) ++ B z))
      (D * (bitLen v.natAbs + s + 1)) :=
  HT.callI_upd I [x, c, z] (.inl 0) hnd rfl (by decide) l B (.inl 2) _
    (hI v s rx rc _ hrx hrc hx hc) []

theorem HT.incI {I : Inst 1 4 Unit} {D : ℕ} (hI : SpecInc I D) (l : Lens σ I.R) (k : TwL)
    (B : TwL → List Sym) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B k = natSyms x ++ rx) :
    HT [] B (callI I [k] (.inl 0) l) (Function.update B k (natSyms (x + 1) ++ rx))
      (D * (ones (encodeNat x) + 1)) :=
  HT.callI_upd I [k] (.inl 0) (List.nodup_singleton k) rfl (by decide) l B (.inl 0) _
    (hI x rx _ hrx hB) []

end Rules

#assert_std_axioms SpecMul.mono SpecAddInt.mono SpecSubInt.mono SpecRnd.mono SpecInc.mono
  SpecCopy.mono SpecShlConst.mono TwInst.reg_finite TwInst.reg_nonempty HT.mulI HT.addI HT.subI
  HT.rndI HT.incI

end WP.W9d
