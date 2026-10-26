import WP.W9sq.Ops

/-!
# WP.W9sq.Bundle — the instances the kernel calls, one register component each, one constant

`SqI` bundles one extracted instance per frozen contract the kernel calls. `SqI.Reg` has one
register component per instance plus `Option Sym` for raw pops (and a trailing `Unit`), and
`SqI.l*` are the lenses. `SqI.Spec Mul J C` states every instance's contract body at the **same**
constant `C` (the `*.mono` lemmas raise each constant to the sum).
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## Raising the cost constant -/

section Mono

variable {C C' : ℕ}

theorem SpecMul.mono {Mul : ℕ → ℕ} {I : Inst 3 8 Unit} (h : SpecMul Mul I C) (hC : C ≤ C') :
    SpecMul Mul I C' := fun w a b ra rb S h1 h2 h3 h4 h5 h6 =>
  Triple.cost_mono (h w a b ra rb S h1 h2 h3 h4 h5 h6)
    (Nat.add_le_add (Nat.mul_le_mul_right _ hC) hC)

theorem SpecAddInt.mono {I : Inst 3 4 Unit} (h : SpecAddInt I C) (hC : C ≤ C') :
    SpecAddInt I C' := fun a b rx ry S h1 h2 h3 h4 =>
  Triple.cost_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecSubInt.mono {I : Inst 3 4 Unit} (h : SpecSubInt I C) (hC : C ≤ C') :
    SpecSubInt I C' := fun a b rx ry S h1 h2 h3 h4 =>
  Triple.cost_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecAddNat.mono {I : Inst 3 4 Unit} (h : SpecAddNat I C) (hC : C ≤ C') :
    SpecAddNat I C' := fun a b rx ry S h1 h2 h3 h4 =>
  Triple.cost_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecShrVar.mono {I : Inst 2 4 Unit} (h : SpecShrVar I C) (hC : C ≤ C') :
    SpecShrVar I C' := fun a c rx rc S h1 h2 h3 h4 =>
  Triple.cost_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecInc.mono {I : Inst 1 4 Unit} (h : SpecInc I C) (hC : C ≤ C') : SpecInc I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecDecr.mono {I : Inst 1 4 Unit} (h : SpecDecr I C) (hC : C ≤ C') : SpecDecr I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecAttach.mono {b : Bool} {I : Inst 1 4 Unit} (h : SpecAttach b I C) (hC : C ≤ C') :
    SpecAttach b I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) hC

theorem SpecCopy.mono' {I : Inst 2 4 Unit} (h : SpecCopy I C) (hC : C ≤ C') : SpecCopy I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecDrop.mono' {I : Inst 1 4 Unit} (h : SpecDrop I C) (hC : C ≤ C') : SpecDrop I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecShlVar.mono' {I : Inst 2 4 Unit} (h : SpecShlVar I C) (hC : C ≤ C') :
    SpecShlVar I C' := fun a c rx rc S h1 h2 h3 h4 =>
  Triple.cost_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

end Mono

/-! ## The bundle -/

/-- The instances the square kernel calls. -/
structure SqI where
  mul : Inst 3 8 Unit
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  sb : Inst 3 4 Unit
  ad : Inst 3 4 Unit
  an : Inst 3 4 Unit
  sr : Inst 2 4 Unit
  sl : Inst 2 4 Unit
  inc : Inst 1 4 Unit
  dec : Inst 1 4 Unit
  atT : Inst 1 4 Unit
  atF : Inst 1 4 Unit

namespace SqI

variable (J : SqI)

/-- Registers: a symbol register, one component per instance, and a trailing `Unit`. -/
abbrev Reg : Type :=
  Option Sym × J.mul.R × J.cp.R × J.dr.R × J.sb.R × J.ad.R × J.an.R × J.sr.R × J.sl.R ×
    J.inc.R × J.dec.R × J.atT.R × J.atF.R × Unit

/-- `(Lens.snd).comp l`. -/
def sn {A B C : Type} (l : Lens B C) : Lens (A × B) C := (Lens.snd A B).comp l

def lS : Lens J.Reg (Option Sym) := Lens.fst _ _
def lMul : Lens J.Reg J.mul.R := sn (Lens.fst _ _)
def lCp : Lens J.Reg J.cp.R := sn (sn (Lens.fst _ _))
def lDr : Lens J.Reg J.dr.R := sn (sn (sn (Lens.fst _ _)))
def lSb : Lens J.Reg J.sb.R := sn (sn (sn (sn (Lens.fst _ _))))
def lAd : Lens J.Reg J.ad.R := sn (sn (sn (sn (sn (Lens.fst _ _)))))
def lAn : Lens J.Reg J.an.R := sn (sn (sn (sn (sn (sn (Lens.fst _ _))))))
def lSr : Lens J.Reg J.sr.R := sn (sn (sn (sn (sn (sn (sn (Lens.fst _ _)))))))
def lSl : Lens J.Reg J.sl.R := sn (sn (sn (sn (sn (sn (sn (sn (Lens.fst _ _))))))))
def lInc : Lens J.Reg J.inc.R := sn (sn (sn (sn (sn (sn (sn (sn (sn (Lens.fst _ _)))))))))
def lDec : Lens J.Reg J.dec.R :=
  sn (sn (sn (sn (sn (sn (sn (sn (sn (sn (Lens.fst _ _))))))))))
def lAtT : Lens J.Reg J.atT.R :=
  sn (sn (sn (sn (sn (sn (sn (sn (sn (sn (sn (Lens.fst _ _)))))))))))
def lAtF : Lens J.Reg J.atF.R :=
  sn (sn (sn (sn (sn (sn (sn (sn (sn (sn (sn (sn (Lens.fst _ _))))))))))))

/-- Every instance's contract body, at one constant `C`. -/
structure Spec (Mul : ℕ → ℕ) (J : SqI) (C : ℕ) : Prop where
  mul : SpecMul Mul J.mul C
  cp : SpecCopy J.cp C
  dr : SpecDrop J.dr C
  sb : SpecSubInt J.sb C
  ad : SpecAddInt J.ad C
  an : SpecAddNat J.an C
  sr : SpecShrVar J.sr C
  sl : SpecShlVar J.sl C
  inc : SpecInc J.inc C
  dec : SpecDecr J.dec C
  atT : SpecAttach true J.atT C
  atF : SpecAttach false J.atF C

end SqI

#assert_std_axioms SpecMul.mono SpecAddInt.mono SpecSubInt.mono SpecAddNat.mono SpecShrVar.mono
  SpecInc.mono SpecDecr.mono SpecAttach.mono SpecCopy.mono' SpecDrop.mono' SpecShlVar.mono'

end WP.W9sq
