import WP.W7k2.Emit
import WP.W7k2.Arith
import WP.W7k2.Canon.Kernels

/-!
# WP.W7k3.Base — the instance bundle of the W7k3 kernels

The kernels `W7_stdChar` and `W7_c0c1` (and their sub-kernels: the series loop, the half-erf)
are sequences of contract calls on W7k2's call layer (`WP.W7k2.Call`). They share one bundle `KI`
of contract instances (one per contract and compile-time parameter) and one register type `KI.R`
(a symbol register, then one register file per instance).

| field | contract | field | contract |
|---|---|---|---|
| `cp` | `W3_copyNat` | `ad` | `W3_addNat` |
| `dr` | `W3_dropNat` | `s1` | `W3_shlConst 1` |
| `iz` | `W3_isZeroNat` | `sv` | `W3_shlVar` |
| `dc`, `ic` | `W3_decNat`, `W3_incNat` | `ng` | `W3_negInt` |
| `ai` | `W3_addInt` | `pi` | `W7_piScaled` |
| `mu` | `W5_mulAt Mul` | `sc`, `ss` | `W7S_series` (cos / sin kind) |
| `dv` | `W6a_divRound` | | |

`KI.Spec I Mul C` states the contract bodies the **series loop** uses (left column) with one shared
constant `C ≥ 1`; `KI.SpecX I C` the extra W3 / W7 ones of the `stdChar` kernel (right column);
the series instances' bodies are `SpecSer` (`WP.W7k3.SerCall`). The series
sub-kernel's statement therefore assumes neither `W7_piScaled` nor `W3_shlVar`; where a program does
not use a field, it can be filled with an arbitrary instance.
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

/-! ## Contract bodies not restated in W7k2 -/

/-- Body of `W3_negInt`. -/
def SpecNegInt (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = intSyms z ++ rx →
    Runs I.P S (Function.update S (.inl 0) (intSyms (-z) ++ rx)) (fun _ => True) C

/-- Body of `W6a_divRound`. -/
def SpecDivRound (I : Inst 3 6 Unit) (C : ℕ) : Prop :=
  ∀ (num : ℤ) (den : ℕ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym), 0 < den →
    TermOK ra → TermOK rb →
    S (.inl 0) = intSyms num ++ ra → S (.inl 1) = natSyms den ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (divRoundRatInt num den) ++ S (.inl 2)))
      (fun _ => True)
      (C * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1))

theorem SpecNegInt.mono {I : Inst 1 4 Unit} {C C' : ℕ} (h : SpecNegInt I C) (hC : C ≤ C') :
    SpecNegInt I C' := fun z rx S h1 h2 => runs_mono (h z rx S h1 h2) hC
theorem SpecDivRound.mono {I : Inst 3 6 Unit} {C C' : ℕ} (h : SpecDivRound I C) (hC : C ≤ C') :
    SpecDivRound I C' := fun n d ra rb S h0 h1 h2 h3 h4 =>
  runs_mono (h n d ra rb S h0 h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

/-! ## Lenses -/

/-- The identity lens (a sub-kernel running on all of the host registers). -/
def lid (σ : Type) : Lens σ σ where
  get := id
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Push a lens one product component to the right. -/
def lsh {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

/-! ## The instance bundle -/

/-- The contract instances of the W7k3 kernels. -/
structure KI : Type 1 where
  /-- `W3_copyNat` -/
  cp : Inst 2 4 Unit
  /-- `W3_dropNat` -/
  dr : Inst 1 4 Unit
  /-- `W3_isZeroNat` -/
  iz : Inst 1 4 Bool
  /-- `W3_decNat` -/
  dc : Inst 1 4 Unit
  /-- `W3_incNat` -/
  ic : Inst 1 4 Unit
  /-- `W3_addInt` -/
  ai : Inst 3 4 Unit
  /-- `W5_mulAt Mul` -/
  mu : Inst 3 8 Unit
  /-- `W6a_divRound` -/
  dv : Inst 3 6 Unit
  /-- `W3_addNat` -/
  ad : Inst 3 4 Unit
  /-- `W3_shlConst 1` -/
  s1 : Inst 1 4 Unit
  /-- `W3_shlVar` -/
  sv : Inst 2 4 Unit
  /-- `W3_negInt` -/
  ng : Inst 1 4 Unit
  /-- `W7_piScaled` -/
  pi : Inst 2 16 Unit
  /-- `W7S_series, cos kind` -/
  sc : Inst 5 12 Unit
  /-- `W7S_series, sin kind` -/
  ss : Inst 5 12 Unit

namespace KI

variable (I : KI)

/-- Host registers: a symbol register, then one register file per instance. -/
abbrev R : Type :=
  Option Sym × I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ic.R × I.ai.R × I.mu.R × I.dv.R × I.ad.R × I.s1.R × I.sv.R × I.ng.R × I.pi.R × I.sc.R × I.ss.R

/-- The symbol register. -/
def lS : Lens I.R (Option Sym) := Lens.fst _ _
def lcp : Lens I.R I.cp.R := lsh (Lens.fst _ _)
def ldr : Lens I.R I.dr.R := lsh (lsh (Lens.fst _ _))
def liz : Lens I.R I.iz.R := lsh (lsh (lsh (Lens.fst _ _)))
def ldc : Lens I.R I.dc.R := lsh (lsh (lsh (lsh (Lens.fst _ _))))
def lic : Lens I.R I.ic.R := lsh (lsh (lsh (lsh (lsh (Lens.fst _ _)))))
def lai : Lens I.R I.ai.R := lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _))))))
def lmu : Lens I.R I.mu.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _)))))))
def ldv : Lens I.R I.dv.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _))))))))
def lad : Lens I.R I.ad.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _)))))))))
def ls1 : Lens I.R I.s1.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _))))))))))
def lsv : Lens I.R I.sv.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _)))))))))))
def lng : Lens I.R I.ng.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _))))))))))))
def lpi : Lens I.R I.pi.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _)))))))))))))
def lsc : Lens I.R I.sc.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.fst _ _))))))))))))))
def lss : Lens I.R I.ss.R := lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (lsh (Lens.snd _ _))))))))))))))

theorem R_finite : Finite I.R := by
  haveI := I.cp.fin; haveI := I.dr.fin; haveI := I.iz.fin; haveI := I.dc.fin; haveI := I.ic.fin; haveI := I.ai.fin; haveI := I.mu.fin; haveI := I.dv.fin; haveI := I.ad.fin; haveI := I.s1.fin; haveI := I.sv.fin; haveI := I.ng.fin; haveI := I.pi.fin; haveI := I.sc.fin; haveI := I.ss.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  haveI := I.cp.ne; haveI := I.dr.ne; haveI := I.iz.ne; haveI := I.dc.ne; haveI := I.ic.ne; haveI := I.ai.ne; haveI := I.mu.ne; haveI := I.dv.ne; haveI := I.ad.ne; haveI := I.s1.ne; haveI := I.sv.ne; haveI := I.ng.ne; haveI := I.pi.ne; haveI := I.sc.ne; haveI := I.ss.ne
  infer_instance

/-- The contract bodies the series loop uses, one shared constant `C ≥ 1`. -/
structure Spec (Mul : ℕ → ℕ) (C : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  iz : SpecIsZero I.iz C
  dc : SpecDec I.dc C
  ic : SpecInc I.ic C
  ai : SpecAddInt I.ai C
  mu : SpecMul Mul I.mu C
  dv : SpecDivRound I.dv C
  one : 1 ≤ C

/-- The contract bodies of the extra fields of the `stdChar` kernel. -/
structure SpecX (C : ℕ) : Prop where
  ad : SpecAddNat I.ad C
  s1 : SpecShlConst 1 I.s1 C
  sv : SpecShlVar I.sv C
  ng : SpecNegInt I.ng C
  pi : SpecPi I.pi C

end KI

/-- Programs over the host stacks `Loc a b` with the bundle registers. -/
abbrev KP (a b : ℕ) (I : KI) : Type := Prog (Loc a b) (fun _ => Sym) I.R

/-! ## Calls on host stacks (the first named stack doubles as the unused default) -/

section Wrappers

variable {a b : ℕ} (I : KI)

def kcp (x y : Loc a b) : KP a b I := callI I.cp [x, y] x I.lcp
def kdr (x : Loc a b) : KP a b I := callI I.dr [x] x I.ldr
def kiz (x : Loc a b) : KP a b I := callI I.iz [x] x I.liz
def kdc (x : Loc a b) : KP a b I := callI I.dc [x] x I.ldc
def kic (x : Loc a b) : KP a b I := callI I.ic [x] x I.lic
def kad (x y z : Loc a b) : KP a b I := callI I.ad [x, y, z] x I.lad
def ks1 (x : Loc a b) : KP a b I := callI I.s1 [x] x I.ls1
def ksv (x c : Loc a b) : KP a b I := callI I.sv [x, c] x I.lsv
def kai (x y z : Loc a b) : KP a b I := callI I.ai [x, y, z] x I.lai
def kng (x : Loc a b) : KP a b I := callI I.ng [x] x I.lng
def kmu (x y z : Loc a b) : KP a b I := callI I.mu [x, y, z] x I.lmu
def kdv (x y z : Loc a b) : KP a b I := callI I.dv [x, y, z] x I.ldv
def kpi (x z : Loc a b) : KP a b I := callI I.pi [x, z] x I.lpi
/-- The series sub-kernel, cos kind (stacks `a0 c d n dst`). -/
def ksc (x0 x1 x2 x3 z : Loc a b) : KP a b I := callI I.sc [x0, x1, x2, x3, z] x0 I.lsc
/-- The series sub-kernel, sin kind (stacks `a0 c d n dst`). -/
def kss (x0 x1 x2 x3 z : Loc a b) : KP a b I := callI I.ss [x0, x1, x2, x3, z] x0 I.lss

theorem kcall_closed {n cap : ℕ} {O : Type} (J : Inst n cap O) (nm : List (Loc a b)) (d : Loc a b)
    (l : Lens I.R J.R) : (callI J nm d l).Closed := callI_closed J nm d l

end Wrappers

#assert_std_axioms SpecNegInt.mono SpecDivRound.mono
  KI.R_finite KI.R_nonempty kcall_closed

end WP.W7k3
