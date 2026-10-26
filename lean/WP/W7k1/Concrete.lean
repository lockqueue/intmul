import WP.W7k1.Ln
import WP.Inst.W3
import WP.W6a.DivMod

/-!
# WP.W7k1.Concrete — the W7k1 kernels as concrete programs

The `_holds` theorems hide their programs in `∃`. This module exports, for each kernel, **exactly the
witness program** of its `_holds` theorem as a plain `def`, with every subroutine taken from the
shared instance modules:

* W3 subroutines: `WP.Inst.<c>` (`WP.Inst.W3`), bundled as `WP.W7k2.Inst` records (`iCopy` … `iDec`);
* `W7_isqrt` (called by `π`): this package's `isqrtProg` (`iIsq`);
* `W6a_divModNat` (called by `ln 2`): `WP.W6a.divModProg WP.Inst.subNat.prog` (`iDiv`).

| namespace | `mC` | `RC` | `progC` | witness of |
|---|---|---|---|---|
| `Isqrt` | 6 | `IReg` | `isqrtProg` | `W7_isqrt_holds` |
| `Pi` | 16 | `piJ.Reg` | `piProg piJ` | `piScaled_of_inst piJ` (used by `W7_piScaled_holds`) |
| `Ln` | 16 | `lnJ.Reg` | `lnProg lnJ` | `log2Scaled_of_inst lnJ` (used by `W7_log2Scaled_holds`) |

Each namespace also exports `r0C`, `hmC : mC ≤ 16` (the contracts' scratch cap), `closedC`,
`finC : Finite RC` and `instC : WP.W7k2.Inst 2 16 Unit` (the bundle for `callI`); `Isqrt` also has
`specC`, the `W7_isqrt` contract body for `progC`. The runs are in `WP.W7k1.ConcreteRun`.
-/

namespace WP.W7k1.Concrete

open TMFw TMFw.Contracts

/-! ## Subroutine bundles -/

/-- `W3_copyNat`. -/
def iCopy : WP.W7k2.Inst 2 4 Unit :=
  ⟨WP.Inst.copyNat.m, WP.Inst.copyNat.R, WP.Inst.copyNat.obs, WP.Inst.copyNat.prog, by decide,
    inferInstance, ⟨WP.Inst.copyNat.r0⟩, WP.Inst.copyNat.closed⟩

/-- `W3_incNat`. -/
def iInc : WP.W7k2.Inst 1 4 Unit :=
  ⟨WP.Inst.incNat.m, WP.Inst.incNat.R, WP.Inst.incNat.obs, WP.Inst.incNat.prog, by decide,
    inferInstance, ⟨WP.Inst.incNat.r0⟩, WP.Inst.incNat.closed⟩

/-- `W3_shlConst` at `k = 1`. -/
def iShl1 : WP.W7k2.Inst 1 4 Unit :=
  ⟨WP.Inst.shlConst.m, WP.Inst.shlConst.R, WP.Inst.shlConst.obs, WP.Inst.shlConst.prog 1,
    by decide, inferInstance, ⟨WP.Inst.shlConst.r0⟩, WP.Inst.shlConst.closed 1⟩

/-- `W3_shlVar`. -/
def iShlV : WP.W7k2.Inst 2 4 Unit :=
  ⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.obs, WP.Inst.shlVar.prog, by decide,
    inferInstance, ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩

/-- `W3_addNat`. -/
def iAdd : WP.W7k2.Inst 3 4 Unit :=
  ⟨WP.Inst.addNat.m, WP.Inst.addNat.R, WP.Inst.addNat.obs, WP.Inst.addNat.prog, by decide,
    inferInstance, ⟨WP.Inst.addNat.r0⟩, WP.Inst.addNat.closed⟩

/-- `W3_subNat`. -/
def iSub : WP.W7k2.Inst 3 4 Unit :=
  ⟨WP.Inst.subNat.m, WP.Inst.subNat.R, WP.Inst.subNat.obs, WP.Inst.subNat.prog, by decide,
    inferInstance, ⟨WP.Inst.subNat.r0⟩, WP.Inst.subNat.closed⟩

/-- `W3_shrVar`. -/
def iShrV : WP.W7k2.Inst 2 4 Unit :=
  ⟨WP.Inst.shrVar.m, WP.Inst.shrVar.R, WP.Inst.shrVar.obs, WP.Inst.shrVar.prog, by decide,
    inferInstance, ⟨WP.Inst.shrVar.r0⟩, WP.Inst.shrVar.closed⟩

/-- `W3_shrConst` at `k = 1`. -/
def iShr1 : WP.W7k2.Inst 1 4 Unit :=
  ⟨WP.Inst.shrConst.m, WP.Inst.shrConst.R, WP.Inst.shrConst.obs, WP.Inst.shrConst.prog 1,
    by decide, inferInstance, ⟨WP.Inst.shrConst.r0⟩, WP.Inst.shrConst.closed 1⟩

/-- `W3_dropNat`. -/
def iDrop : WP.W7k2.Inst 1 4 Unit :=
  ⟨WP.Inst.dropNat.m, WP.Inst.dropNat.R, WP.Inst.dropNat.obs, WP.Inst.dropNat.prog, by decide,
    inferInstance, ⟨WP.Inst.dropNat.r0⟩, WP.Inst.dropNat.closed⟩

/-- `W3_isZeroNat`. -/
def iIsZ : WP.W7k2.Inst 1 4 Bool :=
  ⟨WP.Inst.isZeroNat.m, WP.Inst.isZeroNat.R, WP.Inst.isZeroNat.obs, WP.Inst.isZeroNat.prog,
    by decide, inferInstance, ⟨WP.Inst.isZeroNat.r0⟩, WP.Inst.isZeroNat.closed⟩

/-- `W3_decNat`. -/
def iDec : WP.W7k2.Inst 1 4 Unit :=
  ⟨WP.Inst.decNat.m, WP.Inst.decNat.R, WP.Inst.decNat.obs, WP.Inst.decNat.prog, by decide,
    inferInstance, ⟨WP.Inst.decNat.r0⟩, WP.Inst.decNat.closed⟩

/-- `W7_isqrt`: the witness of `W7_isqrt_holds`. -/
def iIsq : WP.W7k2.Inst 2 16 Unit :=
  ⟨6, IReg, fun _ => (), isqrtProg, by decide, inferInstance, ⟨(none, none, false)⟩,
    isqrtProg_closed⟩

/-- Initial registers of `divModProg WP.Inst.subNat.prog` (as in `W6a_divModNat_holds`). -/
def divR0 : WP.W6a.DReg WP.Inst.subNat.R := (none, false, (none, none, .eq), WP.Inst.subNat.r0)

/-- `W6a_divModNat`: the witness of `W6a_divModNat_holds`, with the `W3_subNat` instance. -/
def iDiv : WP.W7k2.Inst 4 6 Unit :=
  ⟨3, WP.W6a.DReg WP.Inst.subNat.R, fun _ => (), WP.W6a.divModProg WP.Inst.subNat.prog, by decide,
    inferInstance, ⟨divR0⟩, WP.W6a.divModProg_closed WP.Inst.subNat.prog WP.Inst.subNat.closed⟩

/-- The instances of the `π` kernel. -/
def piJ : PiInst := ⟨iCopy, iInc, iShl1, iShlV, iAdd, iSub, iShrV, iShr1, iDrop, iIsZ, iDec, iIsq⟩

/-- The instances of the `ln 2` kernel. -/
def lnJ : LnInst := ⟨iCopy, iInc, iShl1, iShlV, iAdd, iSub, iShrV, iShr1, iDrop, iIsZ, iDec, iDiv⟩

/-! ## `W7_isqrt` -/

namespace Isqrt

/-- Scratch count. -/
abbrev mC : ℕ := 6

/-- Registers. -/
abbrev RC : Type := IReg

/-- Initial registers. -/
def r0C : RC := (none, none, false)

/-- The `W7_isqrt` program (no subroutines). -/
def progC : Prog (Loc 2 mC) (fun _ => Sym) RC := isqrtProg

theorem hmC : mC ≤ 16 := by decide

theorem closedC : progC.Closed := isqrtProg_closed

theorem finC : Finite RC := inferInstance

/-- The `W7_isqrt` contract body for `progC`, constant `200`. -/
theorem specC (a : ℕ) (ra : List Sym) (S : Loc 2 mC → List Sym) (hra : TermOK ra)
    (hA : S (.inl 0) = natSyms a ++ ra) :
    Runs progC S (Function.update S (.inl 1) (natSyms (Nat.sqrt a) ++ S (.inl 1)))
      (fun _ => True) (200 * (bitLen a * bitLen a + 1)) :=
  Runs.of_eval fun v => by
    obtain ⟨v', t, e, ht⟩ := isqrtProg_eval a ra v S hra hA
    exact ⟨v', t, e, trivial, ht⟩

/-- The bundle for `callI`. -/
def instC : WP.W7k2.Inst 2 16 Unit := ⟨mC, RC, fun _ => (), progC, hmC, finC, ⟨r0C⟩, closedC⟩

end Isqrt

/-! ## `W7_piScaled` -/

namespace Pi

/-- Scratch count. -/
abbrev mC : ℕ := 16

/-- Registers: one component per instance of `piJ`. -/
abbrev RC : Type := piJ.Reg

/-- Initial registers. -/
def r0C : RC :=
  (WP.Inst.copyNat.r0, WP.Inst.incNat.r0, WP.Inst.shlConst.r0, WP.Inst.shlVar.r0,
    WP.Inst.addNat.r0, WP.Inst.subNat.r0, WP.Inst.shrVar.r0, WP.Inst.shrConst.r0,
    WP.Inst.dropNat.r0, WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0, Isqrt.r0C)

/-- The `W7_piScaled` program. -/
def progC : Prog (Loc 2 mC) (fun _ => Sym) RC := piProg piJ

theorem hmC : mC ≤ 16 := by decide

theorem closedC : progC.Closed := piProg_closed piJ

theorem finC : Finite RC := by
  haveI := piJ.copy.fin; haveI := piJ.inc.fin; haveI := piJ.shl1.fin; haveI := piJ.shlV.fin
  haveI := piJ.add.fin; haveI := piJ.sub.fin; haveI := piJ.shrV.fin; haveI := piJ.shr1.fin
  haveI := piJ.drop.fin; haveI := piJ.isz.fin; haveI := piJ.dec.fin; haveI := piJ.isq.fin
  infer_instance

/-- The bundle for `callI`. -/
def instC : WP.W7k2.Inst 2 16 Unit := ⟨mC, RC, fun _ => (), progC, hmC, finC, ⟨r0C⟩, closedC⟩

end Pi

/-! ## `W7_log2Scaled` -/

namespace Ln

/-- Scratch count. -/
abbrev mC : ℕ := 16

/-- Registers: one component per instance of `lnJ`. -/
abbrev RC : Type := lnJ.Reg

/-- Initial registers. -/
def r0C : RC :=
  (WP.Inst.copyNat.r0, WP.Inst.incNat.r0, WP.Inst.shlConst.r0, WP.Inst.shlVar.r0,
    WP.Inst.addNat.r0, WP.Inst.subNat.r0, WP.Inst.shrVar.r0, WP.Inst.shrConst.r0,
    WP.Inst.dropNat.r0, WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0, divR0)

/-- The `W7_log2Scaled` program. -/
def progC : Prog (Loc 2 mC) (fun _ => Sym) RC := lnProg lnJ

theorem hmC : mC ≤ 16 := by decide

theorem closedC : progC.Closed := lnProg_closed lnJ

theorem finC : Finite RC := by
  haveI := lnJ.copy.fin; haveI := lnJ.inc.fin; haveI := lnJ.shl1.fin; haveI := lnJ.shlV.fin
  haveI := lnJ.add.fin; haveI := lnJ.sub.fin; haveI := lnJ.shrV.fin; haveI := lnJ.shr1.fin
  haveI := lnJ.drop.fin; haveI := lnJ.isz.fin; haveI := lnJ.dec.fin; haveI := lnJ.div.fin
  infer_instance

/-- The bundle for `callI`. -/
def instC : WP.W7k2.Inst 2 16 Unit := ⟨mC, RC, fun _ => (), progC, hmC, finC, ⟨r0C⟩, closedC⟩

end Ln

#assert_std_axioms Isqrt.hmC Isqrt.closedC Isqrt.finC Isqrt.specC Pi.hmC Pi.closedC Pi.finC
  Ln.hmC Ln.closedC Ln.finC

end WP.W7k1.Concrete
