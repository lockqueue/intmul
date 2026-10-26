import WP.W9d.Final
import WP.F9.InstB
import WP.F9.InstW5

/-!
# WP.W9d.Concrete — the twist kernels with the shared instances (Phase F)

`W9_preTwist_holds` and `W9_postTwist_holds` (WP.W9d.Final) hide their programs in `∃`. Here the
witness programs are plain definitions, with every subroutine taken from the shared instance
modules (`WP.Inst` and `WP.F9`):

| slot of `TwInst` | contract | instance |
|---|---|---|
| `mul` | `W5_mulAt` | `WP.Inst.mulInst` (`toomMul`, WP.F9.InstW5) |
| `add` / `sub` | `W3_addInt` / `W3_subInt` | `WP.Inst.addInt` / `WP.Inst.subInt` (WP.F9.InstB) |
| `rnd` | `W9d_roundShift` | the W9dR witness `WP.W9dR.rsProg rsJ` (6 scratch), see below |
| `cp` | `W3_copyNat` | `WP.Inst.copyNat` |
| `shl1` | `W3_shlConst` at `1` | `WP.Inst.shlConst` at `1` |
| `inc` | `W3_incNat` | `WP.Inst.incNat` |

The round shift `rsJ` is built from `WP.Inst.{shlVar, shrConst 1, natToInt, addInt, splitSign, shrVar,
decNat, incNat, copyNat, dropNat}`, exactly the instances `WP.W9dR.w9d_roundShift` extracts.

**Exports.** The package has two kernels with the same registers:
* shared: `mC = 10`, `RC = twJ.Reg`, `r0C`, `hmC`;
* `progPreC` / `closedPreC`: `(kernel twJ (stpPre twJ)).mapStk ιB`, the `W9_preTwist_holds` witness;
* `progPostC` / `closedPostC`: `(kernel twJ (stpPost twJ)).mapStk ιB`, the `W9_postTwist_holds`
  witness;
* the same under the uniform per-kernel witness names, one namespace per kernel: `Pre.{mC, RC, r0C, progC,
  hmC, closedC}` and `Post.{…}`.

There is no `specC`: the concrete instances' contract proofs are not assembled here.
-/

namespace WP.W9d.Concrete

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-! ## W7k2 bundles of the shared instances -/

/-- `W3_addInt`. -/
def addI : WP.W7k2.Inst 3 4 Unit :=
  ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.obs, WP.Inst.addInt.prog, by decide,
    inferInstance, ⟨WP.Inst.addInt.r0⟩, WP.Inst.addInt.closed⟩

/-- `W3_subInt`. -/
def subI : WP.W7k2.Inst 3 4 Unit :=
  ⟨WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.obs, WP.Inst.subInt.prog, by decide,
    inferInstance, ⟨WP.Inst.subInt.r0⟩, WP.Inst.subInt.closed⟩

/-- `W3_copyNat`. -/
def cpI : WP.W7k2.Inst 2 4 Unit :=
  ⟨WP.Inst.copyNat.m, WP.Inst.copyNat.R, WP.Inst.copyNat.obs, WP.Inst.copyNat.prog, by decide,
    inferInstance, ⟨WP.Inst.copyNat.r0⟩, WP.Inst.copyNat.closed⟩

/-- `W3_shlConst` at `1`. -/
def shl1I : WP.W7k2.Inst 1 4 Unit :=
  ⟨WP.Inst.shlConst.m, WP.Inst.shlConst.R, WP.Inst.shlConst.obs, WP.Inst.shlConst.prog 1,
    by decide, inferInstance, ⟨WP.Inst.shlConst.r0⟩, WP.Inst.shlConst.closed 1⟩

/-- `W3_incNat`. -/
def incI : WP.W7k2.Inst 1 4 Unit :=
  ⟨WP.Inst.incNat.m, WP.Inst.incNat.R, WP.Inst.incNat.obs, WP.Inst.incNat.prog, by decide,
    inferInstance, ⟨WP.Inst.incNat.r0⟩, WP.Inst.incNat.closed⟩

/-! ## The round shift (`W9d_roundShift`, WP W9dR) -/

/-- The instances of the round shift, in `RSInst` field order. -/
def rsJ : WP.W9dR.RSInst :=
  ⟨⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.obs, WP.Inst.shlVar.prog, by decide,
      inferInstance, ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩,
    ⟨WP.Inst.shrConst.m, WP.Inst.shrConst.R, WP.Inst.shrConst.obs, WP.Inst.shrConst.prog 1,
      by decide, inferInstance, ⟨WP.Inst.shrConst.r0⟩, WP.Inst.shrConst.closed 1⟩,
    ⟨WP.Inst.natToInt.m, WP.Inst.natToInt.R, WP.Inst.natToInt.obs, WP.Inst.natToInt.prog,
      by decide, inferInstance, ⟨WP.Inst.natToInt.r0⟩, WP.Inst.natToInt.closed⟩,
    addI,
    ⟨WP.Inst.splitSign.m, WP.Inst.splitSign.R, WP.Inst.splitSign.obs, WP.Inst.splitSign.prog,
      by decide, inferInstance, ⟨WP.Inst.splitSign.r0⟩, WP.Inst.splitSign.closed⟩,
    ⟨WP.Inst.shrVar.m, WP.Inst.shrVar.R, WP.Inst.shrVar.obs, WP.Inst.shrVar.prog, by decide,
      inferInstance, ⟨WP.Inst.shrVar.r0⟩, WP.Inst.shrVar.closed⟩,
    ⟨WP.Inst.decNat.m, WP.Inst.decNat.R, WP.Inst.decNat.obs, WP.Inst.decNat.prog, by decide,
      inferInstance, ⟨WP.Inst.decNat.r0⟩, WP.Inst.decNat.closed⟩,
    incI, cpI,
    ⟨WP.Inst.dropNat.m, WP.Inst.dropNat.R, WP.Inst.dropNat.obs, WP.Inst.dropNat.prog, by decide,
      inferInstance, ⟨WP.Inst.dropNat.r0⟩, WP.Inst.dropNat.closed⟩⟩

theorem rsReg_finite : Finite rsJ.Reg := by
  haveI := rsJ.shlV.fin; haveI := rsJ.shr1.fin; haveI := rsJ.n2i.fin; haveI := rsJ.add.fin
  haveI := rsJ.sgn.fin; haveI := rsJ.shrV.fin; haveI := rsJ.dec.fin; haveI := rsJ.inc.fin
  haveI := rsJ.copy.fin; haveI := rsJ.drop.fin
  infer_instance

/-- Initial registers of the round shift. -/
def rsR0 : rsJ.Reg :=
  (WP.Inst.shlVar.r0, WP.Inst.shrConst.r0, WP.Inst.natToInt.r0, WP.Inst.addInt.r0,
    WP.Inst.splitSign.r0, WP.Inst.shrVar.r0, WP.Inst.decNat.r0, WP.Inst.incNat.r0,
    WP.Inst.copyNat.r0, WP.Inst.dropNat.r0)

/-- `W9d_roundShift`: the witness of `WP.W9dR.w9d_roundShift` (`rsProg`, 6 scratch) over `rsJ`. -/
def rndI : WP.W7k2.Inst 3 6 Unit :=
  ⟨6, rsJ.Reg, fun _ => (), WP.W9dR.rsProg rsJ, le_rfl, rsReg_finite, ⟨rsR0⟩,
    WP.W9dR.rsProg_closed rsJ⟩

/-! ## The kernel instances and the exports -/

/-- The twist kernels' instances. -/
def twJ : TwInst := ⟨WP.Inst.mulInst, addI, subI, rndI, cpI, shl1I, incI⟩

/-- Scratch count of both witnesses. -/
abbrev mC : ℕ := 10

/-- Registers of both witnesses. -/
abbrev RC : Type := twJ.Reg

/-- Initial registers. -/
def r0C : RC :=
  (WP.Inst.toomR0, WP.Inst.addInt.r0, WP.Inst.subInt.r0, rsR0, WP.Inst.copyNat.r0,
    WP.Inst.shlConst.r0, WP.Inst.incNat.r0, none)

theorem hmC : mC ≤ w9Scratch := by decide

/-- **The `W9_preTwist` program** (the witness of `W9_preTwist_holds`, concrete instances). -/
def progPreC : Prog (BLoc mC) (fun _ => Sym) RC := (kernel twJ (stpPre twJ)).mapStk ιB

/-- **The `W9_postTwist` program** (the witness of `W9_postTwist_holds`, concrete instances). -/
def progPostC : Prog (BLoc mC) (fun _ => Sym) RC := (kernel twJ (stpPost twJ)).mapStk ιB

theorem closedPreC : progPreC.Closed :=
  WP.W7k2.freeBelow_mapStk ιB _ 0 (kernel_closed twJ _ (WP.W7k2.callI_closed _ _ _ _))

theorem closedPostC : progPostC.Closed :=
  WP.W7k2.freeBelow_mapStk ιB _ 0
    (kernel_closed twJ _ ⟨WP.W7k2.callI_closed _ _ _ _, WP.W7k2.callI_closed _ _ _ _⟩)

/-! ### Pre-twist concrete witness exports -/

namespace Pre
abbrev mC : ℕ := Concrete.mC
abbrev RC : Type := Concrete.RC
def r0C : RC := Concrete.r0C
def progC : Prog (BLoc mC) (fun _ => Sym) RC := progPreC
theorem hmC : mC ≤ w9Scratch := Concrete.hmC
theorem closedC : progC.Closed := closedPreC
end Pre

/-! ### Post-twist concrete witness exports -/

namespace Post
abbrev mC : ℕ := Concrete.mC
abbrev RC : Type := Concrete.RC
def r0C : RC := Concrete.r0C
def progC : Prog (BLoc mC) (fun _ => Sym) RC := progPostC
theorem hmC : mC ≤ w9Scratch := Concrete.hmC
theorem closedC : progC.Closed := closedPostC
end Post

#assert_std_axioms rsReg_finite hmC closedPreC closedPostC Pre.hmC Pre.closedC Post.hmC
  Post.closedC

end WP.W9d.Concrete
