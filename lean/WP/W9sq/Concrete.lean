import WP.W9sq.Main3
import WP.F9.InstW5

/-!
# WP.W9sq.Concrete — the `W9_square` witness program with the shared instances (Phase F)

`progC` is exactly the program of `WP.W9sq.W9_square_core` (`(sqProg J (initK J)).mapStk eH`), with
the bundle `J := JC` filled from the shared concrete instance modules:

| slot | instance |
|---|---|
| `mul` (`W5_mulAt`) | `WP.Inst.mulInst` (`WP.F9.InstW5`: `toomMul`, registers `toomSubs.σ`, r0 `toomR0`) |
| `cp`, `dr`, `an`, `sr`, `sl`, `inc`, `dec` | `WP.Inst.copyNat / dropNat / addNat / shrVar / shlVar / incNat / decNat` (`WP.Inst.W3`) |
| `sb`, `ad` | `WP.Inst.subInt / addInt` (`WP.F9.InstB`) |
| `atT`, `atF` | `WP.Inst.attachSign` at `true` / `false` (`WP.F9.InstB`) |

`mC = 24` scratch stacks, registers `RC = SqI.Reg JC`, initial registers `r0C`.
-/

namespace WP.W9sq.Concrete

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 WP.W9sq

/-! ## W7k2-style bundles of the shared instances -/

def cpI : Inst 2 4 Unit :=
  ⟨WP.Inst.copyNat.m, WP.Inst.copyNat.R, WP.Inst.copyNat.obs, WP.Inst.copyNat.prog, by decide,
    inferInstance, ⟨WP.Inst.copyNat.r0⟩, WP.Inst.copyNat.closed⟩

def drI : Inst 1 4 Unit :=
  ⟨WP.Inst.dropNat.m, WP.Inst.dropNat.R, WP.Inst.dropNat.obs, WP.Inst.dropNat.prog, by decide,
    inferInstance, ⟨WP.Inst.dropNat.r0⟩, WP.Inst.dropNat.closed⟩

def sbI : Inst 3 4 Unit :=
  ⟨WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.obs, WP.Inst.subInt.prog, by decide,
    inferInstance, ⟨WP.Inst.subInt.r0⟩, WP.Inst.subInt.closed⟩

def adI : Inst 3 4 Unit :=
  ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.obs, WP.Inst.addInt.prog, by decide,
    inferInstance, ⟨WP.Inst.addInt.r0⟩, WP.Inst.addInt.closed⟩

def anI : Inst 3 4 Unit :=
  ⟨WP.Inst.addNat.m, WP.Inst.addNat.R, WP.Inst.addNat.obs, WP.Inst.addNat.prog, by decide,
    inferInstance, ⟨WP.Inst.addNat.r0⟩, WP.Inst.addNat.closed⟩

def srI : Inst 2 4 Unit :=
  ⟨WP.Inst.shrVar.m, WP.Inst.shrVar.R, WP.Inst.shrVar.obs, WP.Inst.shrVar.prog, by decide,
    inferInstance, ⟨WP.Inst.shrVar.r0⟩, WP.Inst.shrVar.closed⟩

def slI : Inst 2 4 Unit :=
  ⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.obs, WP.Inst.shlVar.prog, by decide,
    inferInstance, ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩

def incI : Inst 1 4 Unit :=
  ⟨WP.Inst.incNat.m, WP.Inst.incNat.R, WP.Inst.incNat.obs, WP.Inst.incNat.prog, by decide,
    inferInstance, ⟨WP.Inst.incNat.r0⟩, WP.Inst.incNat.closed⟩

def decI : Inst 1 4 Unit :=
  ⟨WP.Inst.decNat.m, WP.Inst.decNat.R, WP.Inst.decNat.obs, WP.Inst.decNat.prog, by decide,
    inferInstance, ⟨WP.Inst.decNat.r0⟩, WP.Inst.decNat.closed⟩

def atTI : Inst 1 4 Unit :=
  ⟨WP.Inst.attachSign.m, WP.Inst.attachSign.R, WP.Inst.attachSign.obs, WP.Inst.attachSign.prog true,
    by decide, inferInstance, ⟨WP.Inst.attachSign.r0⟩, WP.Inst.attachSign.closed true⟩

def atFI : Inst 1 4 Unit :=
  ⟨WP.Inst.attachSign.m, WP.Inst.attachSign.R, WP.Inst.attachSign.obs,
    WP.Inst.attachSign.prog false, by decide, inferInstance, ⟨WP.Inst.attachSign.r0⟩,
    WP.Inst.attachSign.closed false⟩

/-- The bundle of the square kernel, from the shared instances. -/
def JC : SqI := ⟨WP.Inst.mulInst, cpI, drI, sbI, adI, anI, srI, slI, incI, decI, atTI, atFI⟩

/-! ## Concrete witness exports -/

/-- Scratch count (as in `W9_square_core`). -/
abbrev mC : ℕ := nS

/-- Register type of the witness. -/
abbrev RC : Type := SqI.Reg JC

/-- Initial registers. -/
def r0C : RC :=
  (none, WP.Inst.toomR0, WP.Inst.copyNat.r0, WP.Inst.dropNat.r0, WP.Inst.subInt.r0,
    WP.Inst.addInt.r0, WP.Inst.addNat.r0, WP.Inst.shrVar.r0, WP.Inst.shlVar.r0,
    WP.Inst.incNat.r0, WP.Inst.decNat.r0, WP.Inst.attachSign.r0, WP.Inst.attachSign.r0, ())

/-- **The `W9_square` witness program** with every subroutine from the shared instances. -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC := (sqProg JC (initK JC)).mapStk eH

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed := closed_mapStk_eH (sqProg_closed _ _ (initK_closed _))

#assert_std_axioms hmC closedC

end WP.W9sq.Concrete
