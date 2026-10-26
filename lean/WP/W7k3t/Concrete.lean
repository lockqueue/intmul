import WP.W7k3t.Top
import WP.F9.InstW5
import WP.W6a.DivRoundProg

/-!
# WP.W7k3t.Concrete — the tap kernel with the shared instances (Phase F; written by W9sq)

`progC = topProg IC`: the tap kernel (`W7_sincGaussianTap`'s witness `tapInst I = mkInst I (topProg I)
(topProg_closed I)`) with its bundle `TI` filled from the shared concrete instance modules:

| slot | instance |
|---|---|
| `cp dr iz dc ic ad sv cm` | `WP.Inst.copyNat / dropNat / isZeroNat / decNat / incNat / addNat / shlVar / cmpNat` (`WP.Inst.W3`) |
| `ai si ci` | `WP.Inst.addInt / subInt / cmpInt` (`WP.F9.InstB`) |
| `mu` | `WP.Inst.mulInst` (`WP.F9.InstW5`) |
| `dv` | `WP.W6a.divRoundProg WP.Inst.subNat.prog` (as in `W6a_divRound_holds`) |

The tap has its own series loop (`Ser`/`SerLoop`), so no W7k3 series instance is needed.
`tapInstC = mkInst IC progC closedC` is the `WP.W7k2.Inst 8 16 Unit` bundle (= `tapInst IC`).
-/

namespace WP.W7k3t.Concrete

open TMFw TMFw.Lib TMFw.Contracts WP.W7k2 WP.W7k3t

def cpI : Inst 2 4 Unit :=
  ⟨WP.Inst.copyNat.m, WP.Inst.copyNat.R, WP.Inst.copyNat.obs, WP.Inst.copyNat.prog, by decide,
    inferInstance, ⟨WP.Inst.copyNat.r0⟩, WP.Inst.copyNat.closed⟩

def drI : Inst 1 4 Unit :=
  ⟨WP.Inst.dropNat.m, WP.Inst.dropNat.R, WP.Inst.dropNat.obs, WP.Inst.dropNat.prog, by decide,
    inferInstance, ⟨WP.Inst.dropNat.r0⟩, WP.Inst.dropNat.closed⟩

def izI : Inst 1 4 Bool :=
  ⟨WP.Inst.isZeroNat.m, WP.Inst.isZeroNat.R, WP.Inst.isZeroNat.obs, WP.Inst.isZeroNat.prog,
    by decide, inferInstance, ⟨WP.Inst.isZeroNat.r0⟩, WP.Inst.isZeroNat.closed⟩

def dcI : Inst 1 4 Unit :=
  ⟨WP.Inst.decNat.m, WP.Inst.decNat.R, WP.Inst.decNat.obs, WP.Inst.decNat.prog, by decide,
    inferInstance, ⟨WP.Inst.decNat.r0⟩, WP.Inst.decNat.closed⟩

def icI : Inst 1 4 Unit :=
  ⟨WP.Inst.incNat.m, WP.Inst.incNat.R, WP.Inst.incNat.obs, WP.Inst.incNat.prog, by decide,
    inferInstance, ⟨WP.Inst.incNat.r0⟩, WP.Inst.incNat.closed⟩

def adI : Inst 3 4 Unit :=
  ⟨WP.Inst.addNat.m, WP.Inst.addNat.R, WP.Inst.addNat.obs, WP.Inst.addNat.prog, by decide,
    inferInstance, ⟨WP.Inst.addNat.r0⟩, WP.Inst.addNat.closed⟩

def svI : Inst 2 4 Unit :=
  ⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.obs, WP.Inst.shlVar.prog, by decide,
    inferInstance, ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩

def cmI : Inst 2 4 Ordering :=
  ⟨WP.Inst.cmpNat.m, WP.Inst.cmpNat.R, WP.Inst.cmpNat.obs, WP.Inst.cmpNat.prog, by decide,
    inferInstance, ⟨WP.Inst.cmpNat.r0⟩, WP.Inst.cmpNat.closed⟩

def aiI : Inst 3 4 Unit :=
  ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.obs, WP.Inst.addInt.prog, by decide,
    inferInstance, ⟨WP.Inst.addInt.r0⟩, WP.Inst.addInt.closed⟩

def siI : Inst 3 4 Unit :=
  ⟨WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.obs, WP.Inst.subInt.prog, by decide,
    inferInstance, ⟨WP.Inst.subInt.r0⟩, WP.Inst.subInt.closed⟩

def ciI : Inst 2 4 Ordering :=
  ⟨WP.Inst.cmpInt.m, WP.Inst.cmpInt.R, WP.Inst.cmpInt.obs, WP.Inst.cmpInt.prog, by decide,
    inferInstance, ⟨WP.Inst.cmpInt.r0⟩, WP.Inst.cmpInt.closed⟩

/-- Initial registers of the rounding division (as in `W6a_divRound_holds`). -/
def dvR0 : WP.W6a.RReg WP.Inst.subNat.R :=
  (none, none, (none, none, .eq), (none, false, (none, none, .eq), WP.Inst.subNat.r0))

def dvI : Inst 3 6 Unit :=
  ⟨4, WP.W6a.RReg WP.Inst.subNat.R, fun _ => (), WP.W6a.divRoundProg WP.Inst.subNat.prog,
    by decide, inferInstance, ⟨dvR0⟩, WP.W6a.divRoundProg_closed _ WP.Inst.subNat.closed⟩

/-- The tap kernel's bundle, from the shared instances. -/
def IC : TI := ⟨cpI, drI, izI, dcI, icI, adI, svI, cmI, aiI, siI, ciI, WP.Inst.mulInst, dvI⟩

/-! ## Concrete witness exports -/

/-- Scratch count (as in `tapInst`). -/
abbrev mC : ℕ := 16

/-- Register type of the witness. -/
abbrev RC : Type := TI.R IC

/-- Initial registers. -/
def r0C : RC :=
  (WP.Inst.copyNat.r0, WP.Inst.dropNat.r0, WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0,
    WP.Inst.incNat.r0, WP.Inst.addNat.r0, WP.Inst.shlVar.r0, WP.Inst.cmpNat.r0, WP.Inst.addInt.r0,
    WP.Inst.subInt.r0, WP.Inst.cmpInt.r0, WP.Inst.toomR0, dvR0)

/-- **The tap kernel program** with every subroutine from the shared instances. -/
def progC : Prog (Loc 8 mC) (fun _ => Sym) RC := topProg IC

/-- The contract's scratch cap (`W7_sincGaussianTap : MContract Unit 8 16 …`). -/
theorem hmC : mC ≤ 16 := le_refl _

theorem closedC : progC.Closed := topProg_closed IC

/-- The W7k2-style bundle of the concrete tap (`= tapInst IC`). -/
def tapInstC : Inst 8 16 Unit := mkInst IC progC closedC

#assert_std_axioms hmC closedC

end WP.W7k3t.Concrete
