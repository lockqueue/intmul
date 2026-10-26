import WP.W7k3.Ser
import WP.F9.InstW5
import WP.Inst.W7k1

/-!
# WP.W7k3.Concrete — the series sub-kernel with concrete subroutines (Phase F)

`W7S_series_holds` hides its program inside `∃`; here it is a plain definition, with every subroutine
taken from the shared concrete instance modules (`WP.Inst` and `WP.F9`):

| field | instance | module |
|---|---|---|
| `cp dr iz dc ic` | `WP.Inst.{copyNat dropNat isZeroNat decNat incNat}.inst` | `WP.Inst.W7k1` |
| `ad s1 sv` | `WP.Inst.addNat.inst`, `shlConst.inst 1`, `shlVar.inst` | `WP.Inst.W7k1` |
| `ai ng` | `WP.Inst.addInt`, `negInt` (records built here) | `WP.F9.InstB` |
| `mu` | `WP.Inst.mulInst` (Toom-3, `toomMul`) | `WP.F9.InstW5` |
| `dv` | `WP.Inst.divRound.inst` (`WP.W6a.divRoundProg WP.Inst.subNat.prog`) | `WP.Inst.W7k1` |
| `pi sc ss` | not used by the series program: `dummyInst` | — |

Exports: `KIc` (the bundle), `mC = 12`, `RC = KIc.R`, `r0C`, `progC κ = serProg KIc κ` (the program of
`W7S_series_holds` for kind `κ`), `hmC`, `closedC`, and `serC κ : Inst 5 12 Unit` (the instance, for the
`sc`/`ss` fields of a kernel bundle such as stdChar's). Runs: `WP.W7k3.ConcreteRun`.
-/

namespace WP.W7k3.Concrete

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

/-- `W3_copyNat`. -/
def iCp : Inst 2 4 Unit := WP.Inst.copyNat.inst
/-- `W3_dropNat`. -/
def iDr : Inst 1 4 Unit := WP.Inst.dropNat.inst
/-- `W3_isZeroNat`. -/
def iIz : Inst 1 4 Bool := WP.Inst.isZeroNat.inst
/-- `W3_decNat`. -/
def iDc : Inst 1 4 Unit := WP.Inst.decNat.inst
/-- `W3_incNat`. -/
def iIc : Inst 1 4 Unit := WP.Inst.incNat.inst
/-- `W3_addInt` (`WP.F9.InstB` has no record; built here from its witnesses). -/
def iAi : Inst 3 4 Unit := ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.obs,
  WP.Inst.addInt.prog, by decide, inferInstance, ⟨WP.Inst.addInt.r0⟩, WP.Inst.addInt.closed⟩
/-- `W5_mulAt (T3 …)`: the Toom-3 multiplier. -/
def iMu : Inst 3 8 Unit := WP.Inst.mulInst
/-- Initial registers of the rounding division. -/
def dvR0 : WP.W6a.RReg WP.Inst.subNat.R := WP.Inst.divRound.r0
/-- `W6a_divRound`. -/
def iDv : Inst 3 6 Unit := WP.Inst.divRound.inst
/-- `W3_addNat`. -/
def iAd : Inst 3 4 Unit := WP.Inst.addNat.inst
/-- `W3_shlConst 1`. -/
def iS1 : Inst 1 4 Unit := WP.Inst.shlConst.inst 1
/-- `W3_shlVar`. -/
def iSv : Inst 2 4 Unit := WP.Inst.shlVar.inst
/-- `W3_negInt` (`WP.F9.InstB` has no record; built here from its witnesses). -/
def iNg : Inst 1 4 Unit := ⟨WP.Inst.negInt.m, WP.Inst.negInt.R, WP.Inst.negInt.obs,
  WP.Inst.negInt.prog, by decide, inferInstance, ⟨WP.Inst.negInt.r0⟩, WP.Inst.negInt.closed⟩

/-- **The concrete bundle** (series-level: `pi`, `sc`, `ss` unused). -/
def KIc : KI := ⟨iCp, iDr, iIz, iDc, iIc, iAi, iMu, iDv, iAd, iS1, iSv, iNg, dummyInst 2 16,
  dummyInst 5 12, dummyInst 5 12⟩

/-- Scratch count of the series sub-kernel. -/
abbrev mC : ℕ := 12

/-- Register type of the series sub-kernel. -/
abbrev RC : Type := KIc.R

/-- Initial registers. -/
def r0C : RC :=
  (none, WP.Inst.copyNat.r0, WP.Inst.dropNat.r0, WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0,
    WP.Inst.incNat.r0, WP.Inst.addInt.r0, WP.Inst.toomR0, dvR0, WP.Inst.addNat.r0,
    WP.Inst.shlConst.r0, WP.Inst.shlVar.r0, WP.Inst.negInt.r0, (), (), ())

/-- **The series sub-kernel's program** for kind `κ` (exactly the program of `W7S_series_holds`,
with the concrete subroutines). -/
def progC (κ : SK) : Prog (Loc 5 mC) (fun _ => Sym) RC := serProg KIc κ

theorem hmC : mC ≤ 12 := le_rfl

theorem closedC (κ : SK) : (progC κ).Closed := serProg_closed KIc κ

/-- The series sub-kernel as an instance (`Inst 5 12 Unit`), for kernel bundles. -/
def serC (κ : SK) : Inst 5 12 Unit := serInst KIc κ

#assert_std_axioms hmC closedC

end WP.W7k3.Concrete
