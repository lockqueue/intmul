import WP.W7k3.Concrete
import WP.W7k3c.Final

/-!
# WP.W7k3.ConcreteC0C1 — the `c0c1` kernel with concrete subroutines (Phase F)

`WP.W7k3c.W7_c0c1_holds` (`WP.W7k3c`) hides its program `WP.W7k3c.pMain I` inside
`∃`. Here it is instantiated with the concrete bundle `CIc : WP.W7k3c.CI`:

| field | instance |
|---|---|
| `cp dr ad sb sv cm` | `WP.Inst.{copyNat dropNat addNat subNat shlVar cmpNat}.inst` (`WP.Inst.W7k1`) |
| `ai si ng ci` | `WP.Inst.{addInt subInt negInt cmpInt}` (`WP.F9.InstB`, records built here) |
| `mu` | `WP.Inst.mulInst` (Toom-3) |
| `dv` | `WP.Inst.divRound.inst` |
| `pi ln sq` | `WP.Inst.{piScaled log2Scaled isqrt}.inst` (`WP.Inst.W7k1`) |
| `se` | `serC SK.erf` (the concrete series sub-kernel, `WP.W7k3.Concrete`) |

Exports: `CIc`, `mC = 16`, `RC = CIc.R`, `r0C`, `progC = WP.W7k3c.pMain CIc`, `hmC`, `closedC`,
`c0c1InstC : Inst 5 16 Unit` (`= WP.W7k3c.c0c1InstOf CIc`).

A full machine run is infeasible (`π`, `ln 2` at `≥ 56` bits and three half-erf series of `≥ 149`
steps on `~400`-bit operands). Validation is by components: the series runs (`ConcreteRun`, exact),
the `π` / `ln 2` / `isqrt` runs (`WP.Inst.Smoke2`), and the proof `W7_c0c1_holds` of the composition.
-/

namespace WP.W7k3.ConcreteC0C1

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3 WP.W7k3.Concrete

/-- `W3_subNat`. -/
def iSb : Inst 3 4 Unit := WP.Inst.subNat.inst
/-- `W3_cmpNat`. -/
def iCm : Inst 2 4 Ordering := WP.Inst.cmpNat.inst
/-- `W3_subInt`. -/
def iSi : Inst 3 4 Unit := ⟨WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.obs,
  WP.Inst.subInt.prog, by decide, inferInstance, ⟨WP.Inst.subInt.r0⟩, WP.Inst.subInt.closed⟩
/-- `W3_cmpInt`. -/
def iCi : Inst 2 4 Ordering := ⟨WP.Inst.cmpInt.m, WP.Inst.cmpInt.R, WP.Inst.cmpInt.obs,
  WP.Inst.cmpInt.prog, by decide, inferInstance, ⟨WP.Inst.cmpInt.r0⟩, WP.Inst.cmpInt.closed⟩

/-- **The concrete bundle** of the `c0c1` kernel. -/
def CIc : WP.W7k3c.CI := ⟨iCp, iDr, iAd, iSb, iSv, iCm, iAi, iSi, iNg, iCi, iMu, iDv,
  WP.Inst.piScaled.inst, WP.Inst.log2Scaled.inst, WP.Inst.isqrt.inst, serC SK.erf⟩

/-- Scratch count of the `c0c1` kernel. -/
abbrev mC : ℕ := 16

/-- Register type of the `c0c1` kernel. -/
abbrev RC : Type := CIc.R

/-- Initial registers. -/
def r0C : RC :=
  (WP.Inst.copyNat.r0, WP.Inst.dropNat.r0, WP.Inst.addNat.r0, WP.Inst.subNat.r0,
    WP.Inst.shlVar.r0, WP.Inst.cmpNat.r0, WP.Inst.addInt.r0, WP.Inst.subInt.r0, WP.Inst.negInt.r0,
    WP.Inst.cmpInt.r0, WP.Inst.toomR0, dvR0, WP.Inst.piScaled.r0, WP.Inst.log2Scaled.r0,
    WP.Inst.isqrt.r0, Concrete.r0C)

/-- **The `c0c1` program** (exactly the program of `W7_c0c1_holds`, with the concrete
subroutines). -/
def progC : Prog (Loc 5 mC) (fun _ => Sym) RC := WP.W7k3c.pMain CIc

theorem hmC : mC ≤ 16 := le_rfl

theorem closedC : progC.Closed := WP.W7k3c.pMain_closed CIc

/-- The `c0c1` kernel as an instance (`= WP.W7k3c.c0c1InstOf CIc`). -/
def c0c1InstC : Inst 5 16 Unit := WP.W7k3c.c0c1InstOf CIc

#assert_std_axioms hmC closedC

end WP.W7k3.ConcreteC0C1
