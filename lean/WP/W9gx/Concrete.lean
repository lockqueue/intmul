import WP.W9gx.Final
import WP.F9.InstW5

/-!
# WP.W9gx.Concrete — concrete program for the LEAF kernel `W9_leafFFT`

`W9_leafFFT_holds` takes the five contract programs from `prims_of` (inside `∃`). Here the same
program `(leafProg X).mapStk embS` is built with `X := XC`, whose five slots are the shared verified
instances:

| slot (`Prims`) | contract | instance |
|---|---|---|
| `mul : Inst 3 8` | `W5_mulAt` | `WP.Inst.toomMul` (`WP.F9.InstW5`, Toom-3 over the W3/W3b instances), r0 `toomR0` |
| `add`, `sub : Inst 3 4` | `W3_addInt`, `W3_subInt` | `WP.Inst.addInt`, `WP.Inst.subInt` (`WP.F9.InstB`) |
| `shl`, `shr : Inst 2 4` | `W3_shlVar`, `W3_shrVar` | `WP.Inst.shlVar`, `WP.Inst.shrVar` (`WP.Inst.W3`) |

Concrete witness exports: `mC = 56`, `RC = Option Sym × XC.Reg`, `r0C`, `progC`, `hmC`, `closedC`.
The run against the snapshot is in `WP.W9gx.ConcreteRun`.
-/

namespace WP.W9gx.Concrete

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9g

/-- `W5_mulAt` slot: the concrete Toom-3 multiplier. -/
def mulI : WP.W9g.Inst 3 8 :=
  ⟨8, WP.Inst.toomSubs.σ, WP.Inst.toomMul, le_refl 8, inferInstance, ⟨WP.Inst.toomR0⟩,
    WP.Inst.toomMul_closed⟩

/-- `W3_addInt` slot. -/
def addI : WP.W9g.Inst 3 4 :=
  ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.prog, by decide, inferInstance,
    ⟨WP.Inst.addInt.r0⟩, WP.Inst.addInt.closed⟩

/-- `W3_subInt` slot. -/
def subI : WP.W9g.Inst 3 4 :=
  ⟨WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.prog, by decide, inferInstance,
    ⟨WP.Inst.subInt.r0⟩, WP.Inst.subInt.closed⟩

/-- `W3_shlVar` slot. -/
def shlI : WP.W9g.Inst 2 4 :=
  ⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.prog, by decide, inferInstance,
    ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩

/-- `W3_shrVar` slot. -/
def shrI : WP.W9g.Inst 2 4 :=
  ⟨WP.Inst.shrVar.m, WP.Inst.shrVar.R, WP.Inst.shrVar.prog, by decide, inferInstance,
    ⟨WP.Inst.shrVar.r0⟩, WP.Inst.shrVar.closed⟩

/-- The leaf kernel's contract programs. -/
def XC : Prims := ⟨mulI, addI, subI, shlI, shrI⟩

/-- Scratch count (the `_holds` witness). -/
abbrev mC : ℕ := 56

/-- Registers of the witness. -/
abbrev RC : Type := Option Sym × XC.Reg

/-- Initial registers. -/
def r0C : RC :=
  (none, WP.Inst.toomR0, WP.Inst.addInt.r0, WP.Inst.subInt.r0, WP.Inst.shlVar.r0,
    WP.Inst.shrVar.r0)

/-- **The concrete LEAF kernel**: `W9_leafFFT_holds`'s witness with `X := XC`. -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC := (leafProg XC).mapStk embS

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed := mapStk_closed _ (leafProg_closed XC)

#assert_std_axioms hmC closedC

end WP.W9gx.Concrete
