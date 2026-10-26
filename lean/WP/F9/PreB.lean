import WP.F9.InstB
import WP.W9b.AltSum
import WP.W9b.Emit
import WP.W9b.Transpose
import WP.W4.Main

/-!
# WP.F9.PreB — the concrete PRE routing phases P1, P2, P8 (W9b)

These are the witnesses of the W9b proofs with their subroutine hypotheses instantiated:

| phase | contract | program | `m` | registers |
|---|---|---|---|---|
| P1 | `W9_preTranspose` | `(tProg (TMFw.W4.transposeProg .down .up) _).mapStk tι` | 8 | `TReg CReg` |
| P2 | `W9_altSum` | `(altKernel kit).mapStk aι`, with the kit from `WP.Inst` (addInt, subInt, addNat, subNat, shlVar, shrVar) | 24 | `KReg kit` |
| P8 | `W9_emitRows` | `emitProg.mapStk eι` | 6 | `Option Sym` |
-/

namespace WP.F9

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-- **P1** (`W9_preTranspose`'s witness with the verified W4 transpose, `.down .up`). -/
def P1C : Prog (BLoc 8) (fun _ => Sym) (WP.W9b.TReg CReg) :=
  (WP.W9b.tProg (TMFw.W4.transposeProg .down .up) (le_refl 4)).mapStk WP.W9b.tι

/-- Initial registers of P1. -/
def p1r0 : WP.W9b.TReg CReg := (none, (none, none, .eq))

/-- The W3 kit of P2, from the instances. -/
def altKit : WP.W9b.W3Kit :=
  ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.prog, by decide,
    WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.prog, by decide,
    WP.Inst.addNat.m, WP.Inst.addNat.R, WP.Inst.addNat.prog, by decide,
    WP.Inst.subNat.m, WP.Inst.subNat.R, WP.Inst.subNat.prog, by decide,
    WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.prog, by decide,
    WP.Inst.shrVar.m, WP.Inst.shrVar.R, WP.Inst.shrVar.prog, by decide⟩

/-- **P2** (`W9_altSum`'s witness). -/
def P2C : Prog (BLoc 24) (fun _ => Sym) (WP.W9b.KReg altKit) :=
  (WP.W9b.altKernel altKit).mapStk WP.W9b.aι

/-- Initial registers of P2. -/
def p2r0 : WP.W9b.KReg altKit :=
  (none, (none, none, .eq), WP.Inst.addInt.r0, WP.Inst.subInt.r0, WP.Inst.addNat.r0,
    WP.Inst.subNat.r0, WP.Inst.shlVar.r0, WP.Inst.shrVar.r0)

/-- **P8** (`W9_emitRows`'s witness). -/
def P8C : Prog (BLoc 6) (fun _ => Sym) (Option Sym) := WP.W9b.emitProg.mapStk WP.W9b.eι

/-- Initial registers of P8. -/
def p8r0 : Option Sym := none

end WP.F9
