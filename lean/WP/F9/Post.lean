import WP.W9e.All
import WP.W4.Main
import WP.W4o.OddRoute
import WP.W4f.Top
import WP.W3s.Concat
import WP.W3s.Split
import WP.W3.AddSub

/-!
# WP.F9.Post — the concrete POST routing phases (Q2, Q3+Q4, Q6)

These are the W9e programs instantiated with the verified subroutine programs. They are exactly the
witnesses of each contract's proof:

| hypothesis of W9e | program | witness of |
|---|---|---|
| `W4_transpose .down .down` | `TMFw.W4.transposeProg .down .down` (`Loc 4 4`, `CReg`) | `W4_transpose_holds` |
| `W4_oddStrideFactor` | `WP.W4f.oddProg` (`Loc 3 4`) | `W4_oddStrideFactor_holds` |
| `W4_oddRoute .down .down` | `TMFw.W4o.oddRouteProg` (`Loc 5 4`) | `W4_oddRoute_holds` |
| `W3_shlVar` | `TMFw.W3s.shlVarProg` (`Loc 2 4`) | `W3_shlVar_holds` |
| `W3_splitAt` | `TMFw.W3s.splitAtProg` (`Loc 3 3`) | `W3_splitAt_holds` |
| `W3_subNat` | `WP.W3.addSubProg WP.W3.subBit` (`Loc 3 3`, `AReg`) | `W3_subNat_holds` |
| `W3_cmpNat` | `cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)` (`Loc 2 2`, observation `v.2.2`) | `w3_cmpNat` |

The phase programs `Q2C`, `Q34C`, `Q6C` live on `BLoc 32` (via W9e's `toB`), the form that W9comp's
`postNodeProg` takes. `q2L`, `q34L`, `q6L` are the same programs on W9e's local stacks `Stk`, which
the stage runs use.
-/

namespace WP.F9

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-- The `W3_cmpNat` program (from `w3_cmpNat`) and its observation. -/
def cmpP : Prog (Loc 2 2) (fun _ => Sym) CReg := cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)

/-- Observation of `cmpP`. -/
def cmpObs : CReg → Ordering := fun v => v.2.2

/-- The `W3_subNat` program (from `W3_subNat_holds`). -/
def subP : Prog (Loc 3 3) (fun _ => Sym) WP.W3.AReg := WP.W3.addSubProg WP.W3.subBit

/-- Q2 on `Stk`. -/
def q2L : Prog WP.W9e.Stk (fun _ => Sym) (Option Sym × CReg) :=
  WP.W9e.q2Prog (TMFw.W4.transposeProg .down .down) (le_refl 4)

/-- Q3+Q4 on `Stk`. -/
def q34L : Prog WP.W9e.Stk (fun _ => Sym)
    (WP.W9e.RegsR (WP.W4f.Reg × TMFw.W4o.Reg) (Option Sym) (Option Sym) WP.W3.AReg CReg) :=
  WP.W9e.q34Prog WP.W4f.oddProg (le_refl 4) TMFw.W4o.oddRouteProg (le_refl 4)
    TMFw.W3s.shlVarProg (le_refl 4) TMFw.W3s.splitAtProg (by decide) subP (by decide) cmpP
    (by decide) cmpObs

/-- Q6 on `Stk`. -/
def q6L : Prog WP.W9e.Stk (fun _ => Sym)
    (WP.W9e.RegsR CReg (Option Sym) (Option Sym) WP.W3.AReg CReg) :=
  WP.W9e.q6Prog (TMFw.W4.transposeProg .down .down) (le_refl 4) TMFw.W3s.shlVarProg (le_refl 4)
    TMFw.W3s.splitAtProg (by decide) subP (by decide) cmpP (by decide) cmpObs

/-- **Q2** as a W9 phase program (`W9_postTranspose`'s witness with the verified W4 transpose). -/
def Q2C : Prog (BLoc 32) (fun _ => Sym) (Option Sym × CReg) := q2L.mapStk WP.W9e.toB

/-- **Q3+Q4** as a W9 phase program. -/
def Q34C : Prog (BLoc 32) (fun _ => Sym)
    (WP.W9e.RegsR (WP.W4f.Reg × TMFw.W4o.Reg) (Option Sym) (Option Sym) WP.W3.AReg CReg) :=
  q34L.mapStk WP.W9e.toB

/-- **Q6** as a W9 phase program. -/
def Q6C : Prog (BLoc 32) (fun _ => Sym)
    (WP.W9e.RegsR CReg (Option Sym) (Option Sym) WP.W3.AReg CReg) :=
  q6L.mapStk WP.W9e.toB

/-- Initial registers (the contracts' nonemptiness witnesses). -/
def q2r0 : Option Sym × CReg := (none, (none, none, .eq))

/-- Initial registers of Q3+Q4. -/
def q34r0 : WP.W9e.RegsR (WP.W4f.Reg × TMFw.W4o.Reg) (Option Sym) (Option Sym) WP.W3.AReg CReg :=
  (none, ((none, false, false), (none, none, false)), none, none, (none, none, false),
    (none, none, .eq))

/-- Initial registers of Q6. -/
def q6r0 : WP.W9e.RegsR CReg (Option Sym) (Option Sym) WP.W3.AReg CReg :=
  (none, (none, none, .eq), none, none, (none, none, false), (none, none, .eq))

end WP.F9
