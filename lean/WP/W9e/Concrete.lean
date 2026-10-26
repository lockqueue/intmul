import WP.W9e.All
import WP.Inst.W3
import WP.Inst.W4

/-!
# WP.W9e.Concrete — concrete programs for the POST routing phases Q2, Q3+Q4, Q6

These are W9e's phase programs, `(q2Prog …).mapStk toB` etc. They are exactly the witnesses of
`W9_postTranspose_holds`, `W9_columnRoutes_holds` and `W9_postOutput_holds`, with every subroutine
taken from `WP.Inst`:

| slot | instance |
|---|---|
| W4 transpose `.down .down` | `WP.Inst.transpose.prog .down .down` |
| W4 odd-stride factor / odd route | `WP.Inst.oddStrideFactor.prog` / `WP.Inst.oddRoute.prog` |
| W3 `shlVar`, `splitAt`, `subNat` | `WP.Inst.shlVar/splitAt/subNat.prog` |
| W3 `cmpNat` | `WP.Inst.cmpNat.prog` (observation `cmpNat.obs`) |

There is one sub-namespace per phase (`Q2`, `Q34`, `Q6`), each with `mC = 32`, `RC`, `r0C`, `progC`,
`hmC` and `closedC`. The runs against the snapshot are in `WP.F9.PostRun`.
-/

namespace WP.W9e.Concrete

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

namespace Q2
abbrev mC : ℕ := 32
abbrev RC : Type := Option Sym × WP.Inst.transpose.R
def r0C : RC := (none, WP.Inst.transpose.r0)
def progC : Prog (BLoc mC) (fun _ => Sym) RC :=
  (WP.W9e.q2Prog (WP.Inst.transpose.prog .down .down) (by decide)).mapStk WP.W9e.toB
theorem hmC : mC ≤ w9Scratch := by decide
theorem closedC : progC.Closed :=
  (closed_mapStk_iff WP.W9e.toB _).2
    (WP.W9e.closed_q2Prog _ _ (WP.Inst.transpose.closed .down .down))
end Q2

namespace Q34
abbrev mC : ℕ := 32
abbrev RC : Type :=
  WP.W9e.RegsR (WP.Inst.oddStrideFactor.R × WP.Inst.oddRoute.R) WP.Inst.shlVar.R WP.Inst.splitAt.R
    WP.Inst.subNat.R WP.Inst.cmpNat.R
def r0C : RC :=
  (none, (WP.Inst.oddStrideFactor.r0, WP.Inst.oddRoute.r0), WP.Inst.shlVar.r0, WP.Inst.splitAt.r0,
    WP.Inst.subNat.r0, WP.Inst.cmpNat.r0)
def progC : Prog (BLoc mC) (fun _ => Sym) RC :=
  (WP.W9e.q34Prog WP.Inst.oddStrideFactor.prog (by decide) WP.Inst.oddRoute.prog (by decide)
    WP.Inst.shlVar.prog (by decide) WP.Inst.splitAt.prog (by decide) WP.Inst.subNat.prog
    (by decide) WP.Inst.cmpNat.prog (by decide) WP.Inst.cmpNat.obs).mapStk WP.W9e.toB
theorem hmC : mC ≤ w9Scratch := by decide
theorem closedC : progC.Closed :=
  (closed_mapStk_iff WP.W9e.toB _).2
    (WP.W9e.closed_q34Prog _ _ _ _ _ _ _ _ _ _ _ _ _ WP.Inst.oddStrideFactor.closed
      WP.Inst.oddRoute.closed WP.Inst.shlVar.closed WP.Inst.splitAt.closed WP.Inst.subNat.closed
      WP.Inst.cmpNat.closed)
end Q34

namespace Q6
abbrev mC : ℕ := 32
abbrev RC : Type :=
  WP.W9e.RegsR WP.Inst.transpose.R WP.Inst.shlVar.R WP.Inst.splitAt.R WP.Inst.subNat.R
    WP.Inst.cmpNat.R
def r0C : RC :=
  (none, WP.Inst.transpose.r0, WP.Inst.shlVar.r0, WP.Inst.splitAt.r0, WP.Inst.subNat.r0,
    WP.Inst.cmpNat.r0)
def progC : Prog (BLoc mC) (fun _ => Sym) RC :=
  (WP.W9e.q6Prog (WP.Inst.transpose.prog .down .down) (by decide) WP.Inst.shlVar.prog (by decide)
    WP.Inst.splitAt.prog (by decide) WP.Inst.subNat.prog (by decide) WP.Inst.cmpNat.prog
    (by decide) WP.Inst.cmpNat.obs).mapStk WP.W9e.toB
theorem hmC : mC ≤ w9Scratch := by decide
theorem closedC : progC.Closed :=
  (closed_mapStk_iff WP.W9e.toB _).2
    (WP.W9e.closed_q6Prog _ _ _ _ _ _ _ _ _ _ _ (WP.Inst.transpose.closed .down .down)
      WP.Inst.shlVar.closed WP.Inst.splitAt.closed WP.Inst.subNat.closed WP.Inst.cmpNat.closed)
end Q6

#assert_std_axioms Q2.hmC Q2.closedC Q34.hmC Q34.closedC Q6.hmC Q6.closedC

end WP.W9e.Concrete
