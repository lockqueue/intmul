import WP.W3.Misc
import WP.W3.AddSub
import WP.W3s.Split
import WP.W3s.Concat
import WP.W3e.Shift

/-!
# WP.Inst.W3 — concrete instances of the unsigned W3 contracts

One namespace `WP.Inst.<c>` per contract `TMFw.Contracts.W3_<c>`, exporting the witnesses of its proof as
plain definitions, so stage programs (which take their subroutines as parameters) can be instantiated and
run:

* `m` (scratch stacks), `R` (registers), `r0 : R` (initial registers), `obs` (observation);
* `prog : Prog (Loc n m) (fun _ => Sym) R` (with the contract's parameter, if any);
* `closed : prog.Closed`.

The contract theorems for exactly these definitions are in `WP.Inst.W3Ok`.

| contract | program | `m` | `R` | proved by |
|---|---|---|---|---|
| `copyNat` | `copyBlock (.inl 0) (.inl 1) (.inr 0)` | 1 | `Option Sym` | `w3_copyNat` |
| `cmpNat` | `cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)`, obs `v.2.2` | 2 | `CReg` | `w3_cmpNat` |
| `isZeroNat` | `zeroTest (.inl 0)`, obs `!optIsBit` | 0 | `Option Sym` | `w3_isZeroNat` |
| `incNat` / `decNat` | `inc` / `dec (.inl 0) (.inr 0)` | 1 | `Option Sym` | `w3_incNat` / `w3_decNat` |
| `natToInt` | `pushC (.inl 0) .pos` | 0 | `Option Sym` | `w3_natToInt` |
| `splitSign` | `popR (.inl 0)`, obs `r = some .neg` | 0 | `Option Sym` | `w3_splitSign` |
| `addNat` / `subNat` | `WP.W3.addSubProg addBit` / `subBit` | 3 | `AReg` | `WP.W3.W3_addNat_holds` / `W3_subNat_holds` |
| `dropNat` / `normNat` | `WP.W3.dropNum (.inl 0)` / `WP.W3.normProg` | 0 / 1 | `Option Sym` | `WP.W3.W3_dropNat_holds` / `W3_normNat_holds` |
| `splitAt` / `concatAt` | `TMFw.W3s.splitAtProg` / `concatAtProg` | 3 | `Option Sym` | `TMFw.W3s.W3_splitAt_holds` / `W3_concatAt_holds` |
| `shrVar` / `shlVar` | `TMFw.W3s.shrVarProg` / `shlVarProg` | 4 | `Option Sym` | `TMFw.W3s.W3_shrVar_holds` / `W3_shlVar_holds` |
| `shlConst k` / `shrConst k` | `WP.W3e.shlProg k` / `shrProg k` | 0 | `Option Sym` | `WP.W3e.W3_shlConst_holds` / `W3_shrConst_holds` |

The signed instances (W3b) and the Toom-3 subroutine record (W5 `Subs`) are built on top of this module
(`WP.F9.InstB`, `WP.F9.InstW5`).
-/

namespace WP.Inst

open TMFw TMFw.Lib TMFw.Contracts

namespace copyNat
abbrev m : ℕ := 1
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 2 m) (fun _ => Sym) R := copyBlock (.inl 0) (.inl 1) (.inr 0)
theorem closed : prog.Closed := by
  simp [prog, Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]
end copyNat

namespace cmpNat
abbrev m : ℕ := 2
abbrev R : Type := CReg
def r0 : R := (none, none, .eq)
def obs : R → Ordering := fun v => v.2.2
def prog : Prog (Loc 2 m) (fun _ => Sym) R := cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)
theorem closed : prog.Closed := by
  simp [prog, Prog.Closed, Prog.FreeBelow, cmpNum, cmpBody, Prog.liftRegs, pushC, pushR, popR,
    restoreR, moveBits, moveBitsBody, skip]
end cmpNat

namespace isZeroNat
abbrev m : ℕ := 0
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Bool := fun r => !optIsBit r
def prog : Prog (Loc 1 m) (fun _ => Sym) R := zeroTest (.inl 0)
theorem closed : prog.Closed := by
  simp [prog, Prog.Closed, Prog.FreeBelow, zeroTest, peekR]
end isZeroNat

namespace incNat
abbrev m : ℕ := 1
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 1 m) (fun _ => Sym) R := TMFw.Lib.inc (.inl 0) (.inr 0)
theorem closed : prog.Closed := by
  simp [prog, Prog.Closed, Prog.FreeBelow, TMFw.Lib.inc, incFix, scanLoop, scanBody, pushC, popR,
    restoreR, pushR, skip, moveBits, moveBitsBody]
end incNat

namespace decNat
abbrev m : ℕ := 1
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 1 m) (fun _ => Sym) R := TMFw.Lib.dec (.inl 0) (.inr 0)
theorem closed : prog.Closed := by
  simp [prog, Prog.Closed, Prog.FreeBelow, TMFw.Lib.dec, decFix, scanLoop, scanBody, pushC, popR,
    peekR, pushR, skip, moveBits, moveBitsBody]
end decNat

namespace natToInt
abbrev m : ℕ := 0
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 1 m) (fun _ => Sym) R := pushC (.inl 0) .pos
theorem closed : prog.Closed := by simp [prog, Prog.Closed, Prog.FreeBelow, pushC]
end natToInt

namespace splitSign
abbrev m : ℕ := 0
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Bool := fun r => decide (r = some Sym.neg)
def prog : Prog (Loc 1 m) (fun _ => Sym) R := popR (.inl 0)
theorem closed : prog.Closed := by simp [prog, Prog.Closed, Prog.FreeBelow, popR]
end splitSign

namespace addNat
abbrev m : ℕ := 3
abbrev R : Type := WP.W3.AReg
def r0 : R := (none, none, false)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 3 m) (fun _ => Sym) R := WP.W3.addSubProg WP.W3.addBit
theorem closed : prog.Closed := WP.W3.addSubProg_closed WP.W3.addBit
end addNat

namespace subNat
abbrev m : ℕ := 3
abbrev R : Type := WP.W3.AReg
def r0 : R := (none, none, false)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 3 m) (fun _ => Sym) R := WP.W3.addSubProg WP.W3.subBit
theorem closed : prog.Closed := WP.W3.addSubProg_closed WP.W3.subBit
end subNat

namespace dropNat
abbrev m : ℕ := 0
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 1 m) (fun _ => Sym) R := WP.W3.dropNum (.inl 0)
theorem closed : prog.Closed := WP.W3.closed_of_noRec rfl
end dropNat

namespace normNat
abbrev m : ℕ := 1
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 1 m) (fun _ => Sym) R := WP.W3.normProg
theorem closed : prog.Closed := WP.W3.closed_of_noRec rfl
end normNat

namespace splitAt
abbrev m : ℕ := 3
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 3 m) (fun _ => Sym) R := TMFw.W3s.splitAtProg
theorem closed : prog.Closed := TMFw.W3s.splitCore_closed _ _ _ _ _ _
end splitAt

namespace concatAt
abbrev m : ℕ := 3
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 3 m) (fun _ => Sym) R := TMFw.W3s.concatAtProg
theorem closed : prog.Closed := TMFw.W3s.concatCore_closed _ _ _ _ _ _
end concatAt

namespace shrVar
abbrev m : ℕ := 4
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 2 m) (fun _ => Sym) R := TMFw.W3s.shrVarProg
theorem closed : prog.Closed := TMFw.W3s.shrVarProg_closed
end shrVar

namespace shlVar
abbrev m : ℕ := 4
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 2 m) (fun _ => Sym) R := TMFw.W3s.shlVarProg
theorem closed : prog.Closed := TMFw.W3s.shlVarProg_closed
end shlVar

namespace shlConst
abbrev m : ℕ := 0
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog (k : ℕ) : Prog (Loc 1 m) (fun _ => Sym) R := WP.W3e.shlProg k
theorem closed (k : ℕ) : (prog k).Closed := WP.W3e.shlProg_closed k
end shlConst

namespace shrConst
abbrev m : ℕ := 0
abbrev R : Type := Option Sym
def r0 : R := none
def obs : R → Unit := fun _ => ()
def prog (k : ℕ) : Prog (Loc 1 m) (fun _ => Sym) R := WP.W3e.shrProg k
theorem closed (k : ℕ) : (prog k).Closed := WP.W3e.shrProg_closed k
end shrConst

end WP.Inst
