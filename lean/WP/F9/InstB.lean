import WP.Inst.W3
import WP.W3b.AddSub
import WP.W3b.CmpInt
import WP.W3b.SmallOp
import WP.W3b.Sign

/-!
# WP.F9.InstB — concrete instances of the signed W3 contracts (W3b)

Same convention as `WP.Inst.W3`: one namespace `WP.Inst.<c>` per contract `TMFw.Contracts.W3_<c>`,
exporting the witnesses of its proof as plain definitions: `m`, `R`, `r0 : R`, `obs`, `prog` and
`closed : prog.Closed`. The W3b programs take unsigned subroutines as parameters; here they get the
`WP.Inst` instances (`addNat`, `subNat`, `cmpNat`), exactly as `W3_addInt_holds` does when it is given
`W3_addNat_holds`, `W3_subNat_holds` and `w3_cmpNat`.

| contract | program | `m` | `R` | proved by |
|---|---|---|---|---|
| `addInt` / `subInt` | `TMFw.W3b.addSubProg … addNat.prog subNat.prog cmpNat.prog false/true` | 4 | `RegA AReg AReg CReg` | `W3_addInt_holds` / `W3_subInt_holds` |
| `cmpInt` | `TMFw.W3b.cmpIntProg cmpNat.prog`, obs `cmpIntObs cmpNat.obs` | 2 | `RegS CReg` | `W3_cmpInt_holds` |
| `smallOpInt op` | `mul2Prog`, `mul3Prog`, `div2Prog`, `div3Prog` | 0/1/0/1 | `Reg2`/`M3R`/`Reg2`/`D3R` | `W3_smallOpInt_holds` |
| `attachSign isNeg` | `TMFw.W3b.attachProg isNeg` | 0 | `Reg2` | `W3_attachSign_holds` |
| `negInt` | `TMFw.W3b.negProg` | 0 | `Reg2` | `W3_negInt_holds` |
| `signInt` | `TMFw.W3b.signProg`, obs `signObs` | 0 | `Reg2` | `W3_signInt_holds` |

`W3_dec_amortised` is a pure cost fact about `decNat` (no program).
-/

namespace WP.Inst

open TMFw TMFw.Lib TMFw.Contracts

namespace addInt
abbrev m : ℕ := 4
abbrev R : Type := TMFw.W3b.RegA addNat.R subNat.R cmpNat.R
def r0 : R := (none, none, addNat.r0, subNat.r0, cmpNat.r0)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 3 m) (fun _ => Sym) R :=
  TMFw.W3b.addSubProg (by decide) (by decide) (by decide) cmpNat.obs addNat.prog subNat.prog
    cmpNat.prog false
theorem closed : prog.Closed :=
  TMFw.W3b.addSubProg_closed _ _ _ _ addNat.closed subNat.closed cmpNat.closed false
end addInt

namespace subInt
abbrev m : ℕ := 4
abbrev R : Type := TMFw.W3b.RegA addNat.R subNat.R cmpNat.R
def r0 : R := (none, none, addNat.r0, subNat.r0, cmpNat.r0)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 3 m) (fun _ => Sym) R :=
  TMFw.W3b.addSubProg (by decide) (by decide) (by decide) cmpNat.obs addNat.prog subNat.prog
    cmpNat.prog true
theorem closed : prog.Closed :=
  TMFw.W3b.addSubProg_closed _ _ _ _ addNat.closed subNat.closed cmpNat.closed true
end subInt

namespace cmpInt
abbrev m : ℕ := cmpNat.m
abbrev R : Type := TMFw.W3b.RegS cmpNat.R
def r0 : R := (none, none, cmpNat.r0)
def obs : R → Ordering := TMFw.W3b.cmpIntObs cmpNat.obs
def prog : Prog (Loc 2 m) (fun _ => Sym) R := TMFw.W3b.cmpIntProg cmpNat.prog
theorem closed : prog.Closed :=
  ⟨trivial, trivial, TMFw.W3b.call_closed id (TMFw.W3b.lensSub cmpNat.R) cmpNat.closed, trivial,
    trivial⟩
end cmpInt

namespace smallOpInt
/-- Scratch count per operation. -/
abbrev m : SmallOp → ℕ
  | .mul2 => 0
  | .mul3 => 1
  | .div2 => 0
  | .div3 => 1
/-- Registers per operation. -/
abbrev R : SmallOp → Type
  | .mul2 => TMFw.W3b.Reg2
  | .mul3 => TMFw.W3b.M3R
  | .div2 => TMFw.W3b.Reg2
  | .div3 => TMFw.W3b.D3R
def r0 : (op : SmallOp) → R op
  | .mul2 => (none, none)
  | .mul3 => (none, none, 0)
  | .div2 => (none, none)
  | .div3 => (none, none, 0, false)
def obs (op : SmallOp) : R op → Unit := fun _ => ()
def prog : (op : SmallOp) → Prog (Loc 1 (m op)) (fun _ => Sym) (R op)
  | .mul2 => TMFw.W3b.mul2Prog
  | .mul3 => TMFw.W3b.mul3Prog
  | .div2 => TMFw.W3b.div2Prog
  | .div3 => TMFw.W3b.div3Prog
theorem closed : ∀ op, (prog op).Closed
  | .mul2 => TMFw.W3b.mul2Prog_closed
  | .mul3 => TMFw.W3b.mul3Prog_closed
  | .div2 => TMFw.W3b.div2Prog_closed
  | .div3 => TMFw.W3b.div3Prog_closed
end smallOpInt

namespace attachSign
abbrev m : ℕ := 0
abbrev R : Type := TMFw.W3b.Reg2
def r0 : R := (none, none)
def obs : R → Unit := fun _ => ()
def prog (isNeg : Bool) : Prog (Loc 1 m) (fun _ => Sym) R := TMFw.W3b.attachProg isNeg
theorem closed (isNeg : Bool) : (prog isNeg).Closed := by
  simp [prog, Prog.Closed, Prog.FreeBelow, TMFw.W3b.attachProg]
end attachSign

namespace negInt
abbrev m : ℕ := 0
abbrev R : Type := TMFw.W3b.Reg2
def r0 : R := (none, none)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 1 m) (fun _ => Sym) R := TMFw.W3b.negProg
theorem closed : prog.Closed := by
  simp [prog, Prog.Closed, Prog.FreeBelow, TMFw.W3b.negProg]
end negInt

namespace signInt
abbrev m : ℕ := 0
abbrev R : Type := TMFw.W3b.Reg2
def r0 : R := (none, none)
def obs : R → Ordering := TMFw.W3b.signObs
def prog : Prog (Loc 1 m) (fun _ => Sym) R := TMFw.W3b.signProg
theorem closed : prog.Closed := by
  simp [prog, Prog.Closed, Prog.FreeBelow, TMFw.W3b.signProg]
end signInt

#assert_std_axioms addInt.closed subInt.closed cmpInt.closed smallOpInt.closed attachSign.closed
  negInt.closed signInt.closed

end WP.Inst
