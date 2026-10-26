import WP.W9fF.Main
import WP.W9fN.Main
import WP.W9fNF.Prog
import WP.F9.InstW5
import WP.Inst.W6a

/-!
# WP.W9f.ConcreteOps — the column cores on the shared instances

The concrete fwdCore (S1, `WP.W9fF.mainProg`) and nyqCore (S2, `WP.W9fN.nyqProg` with the Nyquist
finish `WP.W9fNF.finishProg`). They are the witness programs of `W9f_fwdCore_holds`,
`W9f_nyqCore_of_finish` and `W9f_nyqFinish_holds`, with every subroutine taken from the shared
concrete instances (`WP.Inst` and `WP.F9`).

| op | program | from |
|---|---|---|
| `add`, `sub`, `neg` | `WP.Inst.addInt`, `subInt`, `negInt` | W3b (`WP.F9.InstB`) |
| `mul` | `WP.Inst.toomMul` (Toom-3) | W5 (`WP.F9.InstW5`) |
| `shl` | `WP.W9fOps.mulPow2Prog` on `copyNat`, `shlVar` | W9fOps, W3 |
| `sar` | `WP.W9fOps.shrFloorProg` on `copyNat`, `decNat`, `shrVar`, `incNat` | W9fOps, W3 |
| `le` | `WP.W9fOps.leIndProg` on `cmpNat` | W9fOps, W3 |
| `divR` | `WP.W9fDiv.w9Prog` on `WP.Inst.divRound` | W9fDiv, W6a (`WP.Inst.W6a`) |

* S1: `IFC : Inst 7 48 Unit` (44 scratch, registers `GReg opsF`), initial registers `rFC`.
* S2: `INC : Inst 8 48 Unit` (48 scratch, registers `GReg opsN × finKit.Reg`), initial registers
  `rNC`. The finish is `finInst : Inst 4 48 Unit` (24 scratch).
-/

namespace WP.W9f.ConcreteOps

open TMFw TMFw.Lib TMFw.Contracts WP.W7k2

/-! ## The ops shared by both cores -/

/-- `shl` registers. -/
abbrev shlR : Type := WP.W9fOps.RegM WP.Inst.copyNat.R WP.Inst.shlVar.R

/-- `z += a·2^|b|` (W9fOps `mulPow2` on W3 `copyNat`, `shlVar`). -/
def shlP : Prog (Loc 3 4) (fun _ => Sym) shlR :=
  WP.W9fOps.mulPow2Prog (by decide) (by decide) WP.Inst.copyNat.prog WP.Inst.shlVar.prog

def shlR0 : shlR := (none, none, WP.Inst.copyNat.r0, WP.Inst.shlVar.r0)

theorem shlP_closed : shlP.Closed :=
  WP.W9fOps.mulPow2Prog_closed _ _ WP.Inst.copyNat.closed WP.Inst.shlVar.closed

/-- `sar` registers. -/
abbrev sarR : Type :=
  WP.W9fOps.RegF WP.Inst.copyNat.R WP.Inst.decNat.R WP.Inst.shrVar.R WP.Inst.incNat.R

/-- `z += a >>> |b|` (W9fOps `shrFloor` on W3 `copyNat`, `decNat`, `shrVar`, `incNat`). -/
def sarP : Prog (Loc 3 4) (fun _ => Sym) sarR :=
  WP.W9fOps.shrFloorProg (by decide) (by decide) (by decide) (by decide) WP.Inst.copyNat.prog
    WP.Inst.decNat.prog WP.Inst.shrVar.prog WP.Inst.incNat.prog

def sarR0 : sarR :=
  (none, none, WP.Inst.copyNat.r0, WP.Inst.decNat.r0, WP.Inst.shrVar.r0, WP.Inst.incNat.r0)

theorem sarP_closed : sarP.Closed :=
  WP.W9fOps.shrFloorProg_closed _ _ _ _ WP.Inst.copyNat.closed WP.Inst.decNat.closed
    WP.Inst.shrVar.closed WP.Inst.incNat.closed

/-- `le` registers. -/
abbrev leR : Type := WP.W9fOps.RegL WP.Inst.cmpNat.R

/-- `z += [a ≤ b]` (W9fOps `leInd` on W3 `cmpNat`). -/
def leP : Prog (Loc 3 4) (fun _ => Sym) leR :=
  WP.W9fOps.leIndProg (by decide) WP.Inst.cmpNat.obs WP.Inst.cmpNat.prog

def leR0 : leR := (none, none, WP.Inst.cmpNat.r0)

theorem leP_closed : leP.Closed := WP.W9fOps.leIndProg_closed _ _ WP.Inst.cmpNat.closed

/-- `divR` registers. -/
abbrev divRR : Type := WP.W9fDiv.FReg WP.Inst.divRound.R

/-- `z += divRoundRatInt a b` (W9fDiv on W6a `divRound`). -/
def divP : Prog (Loc 3 6) (fun _ => Sym) divRR := WP.W9fDiv.w9Prog WP.Inst.divRound.prog

def divR0 : divRR := (none, none, WP.Inst.divRound.r0)

theorem divP_closed : divP.Closed := WP.W9fDiv.w9Prog_closed _ WP.Inst.divRound.closed

/-! ## S1: the forward column core -/

/-- S1's op table. -/
def opsF : WP.W9fF.Op → WP.W9fF.IL.OpImpl
  | .add => ⟨WP.Inst.addInt.m, by decide, WP.Inst.addInt.R, WP.Inst.addInt.prog⟩
  | .sub => ⟨WP.Inst.subInt.m, by decide, WP.Inst.subInt.R, WP.Inst.subInt.prog⟩
  | .mul => ⟨8, by decide, WP.Inst.toomSubs.σ, WP.Inst.toomMul⟩
  | .shl => ⟨4, by decide, shlR, shlP⟩
  | .sar => ⟨4, by decide, sarR, sarP⟩
  | .le => ⟨4, by decide, leR, leP⟩
  | .divR => ⟨6, by decide, divRR, divP⟩

/-- Initial registers of S1's ops. -/
def opsFR0 : (o : WP.W9fF.Op) → (opsF o).R
  | .add => WP.Inst.addInt.r0
  | .sub => WP.Inst.subInt.r0
  | .mul => WP.Inst.toomR0
  | .shl => shlR0
  | .sar => sarR0
  | .le => leR0
  | .divR => divR0

theorem goodF {I : WP.W9fF.IL.OpImpl} (h1 : I.P.Closed) (h2 : Finite I.R) (h3 : Nonempty I.R) :
    I.Good :=
  And.intro h1 (And.intro h2 h3)

theorem opsF_good : ∀ o, (opsF o).Good
  | .add => goodF WP.Inst.addInt.closed (inferInstance : Finite WP.Inst.addInt.R)
      ⟨WP.Inst.addInt.r0⟩
  | .sub => goodF WP.Inst.subInt.closed (inferInstance : Finite WP.Inst.subInt.R)
      ⟨WP.Inst.subInt.r0⟩
  | .mul => goodF WP.Inst.toomMul_closed (inferInstance : Finite WP.Inst.toomSubs.σ)
      ⟨WP.Inst.toomR0⟩
  | .shl => goodF shlP_closed (inferInstance : Finite shlR) ⟨shlR0⟩
  | .sar => goodF sarP_closed (inferInstance : Finite sarR) ⟨sarR0⟩
  | .le => goodF leP_closed (inferInstance : Finite leR) ⟨leR0⟩
  | .divR => goodF divP_closed (inferInstance : Finite divRR) ⟨divR0⟩

/-- **S1, the forward column core**: `WP.W9fF.mainProg` on the concrete ops (`Loc 7 44`). -/
def IFC : Inst 7 48 Unit :=
  ⟨44, WP.W9fF.IL.GReg opsF, fun _ => (), WP.W9fF.mainProg opsF, by decide,
    WP.W9fF.finite_GReg opsF opsF_good, ⟨((none, .eq), opsFR0)⟩,
    WP.W9fF.mainProg_closed opsF (fun o => (opsF_good o).1)⟩

/-- Initial registers of S1. -/
def rFC : IFC.R := ((none, .eq), opsFR0)

/-! ## S2: the Nyquist column core -/

/-- S2's op table (the same programs, as `WP.W9fN.IL.OpImpl`). -/
def opsN : WP.W9fN.Op → WP.W9fN.IL.OpImpl
  | .add => ⟨WP.Inst.addInt.m, by decide, WP.Inst.addInt.R, WP.Inst.addInt.prog⟩
  | .sub => ⟨WP.Inst.subInt.m, by decide, WP.Inst.subInt.R, WP.Inst.subInt.prog⟩
  | .mul => ⟨8, by decide, WP.Inst.toomSubs.σ, WP.Inst.toomMul⟩
  | .shl => ⟨4, by decide, shlR, shlP⟩
  | .sar => ⟨4, by decide, sarR, sarP⟩
  | .le => ⟨4, by decide, leR, leP⟩
  | .divR => ⟨6, by decide, divRR, divP⟩

/-- Initial registers of S2's ops. -/
def opsNR0 : (o : WP.W9fN.Op) → (opsN o).R
  | .add => WP.Inst.addInt.r0
  | .sub => WP.Inst.subInt.r0
  | .mul => WP.Inst.toomR0
  | .shl => shlR0
  | .sar => sarR0
  | .le => leR0
  | .divR => divR0

theorem goodN {I : WP.W9fN.IL.OpImpl} (h1 : I.P.Closed) (h2 : Finite I.R) (h3 : Nonempty I.R) :
    I.Good :=
  And.intro h1 (And.intro h2 h3)

theorem opsN_good : ∀ o, (opsN o).Good
  | .add => goodN WP.Inst.addInt.closed (inferInstance : Finite WP.Inst.addInt.R)
      ⟨WP.Inst.addInt.r0⟩
  | .sub => goodN WP.Inst.subInt.closed (inferInstance : Finite WP.Inst.subInt.R)
      ⟨WP.Inst.subInt.r0⟩
  | .mul => goodN WP.Inst.toomMul_closed (inferInstance : Finite WP.Inst.toomSubs.σ)
      ⟨WP.Inst.toomR0⟩
  | .shl => goodN shlP_closed (inferInstance : Finite shlR) ⟨shlR0⟩
  | .sar => goodN sarP_closed (inferInstance : Finite sarR) ⟨sarR0⟩
  | .le => goodN leP_closed (inferInstance : Finite leR) ⟨leR0⟩
  | .divR => goodN divP_closed (inferInstance : Finite divRR) ⟨divR0⟩

/-- The Nyquist finish's subroutines: W3 `subInt`, `addInt`, `negInt`; W9fOps `shrFloor`. -/
def finKit : WP.W9fNF.Kit :=
  ⟨WP.Inst.subInt.m, WP.Inst.addInt.m, WP.Inst.negInt.m, 4, WP.Inst.subInt.R, WP.Inst.addInt.R,
    WP.Inst.negInt.R, sarR, by decide, by decide, by decide, by decide, WP.Inst.subInt.prog,
    WP.Inst.addInt.prog, WP.Inst.negInt.prog, sarP⟩

def finR0 : finKit.Reg :=
  (none, WP.Inst.subInt.r0, WP.Inst.addInt.r0, WP.Inst.negInt.r0, sarR0)

theorem finite_finReg : Finite finKit.Reg := by
  show Finite (Option Sym × (WP.Inst.subInt.R × (WP.Inst.addInt.R × (WP.Inst.negInt.R × sarR))))
  infer_instance

/-- **The Nyquist finish** (`WP.W9fNF.finishProg`, `Loc 4 24`). -/
def finInst : Inst 4 48 Unit :=
  ⟨24, finKit.Reg, fun _ => (), WP.W9fNF.finishProg finKit, by decide, finite_finReg, ⟨finR0⟩,
    WP.W9fNF.finishProg_closed finKit WP.Inst.subInt.closed WP.Inst.addInt.closed
      WP.Inst.negInt.closed sarP_closed⟩

theorem finite_INR : Finite (WP.W9fN.IL.GReg opsN × finKit.Reg) := by
  haveI : ∀ o, Finite (opsN o).R := fun o => (opsN_good o).2.1
  haveI := finite_finReg
  infer_instance

/-- **S2, the Nyquist column core**: `WP.W9fN.nyqProg` on the concrete ops and finish
(`Loc 8 48`). -/
def INC : Inst 8 48 Unit :=
  ⟨48, WP.W9fN.IL.GReg opsN × finInst.R, fun _ => (), WP.W9fN.nyqProg opsN finInst, le_rfl,
    finite_INR, ⟨(((none, .eq), opsNR0), finR0)⟩,
    WP.W9fN.nyqProg_closed opsN (fun o => (opsN_good o).1) finInst⟩

/-- Initial registers of S2. -/
def rNC : INC.R := (((none, .eq), opsNR0), finR0)

/-! ## Register normalization (for runners)

IntLang keeps the op registers in a dependent function `(o : Op) → (I o).R` and updates it with
`Function.update`. On a long run the closure chain grows: each lookup walks it, and the
interpreter's recursion overflows. `normIF` and `normIN` rebuild that function from its seven
values. They are the identity (`normIF_eq`, `normIN_eq`), so a runner may apply them between steps
(`WP.W9f.RunR.runTabledR`). -/

/-- S1's op registers from their values (no closure chain). -/
@[noinline] def mkPiF (a : WP.Inst.addInt.R) (s : WP.Inst.subInt.R) (m : WP.Inst.toomSubs.σ)
    (l : shlR) (r : sarR) (e : leR) (d : divRR) : (o : WP.W9fF.Op) → (opsF o).R
  | .add => a
  | .sub => s
  | .mul => m
  | .shl => l
  | .sar => r
  | .le => e
  | .divR => d

/-- S1's registers with the op registers rebuilt. -/
def normIF (v : IFC.R) : IFC.R :=
  (v.1, mkPiF (v.2 .add) (v.2 .sub) (v.2 .mul) (v.2 .shl) (v.2 .sar) (v.2 .le) (v.2 .divR))

theorem normIF_eq (v : IFC.R) : normIF v = v := by
  obtain ⟨a, f⟩ := v
  refine Prod.ext rfl ?_
  funext o
  cases o <;> rfl

/-- S2's op registers from their values (no closure chain). -/
@[noinline] def mkPiN (a : WP.Inst.addInt.R) (s : WP.Inst.subInt.R) (m : WP.Inst.toomSubs.σ)
    (l : shlR) (r : sarR) (e : leR) (d : divRR) : (o : WP.W9fN.Op) → (opsN o).R
  | .add => a
  | .sub => s
  | .mul => m
  | .shl => l
  | .sar => r
  | .le => e
  | .divR => d

/-- S2's registers with the op registers rebuilt. -/
def normIN (v : INC.R) : INC.R :=
  ((v.1.1, mkPiN (v.1.2 .add) (v.1.2 .sub) (v.1.2 .mul) (v.1.2 .shl) (v.1.2 .sar) (v.1.2 .le)
    (v.1.2 .divR)), v.2)

theorem normIN_eq (v : INC.R) : normIN v = v := by
  obtain ⟨⟨a, f⟩, b⟩ := v
  refine Prod.ext (Prod.ext rfl ?_) rfl
  funext o
  cases o <;> rfl

#assert_std_axioms shlP_closed sarP_closed leP_closed divP_closed opsF_good opsN_good
  finite_finReg finite_INR normIF_eq normIN_eq

end WP.W9f.ConcreteOps
