import WP.W7k2.B.Top
import WP.W7k2.ConcreteRun
import WP.F9.InstW5
import WP.W7k1.Concrete
import WP.W7k3.ConcreteStd
import WP.W7k3t.Concrete
import WP.W7k3.ConcreteC0C1

/-!
# WP.W7k2.Concrete — the table builder instantiated with concrete subroutines

The `W7_buildTablesRef_holds` witness is `buildProg I` (B/Top.lean) for an instance bundle `I : BI`
(B/Base.lean, twenty contract instances). Here every instance is a plain def:

| field | contract | concrete instance |
|---|---|---|
| `cp dr iz dc ic ad s1 r1 sv cm` | W3 unsigned | `WP.Inst.{copyNat, dropNat, isZeroNat, decNat, incNat, addNat, shlConst 1, shrConst 1, shlVar, cmpNat}` |
| `ai` | `W3_addInt` | `WP.Inst.addInt` (WP.F9.InstB) |
| `mu` | `W5_mulAt` | `WP.Inst.mulInst` (Toom-3, WP.F9.InstW5) |
| `dm` | `W6a_divModNat` | `WP.W7k2.ConcreteRun.divI` (W6a long division over `WP.Inst.subNat`) |
| `cr` | `W7_colRecip` | `crProg crJ` (WP.W7k2.ConcreteRun) |
| `pi ln` | `W7_piScaled`, `W7_log2Scaled` | `WP.W7k1.Concrete.{Pi,Ln}.instC` |
| `sf st` | `W7_stdChar false/true` | `WP.W7k3.ConcreteStd.{sfC, stC}` (W7sc over the concrete series bundle) |
| `tp` | `W7_sincGaussianTap` | `WP.W7k3t.Concrete.tapInstC` (W9sq; `= tapInst IC`) |
| `cc` | `W7_c0c1` | `WP.W7k3.ConcreteC0C1.c0c1InstC` (W7k3c over the concrete `CIc`) |

The layout is the W7 contract's `Loc 4 32` (named `0 TR, 1 L, 2 p, 3 K`), not `BLoc`.
-/

namespace WP.W7k2.Concrete

open TMFw TMFw.Contracts WP.W7k2 WP.W7k2.ConcreteRun

/-! ## The concrete instances -/

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

def s1I : Inst 1 4 Unit :=
  ⟨WP.Inst.shlConst.m, WP.Inst.shlConst.R, WP.Inst.shlConst.obs, WP.Inst.shlConst.prog 1,
    by decide, inferInstance, ⟨WP.Inst.shlConst.r0⟩, WP.Inst.shlConst.closed 1⟩

def r1I : Inst 1 4 Unit :=
  ⟨WP.Inst.shrConst.m, WP.Inst.shrConst.R, WP.Inst.shrConst.obs, WP.Inst.shrConst.prog 1,
    by decide, inferInstance, ⟨WP.Inst.shrConst.r0⟩, WP.Inst.shrConst.closed 1⟩

def svI : Inst 2 4 Unit :=
  ⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.obs, WP.Inst.shlVar.prog, by decide,
    inferInstance, ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩

def cmI : Inst 2 4 Ordering :=
  ⟨WP.Inst.cmpNat.m, WP.Inst.cmpNat.R, WP.Inst.cmpNat.obs, WP.Inst.cmpNat.prog, by decide,
    inferInstance, ⟨WP.Inst.cmpNat.r0⟩, WP.Inst.cmpNat.closed⟩

def aiI : Inst 3 4 Unit :=
  ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.obs, WP.Inst.addInt.prog, by decide,
    inferInstance, ⟨WP.Inst.addInt.r0⟩, WP.Inst.addInt.closed⟩

def muI : Inst 3 8 Unit := WP.Inst.mulInst

def dmI : Inst 4 6 Unit := divI

theorem crReg_finite : Finite crJ.Reg := by
  haveI := crJ.copy.fin
  haveI := crJ.shl1.fin
  haveI := crJ.cmp.fin
  haveI := crJ.shlV.fin
  haveI := crJ.drop.fin
  haveI := crJ.div.fin
  exact inferInstance

def crI : Inst 6 16 Unit :=
  ⟨6, crJ.Reg, fun _ => (), crProg crJ, by decide, crReg_finite, ⟨crR0⟩, crProg_closed crJ⟩

/-! ## The bundle -/

/-- The builder's instance bundle, given the six W7 kernel instances (stdChar `false`/`true`, tap,
`c0c1`, `piScaled`, `log2Scaled`). -/
def BICof (sf st : Inst 4 16 Unit) (tp : Inst 8 16 Unit) (cc : Inst 5 16 Unit)
    (pi ln : Inst 2 16 Unit) : BI :=
  ⟨cpI, drI, izI, dcI, icI, adI, s1I, r1I, svI, cmI, aiI, muI, dmI, sf, st, tp, cc, crI, pi, ln⟩

/-- Its initial registers, given those of the six kernel instances. -/
def r0Of (sf st : Inst 4 16 Unit) (tp : Inst 8 16 Unit) (cc : Inst 5 16 Unit)
    (pi ln : Inst 2 16 Unit) (rsf : sf.R) (rst : st.R) (rtp : tp.R) (rcc : cc.R) (rpi : pi.R)
    (rln : ln.R) : (BICof sf st tp cc pi ln).R :=
  (none, WP.Inst.copyNat.r0, WP.Inst.dropNat.r0, WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0,
    WP.Inst.incNat.r0, WP.Inst.addNat.r0, WP.Inst.shlConst.r0, WP.Inst.shrConst.r0,
    WP.Inst.shlVar.r0, WP.Inst.cmpNat.r0, WP.Inst.addInt.r0, WP.Inst.toomR0,
    (none, false, (none, none, .eq), WP.Inst.subNat.r0), rsf, rst, rtp, rcc, crR0, rpi, rln)

/-- The bundle with the concrete `piScaled` / `log2Scaled` instances (W7k1). -/
def BICof4 (sf st : Inst 4 16 Unit) (tp : Inst 8 16 Unit) (cc : Inst 5 16 Unit) : BI :=
  BICof sf st tp cc WP.W7k1.Concrete.Pi.instC WP.W7k1.Concrete.Ln.instC

/-- The bundle with the concrete stdChar instances too (W7k3 / W7sc). -/
def BICof2 (tp : Inst 8 16 Unit) (cc : Inst 5 16 Unit) : BI :=
  BICof4 WP.W7k3.ConcreteStd.sfC WP.W7k3.ConcreteStd.stC tp cc

/-- Its initial registers, given those of `tp` and `cc`. -/
def r0Of2 (tp : Inst 8 16 Unit) (cc : Inst 5 16 Unit) (rtp : tp.R) (rcc : cc.R) :
    (BICof2 tp cc).R :=
  r0Of WP.W7k3.ConcreteStd.sfC WP.W7k3.ConcreteStd.stC tp cc WP.W7k1.Concrete.Pi.instC
    WP.W7k1.Concrete.Ln.instC WP.W7k3.ConcreteStd.r0C WP.W7k3.ConcreteStd.r0C rtp rcc
    WP.W7k1.Concrete.Pi.r0C WP.W7k1.Concrete.Ln.r0C

/-- The bundle with the concrete tap instance too (W7k3t). -/
def BICof1 (cc : Inst 5 16 Unit) : BI := BICof2 WP.W7k3t.Concrete.tapInstC cc

/-- Its initial registers, given those of `cc`. -/
def r0Of1 (cc : Inst 5 16 Unit) (rcc : cc.R) : (BICof1 cc).R :=
  r0Of2 WP.W7k3t.Concrete.tapInstC cc WP.W7k3t.Concrete.r0C rcc

/-! ## Concrete builder exports -/

/-- **The builder's instance bundle**, all twenty slots concrete. -/
def BIC : BI := BICof1 WP.W7k3.ConcreteC0C1.c0c1InstC

/-- Scratch stacks: the W7 contract's `W7.maxScratch`. -/
abbrev mC : ℕ := 32

/-- Registers of the witness. -/
abbrev RC : Type := BIC.R

/-- Initial registers. -/
def r0C : RC := r0Of1 WP.W7k3.ConcreteC0C1.c0c1InstC WP.W7k3.ConcreteC0C1.r0C

/-- **The witness program of `W7_buildTablesRef_holds`** (and of `W7_buildTables W7.snapshotSchedule`
via `W7_buildTables_of_ref`), over the concrete subroutines. Layout `Loc 4 32`. -/
def progC : Prog (Loc 4 mC) (fun _ => Sym) RC := buildProg BIC

theorem hmC : mC ≤ W7.maxScratch := le_rfl

theorem closedC : progC.Closed := buildProg_closed BIC

theorem finC : Finite RC := BIC.R_finite

/-! Aliases for the end-to-end machine execution test (`IntMulTM.Exec.TopRun`). -/

abbrev m7 : ℕ := mC
abbrev R7 : Type := RC
def r7 : R7 := r0C
def P7C : Prog (Loc 4 m7) (fun _ => Sym) R7 := progC
theorem hm7 : m7 ≤ 32 := le_rfl

#assert_std_axioms crReg_finite hmC closedC finC hm7

end WP.W7k2.Concrete
