import WP.Inst.W3
import WP.F9.InstW5
import WP.W9c.Unpack
import WP.W9c.Window
import WP.W9c.CycEmit
import WP.W9c.RowHdr
import WP.W9c.RowTaps
import WP.W9c.RowSplit
import WP.W9c.RowZip

/-!
# WP.W9c.ConcreteKit — concrete instance bundles of the spread-row kernel (Phase F)

Every subroutine of the `W9_spreadRow` concrete witness comes from the shared instance
modules. This file builds the W7k2-style bundles (`Inst n cap O`, all `abbrev`, so their register
types reduce for instance search), each with its initial registers:

| bundle | contract | program |
|---|---|---|
| `cpI drI izI icI dcI cmI adI sbI saI caI shlI shrI shr1I` | W3 | `WP.Inst.<c>.prog` (`shrConst 1`) |
| `aiI siI` | W3b `addInt`, `subInt` | `WP.Inst.addInt.prog`, `WP.Inst.subInt.prog` |
| `upI` | `W9c_unpack` | `Unp.unpackP uJ` (piece B), `m = 8` |
| `wnI` / `ceI` | `W9c_window` / `W9c_cycEmit` | `CK.winProg aiI` / `CK.cycProg aiI`, `m = 4` |
| `hdI tpI spI zpI` | row kernels | `RowHdr.hdrProg`, `RowTaps.tapsProg`, `RowSplit.splitProg`, `RowZip.zipProg` |
| `WP.Inst.mulInst` | `W5_mulAt` | `WP.Inst.toomMul` |
-/

namespace WP.W9c.Concrete

open TMFw TMFw.Contracts WP.W7k2

/-! ## W3 and W3b -/

abbrev cpI : Inst 2 4 Unit := ⟨WP.Inst.copyNat.m, WP.Inst.copyNat.R, WP.Inst.copyNat.obs,
  WP.Inst.copyNat.prog, by decide, inferInstance, ⟨WP.Inst.copyNat.r0⟩, WP.Inst.copyNat.closed⟩
abbrev drI : Inst 1 4 Unit := ⟨WP.Inst.dropNat.m, WP.Inst.dropNat.R, WP.Inst.dropNat.obs,
  WP.Inst.dropNat.prog, by decide, inferInstance, ⟨WP.Inst.dropNat.r0⟩, WP.Inst.dropNat.closed⟩
abbrev izI : Inst 1 4 Bool := ⟨WP.Inst.isZeroNat.m, WP.Inst.isZeroNat.R, WP.Inst.isZeroNat.obs,
  WP.Inst.isZeroNat.prog, by decide, inferInstance, ⟨WP.Inst.isZeroNat.r0⟩,
  WP.Inst.isZeroNat.closed⟩
abbrev icI : Inst 1 4 Unit := ⟨WP.Inst.incNat.m, WP.Inst.incNat.R, WP.Inst.incNat.obs,
  WP.Inst.incNat.prog, by decide, inferInstance, ⟨WP.Inst.incNat.r0⟩, WP.Inst.incNat.closed⟩
abbrev dcI : Inst 1 4 Unit := ⟨WP.Inst.decNat.m, WP.Inst.decNat.R, WP.Inst.decNat.obs,
  WP.Inst.decNat.prog, by decide, inferInstance, ⟨WP.Inst.decNat.r0⟩, WP.Inst.decNat.closed⟩
abbrev cmI : Inst 2 4 Ordering := ⟨WP.Inst.cmpNat.m, WP.Inst.cmpNat.R, WP.Inst.cmpNat.obs,
  WP.Inst.cmpNat.prog, by decide, inferInstance, ⟨WP.Inst.cmpNat.r0⟩, WP.Inst.cmpNat.closed⟩
abbrev adI : Inst 3 4 Unit := ⟨WP.Inst.addNat.m, WP.Inst.addNat.R, WP.Inst.addNat.obs,
  WP.Inst.addNat.prog, by decide, inferInstance, ⟨WP.Inst.addNat.r0⟩, WP.Inst.addNat.closed⟩
abbrev sbI : Inst 3 4 Unit := ⟨WP.Inst.subNat.m, WP.Inst.subNat.R, WP.Inst.subNat.obs,
  WP.Inst.subNat.prog, by decide, inferInstance, ⟨WP.Inst.subNat.r0⟩, WP.Inst.subNat.closed⟩
abbrev saI : Inst 3 4 Unit := ⟨WP.Inst.splitAt.m, WP.Inst.splitAt.R, WP.Inst.splitAt.obs,
  WP.Inst.splitAt.prog, by decide, inferInstance, ⟨WP.Inst.splitAt.r0⟩, WP.Inst.splitAt.closed⟩
abbrev caI : Inst 3 4 Unit := ⟨WP.Inst.concatAt.m, WP.Inst.concatAt.R, WP.Inst.concatAt.obs,
  WP.Inst.concatAt.prog, by decide, inferInstance, ⟨WP.Inst.concatAt.r0⟩,
  WP.Inst.concatAt.closed⟩
abbrev shlI : Inst 2 4 Unit := ⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.obs,
  WP.Inst.shlVar.prog, by decide, inferInstance, ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩
abbrev shrI : Inst 2 4 Unit := ⟨WP.Inst.shrVar.m, WP.Inst.shrVar.R, WP.Inst.shrVar.obs,
  WP.Inst.shrVar.prog, by decide, inferInstance, ⟨WP.Inst.shrVar.r0⟩, WP.Inst.shrVar.closed⟩
abbrev shr1I : Inst 1 4 Unit := ⟨WP.Inst.shrConst.m, WP.Inst.shrConst.R, WP.Inst.shrConst.obs,
  WP.Inst.shrConst.prog 1, by decide, inferInstance, ⟨WP.Inst.shrConst.r0⟩,
  WP.Inst.shrConst.closed 1⟩
abbrev aiI : Inst 3 4 Unit := ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.obs,
  WP.Inst.addInt.prog, by decide, inferInstance, ⟨WP.Inst.addInt.r0⟩, WP.Inst.addInt.closed⟩
abbrev siI : Inst 3 4 Unit := ⟨WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.obs,
  WP.Inst.subInt.prog, by decide, inferInstance, ⟨WP.Inst.subInt.r0⟩, WP.Inst.subInt.closed⟩

/-! ## Unpack (piece B), window and cycEmit (piece C) -/

/-- The unpack instances (`Unp.UInst`: split, inc, cmp, sub, drop, zero, dec, copy, shlV). -/
abbrev uJ : Unp.UInst := ⟨saI, icI, cmI, sbI, drI, izI, dcI, cpI, shlI⟩

def upR0 : Unp.UInst.Reg uJ :=
  (none, WP.Inst.splitAt.r0, WP.Inst.incNat.r0, WP.Inst.cmpNat.r0, WP.Inst.subNat.r0,
    WP.Inst.dropNat.r0, WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0, WP.Inst.copyNat.r0,
    WP.Inst.shlVar.r0)

abbrev upI : Inst 4 24 Unit :=
  ⟨8, Unp.UInst.Reg uJ, fun _ => (), Unp.unpackP uJ, by decide, inferInstance, ⟨upR0⟩,
    Unp.unpackP_closed uJ⟩

def wnR0 : CK.WR aiI.R := (none, WP.Inst.addInt.r0)

abbrev wnI : Inst 4 24 Unit :=
  ⟨4, CK.WR aiI.R, fun _ => (), CK.winProg aiI, by decide, inferInstance, ⟨wnR0⟩,
    CK.winProg_closed aiI⟩

def ceR0 : CK.CR aiI.R := (none, WP.Inst.addInt.r0)

abbrev ceI : Inst 3 24 Unit :=
  ⟨4, CK.CR aiI.R, fun _ => (), CK.cycProg aiI, by decide, inferInstance, ⟨ceR0⟩,
    CK.cycProg_closed aiI⟩

/-! ## Row kernels -/

abbrev hdI : Inst 9 24 Unit :=
  ⟨1, Option Sym, fun _ => (), RowHdr.hdrProg, by decide, inferInstance, ⟨none⟩,
    RowHdr.closed_hdrProg⟩
abbrev tpI : Inst 4 24 Unit :=
  ⟨3, Option Sym, fun _ => (), RowTaps.tapsProg, by decide, inferInstance, ⟨none⟩,
    RowTaps.closed_tapsProg⟩
abbrev spI : Inst 3 24 Unit :=
  ⟨1, Option Sym, fun _ => (), RowSplit.splitProg, by decide, inferInstance, ⟨none⟩,
    RowSplit.closed_splitProg⟩
abbrev zpI : Inst 3 24 Unit :=
  ⟨1, Option Sym, fun _ => (), RowZip.zipProg, by decide, inferInstance, ⟨none⟩,
    RowZip.closed_zipProg⟩

end WP.W9c.Concrete
