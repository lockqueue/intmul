import WP.W9c.ConcreteKit
import WP.W9c.BlockPackFin
import WP.W9c.RowMain

/-!
# WP.W9c.Concrete — concrete program for the spread-row kernel `W9_spreadRow`

The witness of `W9_spreadRow_of_parts` is `rowMainProg hd tp sp zp pk up wn ce mu cp dr iz ic dc
ad sb sa` (RowMain) `= (rowProg (mkRKit hd tp sp zp pk ps cp dr iz ic dc ad sb sa)).mapStk eLB`, with
`ps = passInst pk up wn ce mu cp dr iz dc`. Here every instance is concrete (`WP.W9c.ConcreteKit`):

* row kernels `hdI tpI spI zpI`; block pack `pkI = bpProg bpK` (piece A, its `Kit` filled with
  `WP.Inst.*`); unpack `upI` (piece B); window / cycEmit `wnI ceI` (piece C, with `WP.Inst.addInt`);
  the W5 multiplier `WP.Inst.mulInst`; W3 `cpI drI izI icI dcI adI sbI saI`.

`progC` is that program; `mC = 40`, `RC = RSig …` (the product of the instances' registers),
`r0C` their initial registers.
-/

namespace WP.W9c.Concrete

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## Block pack (piece A) -/

/-- The block-pack kit: copy, drop, inc, dec, cmp, add, sub, shlVar, shrVar, shrConst 1, splitAt,
concatAt, subInt. -/
abbrev bpK : BlockPack.Kit := ⟨cpI, drI, icI, dcI, cmI, adI, sbI, shlI, shrI, shr1I, saI, caI, siI⟩

def pkR0 : bpK.Reg :=
  (none, none, WP.Inst.copyNat.r0, WP.Inst.dropNat.r0, WP.Inst.incNat.r0, WP.Inst.decNat.r0,
    WP.Inst.cmpNat.r0, WP.Inst.addNat.r0, WP.Inst.subNat.r0, WP.Inst.shlVar.r0, WP.Inst.shrVar.r0,
    WP.Inst.shrConst.r0, WP.Inst.splitAt.r0, WP.Inst.concatAt.r0, WP.Inst.subInt.r0)

abbrev pkI : Inst 6 24 Unit :=
  ⟨8, bpK.Reg, fun _ => (), BlockPack.bpProg bpK, by decide, BlockPack.Kit.finite bpK, ⟨pkR0⟩,
    BlockPack.bpProg_closed bpK⟩

/-! ## The pass and the row kit -/

/-- The coordinate pass. -/
abbrev psI : Inst 10 24 Unit := passInst pkI upI wnI ceI WP.Inst.mulInst cpI drI izI dcI

def psR0 : psI.R :=
  (none, pkR0, upR0, wnR0, ceR0, WP.Inst.toomR0, WP.Inst.copyNat.r0, WP.Inst.dropNat.r0,
    WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0)

/-- The row kit. -/
abbrev KC : RKit (RSig hdI tpI spI zpI pkI psI cpI drI izI icI dcI adI sbI saI) :=
  mkRKit hdI tpI spI zpI pkI psI cpI drI izI icI dcI adI sbI saI

/-! ## Concrete witness exports -/

/-- Scratch count of the witness. -/
abbrev mC : ℕ := 40

/-- Registers of the witness. -/
abbrev RC : Type := RSig hdI tpI spI zpI pkI psI cpI drI izI icI dcI adI sbI saI

/-- Initial registers: every instance's initial registers. -/
def r0C : RC :=
  (none, none, none, none, pkR0, psR0, WP.Inst.copyNat.r0, WP.Inst.dropNat.r0,
    WP.Inst.isZeroNat.r0, WP.Inst.incNat.r0, WP.Inst.decNat.r0, WP.Inst.addNat.r0,
    WP.Inst.subNat.r0, WP.Inst.splitAt.r0)

/-- **The concrete spread-row program**: the witness of `W9_spreadRow_of_parts`
(`rowMainProg` applied to the instances) at the concrete instances. -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC :=
  rowMainProg hdI tpI spI zpI pkI upI wnI ceI WP.Inst.mulInst cpI drI izI icI dcI adI sbI saI

/-- `progC` unfolds to the row driver over the concrete kit. -/
theorem progC_eq : progC = (rowProg KC).mapStk eLB := rfl

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed := freeBelow_mapStk eLB (rowProg KC) 0 (rowProg_closed KC)

instance instFiniteRC : Finite RC := rsig_finite _ _ _ _ _ _ _ _ _ _ _ _ _ _

instance instNonemptyRC : Nonempty RC := ⟨r0C⟩

#assert_std_axioms progC_eq hmC closedC

end WP.W9c.Concrete
