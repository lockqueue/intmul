import WP.W9sp.Main
import WP.Inst.W3

/-!
# WP.W9sp.Concrete — concrete program for the `W9_splitPack` kernel

`W9_splitPack_holds` takes its W3 subroutines as a `Kit` extracted from `W3_all`. Here the kit is
filled with the shared instances `WP.Inst.*` (copyNat, dropNat, splitAt, shlConst 2, shlVar,
isZeroNat, decNat), and `progC = (prog kitC).mapStk eH` is exactly the witness of
`W9_splitPack_holds` at that kit.
-/

namespace WP.W9sp.Concrete

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- The W3 instances of the kit, from `WP.Inst.W3`. -/
def kitC : Kit :=
  ⟨⟨WP.Inst.copyNat.m, WP.Inst.copyNat.R, WP.Inst.copyNat.obs, WP.Inst.copyNat.prog, by decide,
      inferInstance, ⟨WP.Inst.copyNat.r0⟩, WP.Inst.copyNat.closed⟩,
    ⟨WP.Inst.dropNat.m, WP.Inst.dropNat.R, WP.Inst.dropNat.obs, WP.Inst.dropNat.prog, by decide,
      inferInstance, ⟨WP.Inst.dropNat.r0⟩, WP.Inst.dropNat.closed⟩,
    ⟨WP.Inst.splitAt.m, WP.Inst.splitAt.R, WP.Inst.splitAt.obs, WP.Inst.splitAt.prog, by decide,
      inferInstance, ⟨WP.Inst.splitAt.r0⟩, WP.Inst.splitAt.closed⟩,
    ⟨WP.Inst.shlConst.m, WP.Inst.shlConst.R, WP.Inst.shlConst.obs, WP.Inst.shlConst.prog 2, by decide,
      inferInstance, ⟨WP.Inst.shlConst.r0⟩, WP.Inst.shlConst.closed 2⟩,
    ⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.obs, WP.Inst.shlVar.prog, by decide,
      inferInstance, ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩,
    ⟨WP.Inst.isZeroNat.m, WP.Inst.isZeroNat.R, WP.Inst.isZeroNat.obs, WP.Inst.isZeroNat.prog,
      by decide, inferInstance, ⟨WP.Inst.isZeroNat.r0⟩, WP.Inst.isZeroNat.closed⟩,
    ⟨WP.Inst.decNat.m, WP.Inst.decNat.R, WP.Inst.decNat.obs, WP.Inst.decNat.prog, by decide,
      inferInstance, ⟨WP.Inst.decNat.r0⟩, WP.Inst.decNat.closed⟩⟩

/-- Scratch count of the `W9_splitPack_holds` witness. -/
abbrev mC : ℕ := nS

/-- Registers of the witness. -/
abbrev RC : Type := kitC.Reg

/-- Initial registers: the symbol register and every instance's initial registers. -/
def r0C : RC :=
  (none, WP.Inst.copyNat.r0, WP.Inst.dropNat.r0, WP.Inst.splitAt.r0, WP.Inst.shlConst.r0,
    WP.Inst.shlVar.r0, WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0)

/-- **The concrete splitPack program**: the witness of `W9_splitPack_holds` at `kitC`. -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC := (prog kitC).mapStk eH

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed := closed_mapStk_eH (prog_closed kitC)

instance instFiniteRC : Finite RC := kitC.finite_Reg

instance instNonemptyRC : Nonempty RC := ⟨r0C⟩

#assert_std_axioms hmC closedC

end WP.W9sp.Concrete
