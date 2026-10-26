import WP.W9s.Main
import WP.F9.InstB

/-!
# WP.W9s.Concrete — the concrete synthetic FFT (the witness of `W9_synFFT_holds`)

Concrete synthetic-FFT exports. `W9_synFFT_holds (ha : W3_addInt) (hs : W3_subInt)` takes its subroutines
through `exists_inst`; here the kit is built from the shared instances instead:
* `iAdd` / `iSub`: the W7k2 bundles of `WP.Inst.addInt` / `WP.Inst.subInt` (`WP.F9.InstB`);
* `iInc`: the bundle of `WP.Inst.incNat` (`WP.Inst.W3`), used by the rounding halving `halveRound`.

`progC = (synTop kitC).mapStk eB` is exactly the witness program of `W9_synFFT_holds` for this kit
(`m = 20` scratch stacks, registers `kitC.R`). `closedC` is the `_holds` closedness term; its
`HalveSpec` argument comes from `specInc`, the `W3_incNat` body for `iInc` (as in `incNat.ok`).
-/

namespace WP.W9s.Concrete

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 WP.W9s WP.W9s.Top Computability

/-- The `W3_addInt` instance as a W7k2 bundle. -/
def iAdd : Inst 3 4 Unit :=
  ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.obs, WP.Inst.addInt.prog, by decide,
    inferInstance, ⟨WP.Inst.addInt.r0⟩, WP.Inst.addInt.closed⟩

/-- The `W3_subInt` instance as a W7k2 bundle. -/
def iSub : Inst 3 4 Unit :=
  ⟨WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.obs, WP.Inst.subInt.prog, by decide,
    inferInstance, ⟨WP.Inst.subInt.r0⟩, WP.Inst.subInt.closed⟩

/-- The `W3_incNat` instance as a W7k2 bundle. -/
def iInc : Inst 1 4 Unit :=
  ⟨WP.Inst.incNat.m, WP.Inst.incNat.R, WP.Inst.incNat.obs, WP.Inst.incNat.prog, by decide,
    inferInstance, ⟨WP.Inst.incNat.r0⟩, WP.Inst.incNat.closed⟩

/-- The kit: adder, subtracter, rounding halving from `incNat`. -/
def kitC : Kit := mkKit iAdd iSub iInc

/-- Scratch count of the witness. -/
abbrev mC : ℕ := 20

/-- Registers of the witness: symbol, adder, subtracter, halving (`HReg iInc`). -/
abbrev RC : Type := kitC.R

/-- Initial registers. -/
def r0C : RC := (none, WP.Inst.addInt.r0, WP.Inst.subInt.r0, (none, none, WP.Inst.incNat.r0))

/-- **The witness program of `W9_synFFT_holds`** with the shared instances. -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC := (synTop kitC).mapStk eB

theorem hmC : mC ≤ w9Scratch := by decide

/-- The `W3_incNat` body for `iInc` (constant `9`, as in `WP.Inst.incNat.ok`). -/
theorem specInc : SpecInc iInc 9 := by
  intro a rx S hrx hx
  refine Runs.of_eval fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval (k := (.inl 0 : Loc 1 iInc.m)) (t := .inr ⟨0, by decide⟩)
    (by decide) [] v (encodeNat a) rx S hrx hx
  refine ⟨some .mark, c, ?_, trivial, by omega⟩
  rw [natSyms, encodeNat_succ]
  exact e

/-- The halving subroutine of `kitC` meets `HalveSpec`. -/
theorem halveSpecC : HalveSpec kitC.Hp (9 + 20) := halveSpec_mk specInc

theorem closedC : progC.Closed := freeBelow_mapStk eB _ 0 (synTop_closed halveSpecC)

#assert_std_axioms hmC specInc halveSpecC closedC

end WP.W9s.Concrete
