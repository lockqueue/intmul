import WP.W7k3.Concrete
import WP.W7sc.Prog

/-!
# WP.W7k3.ConcreteStd — the `stdChar` kernel with concrete subroutines (Phase F)

`WP.W7sc.W7_stdChar_holds` (`WP.W7sc`) hides its program `WP.W7sc.scProg I neg` inside `∃`. Here it is
instantiated with the **full concrete bundle** `KIfull`: the series-level bundle `KIc`
(`WP.W7k3.Concrete`) with
* `pi := WP.Inst.piScaled.inst` (concrete `W7_piScaled` from `WP.Inst.W7k1`);
* `sc := serC SK.cos`, `ss := serC SK.sin` (the concrete series sub-kernel).

Exports: `KIfull`, `mC = 16`, `RC = KIfull.R`, `r0C`, `progC neg = WP.W7sc.scProg KIfull neg`,
`hmC`, `closedC`, and the instances `sfC`, `stC : Inst 4 16 Unit` (`neg = false / true`, the
pre- and post-twiddle `stdChar` of the table builder). Runs: `WP.W7k3.ConcreteStdRun`.
-/

namespace WP.W7k3.ConcreteStd

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3 WP.W7k3.Concrete

/-- **The full concrete bundle** of the `stdChar` kernel. -/
def KIfull : KI := { KIc with pi := WP.Inst.piScaled.inst, sc := serC SK.cos, ss := serC SK.sin }

/-- Scratch count of the `stdChar` kernel. -/
abbrev mC : ℕ := 16

/-- Register type of the `stdChar` kernel. -/
abbrev RC : Type := KIfull.R

/-- Initial registers. -/
def r0C : RC :=
  (none, WP.Inst.copyNat.r0, WP.Inst.dropNat.r0, WP.Inst.isZeroNat.r0, WP.Inst.decNat.r0,
    WP.Inst.incNat.r0, WP.Inst.addInt.r0, WP.Inst.toomR0, dvR0, WP.Inst.addNat.r0,
    WP.Inst.shlConst.r0, WP.Inst.shlVar.r0, WP.Inst.negInt.r0, WP.Inst.piScaled.r0,
    Concrete.r0C, Concrete.r0C)

/-- **The `stdChar` program** at sign `neg` (exactly the program of `W7_stdChar_holds`, with the
concrete subroutines). -/
def progC (neg : Bool) : Prog (Loc 4 mC) (fun _ => Sym) RC := WP.W7sc.scProg KIfull neg

theorem hmC : mC ≤ 16 := le_rfl

theorem closedC (neg : Bool) : (progC neg).Closed := WP.W7sc.scProg_closed KIfull neg

/-- The `stdChar` kernel at sign `neg` as an instance (`= WP.W7sc.scInst KIfull neg`). -/
def stdInstC (neg : Bool) : Inst 4 16 Unit :=
  ⟨16, KIfull.R, fun _ => (), progC neg, le_rfl, KIfull.R_finite, KIfull.R_nonempty, closedC neg⟩

/-- Pre-twiddles (`neg = false`). -/
def sfC : Inst 4 16 Unit := stdInstC false

/-- Post-twiddles (`neg = true`). -/
def stC : Inst 4 16 Unit := stdInstC true

#assert_std_axioms hmC closedC

end WP.W7k3.ConcreteStd
