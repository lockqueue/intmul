import WP.W9f.ConcreteP
import WP.W9f.ConcreteOps
import WP.W9fC.Prog

/-!
# WP.W9f.Concrete — the concrete column solver (the witness of `W9_columnSolve_of_cores`)

Concrete column-solver exports. `progC` is the witness program of `W9_columnSolve_of_cores`, which is
`(colProg K).mapStk toB`, written over a `PKit` in `WP.W9f.ConcreteP` (`colProg_eq` holds by `rfl`).
It uses the kit of concrete instances:
* S1 fwdCore `IFC` and S2 nyqCore `INC` (`WP.W9f.ConcreteOps`): `WP.W9fF.mainProg`, and
  `WP.W9fN.nyqProg` with the finish `WP.W9fNF.finishProg`. Every op comes from the shared instances.
* S4 moveEntries `moveC` (`WP.W9fM.moveEntriesProg`) and the comparator `cmpC` (`WP.Inst.cmpNat`).

`progC_eq_witness`: for any constants and specs, the program of `W9_columnSolve_of_cores` on the kit
`⟨IFC, INC, moveC, cmpC, …⟩` is `progC` (`rfl`).

S3, the columns stage (`W9_columns`), is `progColsC = WP.W9fC.colsProg … progC` (`mColsC`,
`RColsC`, `r0ColsC`, `hmColsC`, `closedColsC`). This is the witness of
`WP.W9fC.W9_columns_of_columnSolve`.

Runners: the IntLang cores keep their op registers in a dependent function that is updated with
`Function.update`. Run with `WP.W9f.RunR.runTabledR` and the identity register maps `normRC` and
`normColsC`.
-/

namespace WP.W9f.Concrete

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 WP.W9f WP.W9f.ConcreteP
  WP.W9f.ConcreteOps

/-- Scratch count of the witness. -/
abbrev mC : ℕ := 64

/-- Registers of the witness: symbol register, fwdCore, nyqCore, mover, comparator. -/
abbrev RC : Type := RP IFC INC

/-- Initial registers. -/
def r0C : RC := r0P IFC INC rFC rNC

/-- **The concrete column solver.** -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC := progP IFC INC

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed := closedP IFC INC

/-- **Register normalization** for runners (`WP.W9f.RunR.runTabledR`): rebuilds the cores' IntLang
op registers (`normIF`, `normIN`). It is the identity (`normRC_eq`). -/
def normRC (v : RC) : RC := (v.1, normIF v.2.1, normIN v.2.2.1, v.2.2.2)

theorem normRC_eq (v : RC) : normRC v = v := by
  obtain ⟨a, b, c, d⟩ := v
  show (a, normIF b, normIN c, d) = (a, b, c, d)
  exact Prod.ext rfl (Prod.ext (normIF_eq b) (Prod.ext (normIN_eq c) rfl))

/-- **The `_holds` witness is `progC`**: for any constants and specs of the kit
`⟨IFC, INC, moveC, cmpC, …⟩`, the program of `W9_columnSolve_of_cores` is `progC`. -/
theorem progC_eq_witness {Mul : ℕ → ℕ} (CF CN CM CC : ℕ) (hF : SpecFwd Mul IFC CF)
    (hN : SpecNyq Mul INC CN) (hM : SpecMove moveC CM) (hC : SpecCmpNat cmpC CC) :
    (colProg (⟨IFC, INC, moveC, cmpC, CF, CN, CM, CC, hF, hN, hM, hC⟩ : Kit Mul)).mapStk toB =
      progC :=
  progP_eq_witness IFC INC CF CN CM CC hF hN hM hC

/-! ## S3: the columns stage (`W9_columns`) -/

/-- Scratch count of the columns stage. The witness of `WP.W9fC.W9_columns_of_columnSolve` has
`max mc 7` scratch stacks, with `mc = mC`. -/
abbrev mColsC : ℕ := max mC 7

/-- Registers of the columns stage: the column solver's, and the driver's symbol register. -/
abbrev RColsC : Type := RC × Option Sym

/-- Initial registers of the columns stage. -/
def r0ColsC : RColsC := (r0C, none)

/-- **The concrete `W9_columns` stage**: S3's driver `WP.W9fC.colsProg` on `progC`. This is the
witness program of `WP.W9fC.W9_columns_of_columnSolve` for the column solver `progC`. -/
def progColsC : Prog (BLoc mColsC) (fun _ => Sym) RColsC :=
  WP.W9fC.colsProg (le_max_right mC 7) (le_max_left mC 7) progC

theorem hmColsC : mColsC ≤ w9Scratch := by decide

theorem closedColsC : progColsC.Closed :=
  WP.W9fC.colsProg_closed (le_max_right mC 7) (le_max_left mC 7) closedC

/-- Register normalization of the columns stage. It is the identity (`normColsC_eq`). -/
def normColsC (v : RColsC) : RColsC := (normRC v.1, v.2)

theorem normColsC_eq (v : RColsC) : normColsC v = v := by
  obtain ⟨a, b⟩ := v
  show (normRC a, b) = (a, b)
  rw [normRC_eq]

#assert_std_axioms hmC closedC normRC_eq progC_eq_witness hmColsC closedColsC normColsC_eq

end WP.W9f.Concrete
