import WP.TapeConv.Main
import IntMulTM.Framework.Test.EndToEnd

/-!
# WP.TapeConv.Smoke — run the compiled converter and compare with `W9.tapeSyms` and the bound

The compiled `FinTM2` (`toFinTM2`, Mathlib's `TM2.step`) starts with `W7.tape W7.snapshotFormat
cSpec ++ rest` on `tr` and every scratch stack empty. On halting, `tr` must be exactly
`W9.tapeSyms cSpec ++ rest`, and the step count must be at most the proved bound
`32·(|W7.tape| + 1)` plus one halting step (`conv_runs`; `sim` is exact).

Test specs: a leaf with `K = 0` (empty leaf body), a leaf with `K = 2`, a one-level step over it
(including a negative POST coefficient, so a negative Barrett reciprocal `μ` whose W9 encoding is
`natSyms 0 = []`), and a two-level step; one run has a non-empty `rest` that starts with a sign and
a W7 POST tag, which the converter must leave untouched.
-/

namespace WP.TapeConv.Smoke

open TMFw TMFw.Test TMFw.Contracts WP.TapeConv

/-- A leaf with no stages. -/
def leaf0 : IntMul.ComputablePaperFastDFTSpec := .basePow2 5 0 #[]

/-- A leaf with `K = 2` (stages of 2 and 4 twiddles). -/
def leafEx : IntMul.ComputablePaperFastDFTSpec :=
  .basePow2 9 2 #[#[(1, 2), (-3, 0)], #[(5, -6), (0, 0), (7, 8), (-1, -1)]]

/-- One step level over `leafEx` (`c0[1] = -7` gives a negative column divisor and `μ < 0`). -/
def stepEx : IntMul.ComputablePaperFastDFTSpec :=
  .step 12 9 3 2 2 #[[1, -2, 3], [0, 4]] #[(1, 1), (2, -2)] #[(3, 0), (-4, 5)]
    #[(6, 0), (-7, 0)] #[(8, 0), (9, 0)] leafEx

/-- Two step levels. -/
def stepEx2 : IntMul.ComputablePaperFastDFTSpec :=
  .step 40 12 5 2 4 #[[3, -1], [2]] #[(1, 0), (0, 1), (-1, 0), (0, -1)]
    #[(2, 2), (3, -3), (4, 4), (5, -5)] #[(10, 0), (11, 0), (12, 0), (13, 0)]
    #[(1, 0), (2, 0), (3, 0), (4, 0)] stepEx

/-- The compiled converter: input and output stack `tr`. -/
def convTM : Turing.FinTM2 := toFinTM2 (Γ := fun _ : CS => Sym) CS.tr CS.tr convP (none, 0)

/-- View a machine stack (alphabet `MachΓ … (some tr)`, definitionally `Sym`) as symbols. -/
def asSyms (l : List Sym) : List Sym := l

/-- The proved bound plus the halting step. -/
def bound (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  32 * ((W7.tape W7.snapshotFormat cSpec).length + 1) + 1

/-- `(steps, output = W9 tape ++ rest?)`, the bound, `|W7 tape|`, `|W9 tape|`. -/
def runConv (cSpec : IntMul.ComputablePaperFastDFTSpec) (rest : List Sym) :
    Option (ℕ × Bool) × ℕ × ℕ × ℕ :=
  ((runTM convTM (W7.tape W7.snapshotFormat cSpec ++ rest) 1000000).map
      (fun r => (r.1, decide (asSyms r.2 = W9.tapeSyms cSpec ++ rest))),
    bound cSpec, (W7.tape W7.snapshotFormat cSpec).length, (W9.tapeSyms cSpec).length)

/-- The run halts with exactly `W9.tapeSyms cSpec ++ rest` within the bound. -/
def ok (cSpec : IntMul.ComputablePaperFastDFTSpec) (rest : List Sym) : Bool :=
  match runTM convTM (W7.tape W7.snapshotFormat cSpec ++ rest) 1000000 with
  | some (n, out) => decide (asSyms out = W9.tapeSyms cSpec ++ rest) && decide (n ≤ bound cSpec)
  | none => false

/-- Atoms (`push`/`peek`/`pop`/`load`) and control nodes (`ite`/`loop`/`fix`/`recur`) of a program
term (every `seq`-inlined copy counted). -/
def progSize {K : Type} {Γ : K → Type} {σ : Type} : Prog K Γ σ → ℕ × ℕ
  | .push _ _ => (1, 0)
  | .peek _ _ => (1, 0)
  | .pop _ _ => (1, 0)
  | .load _ => (1, 0)
  | .seq p q => (progSize p).1 + (progSize q).1 |> fun a => (a, (progSize p).2 + (progSize q).2)
  | .ite _ p q => ((progSize p).1 + (progSize q).1, (progSize p).2 + (progSize q).2 + 1)
  | .loop _ p => ((progSize p).1, (progSize p).2 + 1)
  | .fix b => ((progSize b).1, (progSize b).2 + 1)
  | .recur _ => (0, 1)

#eval progSize convP

#eval [runConv leaf0 [], runConv leafEx [], runConv stepEx [],
  runConv stepEx2 [.pos, .tag 10, .bit true]]

#guard ok leaf0 []
#guard ok leafEx []
#guard ok stepEx []
#guard ok stepEx2 [.pos, .tag 10, .bit true]

end WP.TapeConv.Smoke
