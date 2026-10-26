import IntMulTM.Exec.Runner
import WP.Top.Skeleton
import WP.Top.TapeConvBridge
import WP.TapeConv.Smoke

/-!
# Execution prototype 5: the production tape-conversion stage (third stage of `topProgC`)

`PcC` is the converter exactly as `WP.Top.TapeConv_of_contract` instantiates it: `WP.TapeConv.convP` placed on
W9's `BLoc 3` by `emb`, renamed into the 1-named-stack shape `Loc 1 14` by `ιB 3`. `stage := convStage PcC _`
lifts it to the 78-stack production layout (`ιc`: `TR ↦ GW.tr`, scratch ↦ `sc75`). It is run with
`runMachine` from the state with `W7.tape (snapshotSchedule format) cSpec` on `GW.tr` and every other
stack empty, on the converter smoke's specs (`WP.TapeConv.Smoke`).

Check: at the end `GW.tr = W9.tapeSyms cSpec`, every other stack is empty, and the step count is within the
proved bound `32·(|W7 tape| + 1)` plus the halting step.
-/

namespace IntMulTM.Exec.ConvStageRun

open TMFw TMFw.Contracts WP.Top IntMulTM

/-- The converter in the Top's shape. -/
def PcC : Prog (Loc 1 (11 + 3)) (fun _ => Sym) WP.TapeConv.CR :=
  (WP.TapeConv.convP.mapStk WP.TapeConv.emb).mapStk (ιB 3)

/-- The production stage. -/
def stage : Prog (StackId GW) (StackId.Γ encNatPair.Γ) WP.TapeConv.CR := convStage PcC (by decide)

/-- All 78 stacks. -/
def keys : List (StackId GW) := [.input, .output] ++ allGW.map StackId.work

/-- The W7 tape of `cSpec` (production format). -/
def tape7 (cSpec : IntMul.ComputablePaperFastDFTSpec) : List Sym :=
  W7.tape W7.snapshotSchedule.toTapeFormat cSpec

/-- Start: the W7 tape on `GW.tr`, everything else empty. -/
def start (cSpec : IntMul.ComputablePaperFastDFTSpec) : ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k) :=
  Function.update (fun _ => []) (StackId.work GW.tr) (tape7 cSpec)

/-- Run the stage. -/
def run (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    Option (ℕ × ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)) :=
  runMachine stage ((none, 0) : WP.TapeConv.CR) keys ⟨(none, 0), start cSpec⟩ 2000000

/-- Final state and bound. -/
def ok (cSpec : IntMul.ComputablePaperFastDFTSpec) : Bool :=
  match run cSpec with
  | some (t, S) =>
    (S .input).isEmpty && (S .output).isEmpty &&
      (allGW.all fun w => S (.work w) == if w = GW.tr then W9.tapeSyms cSpec else []) &&
      decide (t ≤ 32 * ((tape7 cSpec).length + 1) + 1)
  | none => false

#guard complete keys

#guard [WP.TapeConv.Smoke.leaf0, WP.TapeConv.Smoke.leafEx, WP.TapeConv.Smoke.stepEx,
  WP.TapeConv.Smoke.stepEx2].all ok

-- `(steps, bound, |W7 tape|, |W9 tape|)`
#eval [WP.TapeConv.Smoke.leaf0, WP.TapeConv.Smoke.leafEx, WP.TapeConv.Smoke.stepEx,
  WP.TapeConv.Smoke.stepEx2].map fun c =>
    ((run c).map Prod.fst, 32 * ((tape7 c).length + 1) + 1, (tape7 c).length, (W9.tapeSyms c).length)

end IntMulTM.Exec.ConvStageRun
