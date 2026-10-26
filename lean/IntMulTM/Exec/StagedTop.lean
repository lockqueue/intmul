import IntMulTM.Exec.TopRun

/-!
# The final machine, stage by stage (native driver with per-stage progress)

`topP = topProg PinC P7C _ PcC _ P9C _` is `.seq` of six stage programs, each on its own register component. Running
the stages one after another, each from its initial registers on the stacks left by the previous one, performs
the same computation as the full run (`Eval.seq`; a stage's register component is untouched by the others), but
reports each stage's step count as soon as it finishes. Total machine steps of the full run = Σ stage steps − 5
(each separate run adds one halting step; the full run adds one).

Usage: `staged_top AxB [fuel]`.
-/

open TMFw TMFw.Contracts WP.Top IntMulTM IntMulTM.Exec

abbrev Stks := ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)

/-- Run one stage program with `runTabledIxR` and register normalizer `nr` (the identity in every use). -/
def runStage {σ : Type} (p : Prog (StackId GW) (StackId.Γ encNatPair.Γ) σ) (r0 : σ) (S : Stks) (fuel : ℕ)
    (nr : σ → σ := id) : Option (ℕ × Stks) :=
  WP.F9.runTabledIxR p r0 InputStageRun.keys TopRun.ix nr ⟨r0, S⟩ fuel

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let (a, b) := match args.head?.bind fun s => match s.splitOn "x" with
      | [x, y] => do pure (← x.toNat?, ← y.toNat?)
      | _ => none with
    | some p => p
    | none => (0, 0)
  let fuel := (args[1]? >>= String.toNat?).getD 100000000000
  let S0 : Stks := inputStk (W := GW) (encNatPair.encode (a, b))
  let stage {σ : Type} (name : String) (p : Prog (StackId GW) (StackId.Γ encNatPair.Γ) σ) (r0 : σ)
      (S : Stks) (nr : σ → σ := id) : IO (Option (ℕ × Stks)) := do
    let t0 ← IO.monoMsNow
    let r := runStage p r0 S fuel nr
    match r with
    | some (t, _) =>
      let t1 ← IO.monoMsNow
      out.putStrLn s!"  {a}*{b} stage {name}: steps={t} ms={t1 - t0}"
    | none => out.putStrLn s!"  {a}*{b} stage {name}: did not halt within fuel={fuel}"
    out.flush
    return r
  let some (t1, S1) ← stage "1 input" InputStageRun.PinC InputStageRun.σIn0 S0 | return 1
  let some (t2, S2) ← stage "2 tables" (tabStage WP.W7k2.Concrete.P7C WP.W7k2.Concrete.hm7)
      WP.W7k2.Concrete.r7 S1 | return 1
  let some (t3, S3) ← stage "3 conv" (convStage ConvStageRun.PcC (by decide)) ((none, 0) : WP.TapeConv.CR) S2
    | return 1
  let some (t4, S4) ← stage "4 glue" glueStage (none : Option Sym) S3 | return 1
  let some (t5, S5) ← stage "5 w9" (w9Stage WP.F9.Top.P9C TopRun.hm9) WP.F9.Top.r9 S4 WP.F9.Top.nr9
    | return 1
  let some (t6, S6) ← stage "6 output" outStage (none : Option Sym) S5 | return 1
  let good := TopRun.accepted a b S6
  out.putStrLn s!"STAGED_TOP: {if good then "OK" else "FAIL"} {a}*{b} totalSteps={t1 + t2 + t3 + t4 + t5 + t6 - 5} accepted={good}"
  out.flush
  return (if good then 0 else 1)
