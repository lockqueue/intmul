import IntMulTM.Exec.TopRun

/-!
# Native driver: the concrete final machine on the execution-test inputs

Usage: `native_top [AxB ...]` (default: the list below). For each input it prints `steps`, `accepted` and wall
ms, flushing after each line, then a verdict line `NATIVE_TOP: OK|FAIL`. Inputs come from the command line,
so no run is folded into a compile-time constant.
-/

open IntMulTM.Exec.TopRun

/-- Default inputs. -/
def defaultInputs : List String := ["0x0", "1x1", "3x5", "13x11", "255x255"]

/-- Parse `AxB`. -/
def parsePair (s : String) : Option (ℕ × ℕ) :=
  match s.splitOn "x" with
  | [a, b] => do pure (← a.toNat?, ← b.toNat?)
  | _ => none

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let specs := if args.isEmpty then defaultInputs else args
  let mut allOk := true
  for spec in specs do
    match parsePair spec with
    | none =>
      out.putStrLn s!"  bad input {spec}"
      allOk := false
    | some (a, b) =>
      let t0 ← IO.monoMsNow
      match runTopIx a b 4000000000 with
      | some (t, S) =>
        let good := accepted a b S
        let t1 ← IO.monoMsNow
        out.putStrLn s!"  {a}*{b}: steps={t} accepted={good} ms={t1 - t0}"
        allOk := allOk && good
      | none =>
        out.putStrLn s!"  {a}*{b}: did not halt within fuel"
        allOk := false
    out.flush
  out.putStrLn s!"NATIVE_TOP: {if allOk then "OK" else "FAIL"} inputs={specs.length}"
  out.flush
  return (if allOk then 0 else 1)
