import IntMulTM.Exec.IsqrtRun

/-!
# Native prototype: the isqrt machine run as a compiled executable

`main` runs `IntMulTM.Exec.IsqrtRun.ok` (direct machine run of `isqrtProg`: output `⌊√a⌋` within the proved
budget) on inputs far beyond the interpreter smoke, and prints one verdict line with the wall time.
-/

open IntMulTM.Exec.IsqrtRun WP.W7k1

def nativeInputs : List ℕ :=
  [0, 1, 255, 4095, 65535, 2 ^ 64 - 1, 2 ^ 100 + 12345, 2 ^ 128 + 7, 2 ^ 192 - 1]

def main (args : List String) : IO UInt32 := do
  -- `args.length` (0 when run without arguments) keeps the work out of compile-time closed terms.
  let inputs := nativeInputs.map (· + args.length)
  let t0 ← IO.monoMsNow
  let res := inputs.map fun a => (a, ok a, (run a (isqBudget a + 1)).map Prod.fst)
  -- Printing forces the (pure) results before the second clock read.
  for (a, good, st) in res do
    IO.println s!"  a={a} ok={good} steps={st}"
  let allOk := res.all (·.2.1)
  let t1 ← IO.monoMsNow
  let steps := res.map fun (_, _, s) => s.getD 0
  let total := steps.foldl (· + ·) 0
  IO.println s!"NATIVE_ISQRT: {if allOk then "OK" else "FAIL"} inputs={inputs.length} steps={steps} totalSteps={total} ms={t1 - t0}"
  return (if allOk then 0 else 1)
