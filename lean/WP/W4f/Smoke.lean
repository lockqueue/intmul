import WP.W4f.Top
import IntMulTM.Framework.Sim

/-!
# WP.W4f.Smoke — the compiled `oddProg` machine on small inputs

`runOdd k u2` steps `machine oddProg σ0` (the framework's compiled machine; Mathlib's `TM2.step`)
directly from the configuration `machine_run` starts from: `k` on `.inl 0`, `u2` on `.inl 1`, all
other stacks empty. (No `toFinTM2` bundle: its `Fintype` fields are not needed for stepping.)
`smokeOK` checks the exact final stacks (the factor `natSyms (computableOddStrideFactor k u2)` on
`.inl 2`, the inputs restored, every scratch stack empty) and the step count against the proved
budget `40·(k+1)² + 1` (`oddProg_eval` plus the halting step of `machine_run`).
-/

namespace WP.W4f.Smoke

open TMFw TMFw.Contracts Turing

/-- All local stacks, in order. -/
def allStk : List (Loc 3 4) := [.inl 0, .inl 1, .inl 2, .inr 0, .inr 1, .inr 2, .inr 3]

/-- Initial stacks: `k` on `.inl 0`, `u2` on `.inl 1`, the rest empty. -/
def initStk (k u2 : ℕ) (l : Loc 3 4) : List Sym :=
  if l = .inl 0 then natSyms k else if l = .inl 1 then natSyms u2 else []

/-- Step `machine oddProg σ0` until it halts: `some (steps, all final stacks)`. -/
def runOdd (k u2 fuel : ℕ) : Option (ℕ × List (List Sym)) :=
  go fuel 0 ⟨some (some oddProg.entry), (((none, false, false) : Reg), none),
    liftStk (initStk k u2) []⟩
where
  /-- the stepping loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ (Loc 3 4) (fun _ => Sym) (Option oddProg.Lab))
      (Option oddProg.Lab) (Reg × Option (Option oddProg.Lab)) → Option (ℕ × List (List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine oddProg ((none, false, false) : Reg)) c with
      | none => some (n, allStk.map fun l => c.stk (some l))
      | some c' => go fuel (n + 1) c'

/-- The proved step budget of the compiled machine (cost bound plus the halting step). -/
def budget (k : ℕ) : ℕ := 40 * ((k + 1) * (k + 1)) + 1

/-- Exact final stacks and step count within the budget. -/
def smokeOK (k u2 : ℕ) : Bool :=
  match runOdd k u2 (budget k + 1) with
  | some (n, stks) =>
    decide (stks = [natSyms k, natSyms u2, natSyms (computableOddStrideFactor k u2),
      [], [], [], []]) && decide (n ≤ budget k)
  | none => false

#guard (List.range 6).all fun k => (List.range 9).all fun u2 => smokeOK k u2
#guard [(2, 1000), (3, 65535), (7, 12345), (8, 3)].all fun p => smokeOK p.1 p.2

-- `((k, u2), factor, actual steps, proved budget)`; the pinned contract examples first
#eval [(0, 5), (3, 0), (3, 2), (4, 3), (6, 1000), (8, 3)].map fun p =>
  (p, computableOddStrideFactor p.1 p.2, (runOdd p.1 p.2 (budget p.1 + 1)).map Prod.fst,
    budget p.1)

end WP.W4f.Smoke
