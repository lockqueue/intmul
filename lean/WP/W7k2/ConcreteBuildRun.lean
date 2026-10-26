import WP.W7k2.Concrete
import WP.F9.Run

/-!
# WP.W7k2.ConcreteBuildRun — the concrete table builder on the machine (`#eval`)

`progC = buildProg BIC` (WP.W7k2.Concrete, all twenty instances concrete) runs under
`WP.F9.runTabled` (the framework machine itself: `tabled_eq`, `runTabled_sound`) on all 36 stacks of
`Loc 4 32`, with junk on `TR`, on the inputs' rests and on every scratch stack.

Each row checks that `TR = tapeFromC 0 L p K ++ junk` (the reference tape, `tape_ref_eq`) and that
every other stack is restored, and reports the step count.

**Only leaf schedules with `K = 0`.** These exercise init, the level loop, the leaf header and the
final restoration. Every leaf stage `s < K` calls stdChar at `q = 2p + K + 8 ≥ 25`, and a single such
call is hours of interpreter time. Larger `K` and step levels only add calls to the proved kernels
(stdChar, tap, c0c1, colRecip, …). Those kernels are validated by their own runs: W7k3
`ConcreteStdRun`, W7k3t `ConcreteRun`, W7k2 `ConcreteRun`, W7k1 `ConcreteRun`.
-/

namespace WP.W7k2.ConcreteBuildRun

open TMFw TMFw.Contracts WP.W7k2 WP.W7k2.Concrete

/-- All stacks of the builder. -/
def keys : List BL := (List.finRange 4).map Sum.inl ++ (List.finRange 32).map Sum.inr

theorem keys_complete : ∀ k : BL, k ∈ keys := by
  intro k
  rcases k with i | i <;> simp [keys]

/-- Junk tails (they start with a tag, so the input rests are `TermOK`). -/
def junk : List Sym := [.tag 9, .bit true]

/-- Inputs `L p K` on `1 2 3`, junk on `TR` and on every scratch stack. -/
def st0 (L p K : ℕ) : BL → List Sym := fun k =>
  if k = .inl 1 then natSyms L ++ junk
  else if k = .inl 2 then natSyms p ++ junk
  else if k = .inl 3 then natSyms K ++ junk
  else junk

/-- One run: `(every stack as the contract says, steps)`. -/
def row (L p K : ℕ) : Bool × ℕ :=
  let S := st0 L p K
  let E := Function.update S (.inl 0) (tapeFromC 0 L p K ++ S (.inl 0))
  match WP.F9.runTabled progC r0C keys ⟨r0C, S⟩ 1000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

/-- Leaf schedules with `K = 0`: fuel `L = 0`, and `L = 3` (the fuel is `min L K = 0`). -/
def rows : List (Bool × ℕ) := [row 0 8 0, row 3 9 0]

-- `(stacks ok, steps)` for each row.
#eval rows
#guard rows.all (·.1)

#assert_std_axioms keys_complete

end WP.W7k2.ConcreteBuildRun
