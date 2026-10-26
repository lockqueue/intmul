import WP.W3s.Split
import WP.W3s.Concat

/-!
# WP.W3s.Smoke — compiled runs of the W3s programs

Each run compiles the program to the framework machine (`machine p σ0`, Mathlib's `TM2.step`) and
steps it from `liftStk (stkOnly k₀ input) []` (`runMach`, as in `WP.W3b.Smoke`; cross-checked
against the framework harness `Test.runTM ∘ toFinTM2` below). The input is the number on `x`; a
`preload` prefix (`1 + |list|` steps) pushes the counter (and the low part for `concatAt`). The
reported step count is `prefix + cost + 1` (one final step: register reset and halt), and every run
is checked against the proved bound `C·(…)` of its contract.
-/

namespace TMFw.W3s.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Test Turing Computability

/-- Push the symbols of `l` onto stack `k` so that `l` ends up on top, in order (`1 + |l|` steps). -/
def preload {K σ : Type} (k : K) (l : List Sym) : Prog K (fun _ => Sym) σ :=
  l.reverse.foldl (fun p x => .seq p (.push k fun _ => x)) (.load id)

/-- Run `machine p σ0` from input `input` on `k₀`: `some (steps, stack k₁)` if it halts. -/
def runMach {K σ : Type} [DecidableEq K] (p : Prog K (fun _ => Sym) σ) (σ0 : σ) (k₀ k₁ : K)
    (input : List Sym) (fuel : ℕ) : Option (ℕ × List Sym) :=
  go fuel 0 ⟨some (some p.entry), (σ0, none), liftStk (stkOnly k₀ input) []⟩
where
  /-- the loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab)) → Option (ℕ × List Sym)
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine p σ0) c with
      | none => some (n, c.stk (some k₁))
      | some c' => go fuel (n + 1) c'

/-! ## splitAt (`C = 30`) -/

def splitShow (n : ℕ) : SProg (Loc 3 3) := .seq (preload (.inl 1) (natSyms n ++ [.sep])) splitAtProg

/-- `(steps, x, y)` after `splitAt` of `a` at `n`. -/
def runSplit (a n : ℕ) : Option (ℕ × List Sym × List Sym) := do
  let (s, x) ← runMach (splitShow n) none (.inl 0) (.inl 0) (natSyms a ++ [.sep]) 100000
  let (_, y) ← runMach (splitShow n) none (.inl 0) (.inl 2) (natSyms a ++ [.sep]) 100000
  return (s, x, y)

/-- Check outputs and `steps ≤ prefix + 30·(min n |a| + |n| + 1) + 1`. -/
def okSplit (a n : ℕ) : Bool :=
  match runSplit a n with
  | some (s, x, y) => x == natSyms (a / 2 ^ n) ++ [.sep] && y == natSyms (a % 2 ^ n) &&
      decide (s ≤ (bitLen n + 2) + 30 * (min n (bitLen a) + bitLen n + 1) + 1)
  | none => false

#guard okSplit 13 2   -- 1101b: high 3, low 1
#guard okSplit 8 2    -- 0001b: low part 0 (high zeros dropped), high 2
#guard okSplit 5 10   -- counter beyond |a|: high 0, low 5
#guard okSplit 0 3
#guard okSplit 12 0
#guard okSplit 1000 7

/-! ## shrVar (`C = 33`) -/

def shrShow (n : ℕ) : SProg (Loc 2 4) := .seq (preload (.inl 1) (natSyms n ++ [.sep])) shrVarProg

def okShr (a n : ℕ) : Bool :=
  match runMach (shrShow n) none (.inl 0) (.inl 0) (natSyms a ++ [.sep]) 100000 with
  | some (s, x) => x == natSyms (a / 2 ^ n) ++ [.sep] &&
      decide (s ≤ (bitLen n + 2) + 33 * (min n (bitLen a) + bitLen n + 1) + 1)
  | none => false

#guard okShr 13 2
#guard okShr 5 10
#guard okShr 0 0
#guard okShr 1000 3

/-! ## shlVar (`C = 32`) -/

def shlShow (n : ℕ) : SProg (Loc 2 4) := .seq (preload (.inl 1) (natSyms n ++ [.sep])) shlVarProg

def okShl (a n : ℕ) : Bool :=
  match runMach (shlShow n) none (.inl 0) (.inl 0) (natSyms a ++ [.sep]) 100000 with
  | some (s, x) => x == natSyms (a * 2 ^ n) ++ [.sep] &&
      decide (s ≤ (bitLen n + 2) + 32 * (n + bitLen n + 1) + 1)
  | none => false

#guard okShl 5 3      -- 40
#guard okShl 0 5      -- 0: no zeros pushed
#guard okShl 1 0
#guard okShl 6 9

/-! ## concatAt (`C = 30`) -/

def catShow (lo n : ℕ) : SProg (Loc 3 3) :=
  .seq (preload (.inl 1) (natSyms n ++ [.sep]))
    (.seq (preload (.inl 2) (natSyms lo ++ [.sep])) concatAtProg)

def okCat (hi lo n : ℕ) : Bool :=
  match runMach (catShow lo n) none (.inl 0) (.inl 0) (natSyms hi ++ [.sep]) 100000,
    runMach (catShow lo n) none (.inl 0) (.inl 2) (natSyms hi ++ [.sep]) 100000 with
  | some (s, x), some (_, y) => x == natSyms (lo + hi * 2 ^ n) ++ [.sep] && y == [.sep] &&
      decide (s ≤ (bitLen n + 2) + (bitLen lo + 2) + 30 * (n + bitLen n + 1) + 1)
  | _, _ => false

#guard okCat 3 1 2    -- 13
#guard okCat 0 5 4    -- hi = 0: no padding
#guard okCat 2 0 3    -- 16: lo = 0, three zeros
#guard okCat 1 3 2    -- 7
#guard okCat 5 2 6

/-! ## Cross-check with the framework harness, and the actual step counts -/

/-- The framework harness on a two-named-stack program (input and output on `.inl 0`). -/
def runFin (p : SProg (Loc 2 4)) (input : List Sym) : Option (ℕ × List Sym) :=
  runTM (toFinTM2 (Γ := fun _ : Loc 2 4 => Sym) (.inl 0) (.inl 0) p none) input 100000

#guard runFin (shlShow 3) (natSyms 5 ++ [.sep]) =
  runMach (shlShow 3) none (.inl 0) (.inl 0) (natSyms 5 ++ [.sep]) 100000
#guard runFin (shrShow 2) (natSyms 13 ++ [.sep]) =
  runMach (shrShow 2) none (.inl 0) (.inl 0) (natSyms 13 ++ [.sep]) 100000

#eval [runSplit 13 2, runSplit 8 2, runSplit 5 10]
#eval [runMach (shlShow 3) none (.inl 0) (.inl 0) (natSyms 5 ++ [.sep]) 100000,
  runMach (catShow 1 2) none (.inl 0) (.inl 0) (natSyms 3 ++ [.sep]) 100000,
  runMach (shrShow 2) none (.inl 0) (.inl 0) (natSyms 13 ++ [.sep]) 100000]

end TMFw.W3s.Smoke
