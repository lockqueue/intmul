import WP.W3.AddSub
import WP.W3.Misc

/-!
# WP.W3.Smoke — compiled runs of the W3 programs

Each run compiles the program to the framework machine (`machine p σ0`, Mathlib's `TM2.step`) and
steps it from `liftStk (stkOnly k₀ input) []` (`runMach`, as in `WP.W3b.Smoke`; it avoids
`toFinTM2`'s enumeration of the register type). Step count = `preload` prefix (`1 + |b|`) +
evaluation cost + 1 (halt).

| program | exact cost | proved bound |
|---|---|---|
| `addSubProg f` | `6 + Σ_iter (8 + mx + my) + 1 + 2(n+1) + |dropWhile| + 3 + 3|a| + 2 + 3|b| + 2` | `18(|a|+|b|) + 17` |
| `normProg` | `1 + 3|l| + 4 + 2|l| + |dropWhile| + 3` | `6|l| + 8` |
| `dropNum` | `2|a| + 4` | `4(|a| + 1)` |

(`mx`, `my` = 3 if that operand still had a bit in the iteration, else 2; `n = max(|a|, |b|)`.)
-/

namespace WP.W3.Smoke

open TMFw TMFw.Lib TMFw.Contracts Turing Computability

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

/-- `z += a ∘ b` on the machine: `x = a` (input), `y = b` (preloaded), result read from `z`. -/
def runAS (f : Bool → Bool → Bool → Bool × Bool) (a b : ℕ) : Option (ℕ × List Sym) :=
  runMach (.seq (preload (.inl 1) (natSyms b)) (addSubProg f)) ((none, none, false) : AReg)
    (.inl 0) (.inl 2) (natSyms a) 100000

/-- Output correct and steps within `preload + bound + 1`. -/
def okAS (f : Bool → Bool → Bool → Bool × Bool) (a b r : ℕ) : Bool :=
  match runAS f a b with
  | some (n, out) => out == natSyms r &&
      decide (n ≤ (1 + bitLen b) + (18 * (bitLen a + bitLen b) + 17) + 1)
  | none => false

#guard okAS addBit 5 3 8
#guard okAS addBit 0 0 0
#guard okAS addBit 0 6 6
#guard okAS addBit 13 0 13
#guard okAS addBit 255 1 256
#guard okAS addBit 1 255 256
#guard okAS subBit 5 3 2
#guard okAS subBit 8 7 1
#guard okAS subBit 6 6 0
#guard okAS subBit 9 0 9
#guard okAS subBit 256 1 255

-- exact step counts (hand-computed from the exact `Eval` costs, see the table):
-- 5 + 3: preload 3, cost 6 + (12 + 12 + 11 + 1) + 15 + 11 + 8 = 76, halt 1
#guard (runAS addBit 5 3).map (·.1) = some 80
-- 5 - 3: emitNorm skips two zeros: 6 + 36 + 13 + 11 + 8 = 74
#guard (runAS subBit 5 3).map (·.1) = some 78

#eval [runAS addBit 5 3, runAS subBit 5 3, runAS addBit 255 1, runAS subBit 256 1]

/-- `normNat` on the machine. -/
def runNorm (l : List Bool) : Option (ℕ × List Sym) :=
  runMach normProg (none : Option Sym) (.inl 0) (.inl 0) (l.map Sym.bit ++ [.sep]) 100000

-- [1,0,1,0,0] ↦ 5 = [1,0,1]: 1 + 19 + (10 + 3 + 3) + 1 = 37 ≤ 6·5 + 8 + 1
#guard runNorm [true, false, true, false, false] = some (37, natSyms 5 ++ [.sep])
#guard (runNorm [false, false]).map (·.2) = some [.sep]
#guard (runNorm []).map (·.2) = some [.sep]

/-- `dropNat` on the machine. -/
def runDrop (a : ℕ) : Option (ℕ × List Sym) :=
  runMach (dropNum (.inl 0 : Loc 1 0)) (none : Option Sym) (.inl 0) (.inl 0)
    (natSyms a ++ [.sep]) 100000

-- 6 = [0,1,1]: 2·3 + 4 + 1 = 11
#guard runDrop 6 = some (11, [.sep])
#guard runDrop 0 = some (5, [.sep])

end WP.W3.Smoke
