import WP.W3b.Sign
import WP.W3b.CmpInt
import WP.W3b.SmallOp
import WP.W3b.AddSub

/-!
# WP.W3b.Smoke — compiled runs of the W3b programs

Each run compiles a program to the framework machine (`machine p σ0`, Mathlib's `TM2.step`): the
one-operand programs through `toFinTM2` and the framework harness `Test.runTM`, the multi-operand
ones (large register types) through `runMach` below, which is cross-checked against `Test.runTM`.
The step count is `prefix + cost + 1`: an optional `preload` prefix pushing the second operand
(`1 + |intSyms b|` steps), the program's evaluation cost, and one final step (register reset and
halt). Expected values (from the exact `Eval` costs) are in the comments and checked with
`#guard`.

| program | exact cost (proved bound) |
|---|---|
| `attachProg` | 2 (C = 2) |
| `negProg`, `signProg` | 3 (C = 3) |
| `mul2Prog`, `div2Prog` | 5 (`≤ 20·(|z|+1)`) |
| `mul3Prog` | `6n + 3·|flush| + 13` (`≤ 6n + 19`) |
| `div3Prog` | `7n + 9` (`≤ 7n + 9`) |
| `cmpIntProg cmpNum` | `12·min(|a|,|b|) + 19` (`≤ 19·(|a|+|b|+1)`) |

The signed add/sub runs use `tAddSub`, a **test-only, unverified, quadratic** unsigned
adder/subtractor built from the seed-library macros; they check the sign logic end to end, not
the cost (the real subroutines come from W3).
-/

namespace TMFw.W3b.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Test Turing Computability

/-- Push the symbols of `l` onto stack `k` so that `l` ends up on top, in order (`1 + |l|` steps). -/
def preload {K σ : Type} (k : K) (l : List Sym) : Prog K (fun _ => Sym) σ :=
  l.reverse.foldl (fun p x => .seq p (.push k fun _ => x)) (.load id)

/-- Run a one-operand program on stack `x = input`; output = final `x`. -/
def run1 {m : ℕ} {R : Type} [Fintype R] (p : Prog (Loc 1 m) (fun _ => Sym) R) (r0 : R)
    (input : List Sym) : Option (ℕ × List Sym) :=
  runTM (toFinTM2 (Γ := fun _ : Loc 1 m => Sym) (.inl 0) (.inl 0) p r0) input 100000

/-! ## Sign operations -/

-- attach: 5 = [1,0,1]; 2 + 1 steps
#guard run1 (attachProg true) ((none, none) : Reg2) (natSyms 5 ++ [.sep]) =
  some (3, [.neg, .bit true, .bit false, .bit true, .sep])
#guard run1 (attachProg true) ((none, none) : Reg2) (natSyms 0 ++ [.sep]) = some (3, [.pos, .sep])
#guard run1 (attachProg false) ((none, none) : Reg2) (natSyms 5 ++ [.sep]) =
  some (3, [.pos, .bit true, .bit false, .bit true, .sep])

-- negate: 3 + 1 steps; zero stays `pos`
#guard run1 negProg ((none, none) : Reg2) (intSyms 6 ++ [.sep]) = some (4, intSyms (-6) ++ [.sep])
#guard run1 negProg ((none, none) : Reg2) (intSyms (-6) ++ [.sep]) = some (4, intSyms 6 ++ [.sep])
#guard run1 negProg ((none, none) : Reg2) (intSyms 0 ++ [.sep]) = some (4, [.pos, .sep])

/-- `signProg`, then push the observed `Ordering` as a tag (`lt, eq, gt ↦ tag 0, 1, 2`). -/
def signShow : Prog (Loc 1 0) (fun _ => Sym) Reg2 :=
  .seq signProg (.push (.inl 0) fun v => ordTag (signObs v))

-- 3 + 1 (tag) + 1 steps
#guard run1 signShow ((none, none) : Reg2) (intSyms (-6)) = some (5, .tag 0 :: intSyms (-6))
#guard run1 signShow ((none, none) : Reg2) (intSyms 0) = some (5, .tag 1 :: intSyms 0)
#guard run1 signShow ((none, none) : Reg2) (intSyms 6) = some (5, .tag 2 :: intSyms 6)

/-! ## Small constant operations -/

#guard run1 mul2Prog ((none, none) : Reg2) (intSyms (-3) ++ [.sep]) =
  some (6, intSyms (-6) ++ [.sep])
#guard run1 mul2Prog ((none, none) : Reg2) (intSyms 0 ++ [.sep]) = some (6, intSyms 0 ++ [.sep])
#guard run1 div2Prog ((none, none) : Reg2) (intSyms (-6) ++ [.sep]) =
  some (6, intSyms (-3) ++ [.sep])
#guard run1 div2Prog ((none, none) : Reg2) (intSyms 0 ++ [.sep]) = some (6, intSyms 0 ++ [.sep])

-- ×3: 5 ↦ 15 (n = 3, flush [1]): 6·3 + 3 + 13 + 1 = 35 ≤ 6·3 + 19 + 1
#guard run1 mul3Prog ((none, none, 0) : M3R) (intSyms 5 ++ [.sep]) =
  some (35, intSyms 15 ++ [.sep])
-- ×3: -7 ↦ -21 (n = 3, flush [0,1]): 6·3 + 6 + 13 + 1 = 38 = bound + 1 (tight)
#guard run1 mul3Prog ((none, none, 0) : M3R) (intSyms (-7) ++ [.sep]) =
  some (38, intSyms (-21) ++ [.sep])
#guard run1 mul3Prog ((none, none, 0) : M3R) (intSyms 0 ++ [.sep]) = some (14, intSyms 0 ++ [.sep])

-- exact ÷3: 7n + 9 + 1
#guard run1 div3Prog ((none, none, 0, false) : D3R) (intSyms (-15) ++ [.sep]) =
  some (38, intSyms (-5) ++ [.sep])
#guard run1 div3Prog ((none, none, 0, false) : D3R) (intSyms 21 ++ [.sep]) =
  some (45, intSyms 7 ++ [.sep])
#guard run1 div3Prog ((none, none, 0, false) : D3R) (intSyms 0 ++ [.sep]) =
  some (10, intSyms 0 ++ [.sep])

#eval [run1 mul3Prog ((none, none, 0) : M3R) (intSyms 5 ++ [.sep]),
  run1 div3Prog ((none, none, 0, false) : D3R) (intSyms (-15) ++ [.sep])]

/-! ## Direct runner for large register types

`toFinTM2` bundles `Fintype` instances, and its `Fintype σ` field enumerates the whole register
type (`|Option Sym| = 24` per symbol slot: about `10^6` values for `RegS CReg`, `6·10^8` for the
add/sub registers), so `Test.runTM` is only usable for small `σ`. `runMach` steps exactly the same
machine (`machine p σ0`, Mathlib's `TM2.step`) from the same initial configuration
(`liftStk (stkOnly k₀ input) []`, cf. `initList_eq`, `liftStk_stkOnly`), without the bundle. -/

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

-- cross-check against the framework harness on small register types
#guard runMach mul3Prog ((none, none, 0) : M3R) (.inl 0) (.inl 0) (intSyms (-7) ++ [.sep]) 100000 =
  run1 mul3Prog ((none, none, 0) : M3R) (intSyms (-7) ++ [.sep])
#guard runMach div3Prog ((none, none, 0, false) : D3R) (.inl 0) (.inl 0) (intSyms 21 ++ [.sep])
  100000 = run1 div3Prog ((none, none, 0, false) : D3R) (intSyms 21 ++ [.sep])

/-! ## Signed comparison (with the seed comparator `cmpNum`) -/

/-- Preload `b` on `y`, compare, push the result tag on `x`. -/
def cmpShow (b : ℤ) : Prog (Loc 2 2) (fun _ => Sym) (RegS CReg) :=
  .seq (preload (.inl 1) (intSyms b))
    (.seq (cmpIntProg (cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)))
      (.push (.inl 0) fun v => ordTag (cmpIntObs (fun r : CReg => r.2.2) v)))

def runCmpInt (a b : ℤ) : Option (ℕ × List Sym) :=
  runMach (cmpShow b) ((none, none, (none, none, .eq)) : RegS CReg) (.inl 0) (.inl 0) (intSyms a)
    100000

-- -5 < 3: preload 4 + (12·2 + 19) + 1 (tag) + 1 = 49
#guard runCmpInt (-5) 3 = some (49, .tag 0 :: intSyms (-5))
-- -5 > -6: preload 5 + (12·3 + 19) + 2 = 62
#guard runCmpInt (-5) (-6) = some (62, .tag 2 :: intSyms (-5))
-- 0 = 0: preload 2 + 19 + 2 = 23
#guard runCmpInt 0 0 = some (23, .tag 1 :: intSyms 0)
#guard (runCmpInt 6 (-6)).map (·.2.head?) = some (some (.tag 2))
#guard (runCmpInt 6 6).map (·.2.head?) = some (some (.tag 1))

/-! ## Signed add / subtract (glue only; test subroutines) -/

/-- **Test only, unverified, quadratic**: unsigned `z += x + y` (`sub = false`) or `z += x - y`
(`sub = true`): copy both operands to scratch, count the copy of `y` down to zero while counting
the copy of `x` up (or down), then move the result onto `z`. -/
def tAddSub (sub : Bool) : SProg (Loc 3 4) :=
  .seq (pushC (.inr 0) .mark)
  (.seq (copyBlock (.inl 0) (.inr 0) (.inr 3))
  (.seq (pushC (.inr 1) .mark)
  (.seq (copyBlock (.inl 1) (.inr 1) (.inr 3))
  (.seq (peekR (.inr 1))
  (.seq (.loop optIsBit (.seq (dec (.inr 1) (.inr 3))
      (.seq (if sub then dec (.inr 0) (.inr 3) else inc (.inr 0) (.inr 3)) (peekR (.inr 1)))))
  (.seq (popR (.inr 1))
  (.seq (reverseBlock (.inr 0) (.inr 2) (.inr 3))
  (.seq (moveBlock (.inr 0) (.inl 2))
  (popR (.inr 0))))))))))

/-- Preload `b` on `y`, run signed add/sub. -/
def addShow (flip : Bool) (b : ℤ) :
    Prog (Loc 3 4) (fun _ => Sym) (RegA (Option Sym) (Option Sym) CReg) :=
  .seq (preload (.inl 1) (intSyms b))
    (addSubProg (le_refl 4) (le_refl 4) (by decide : 2 ≤ 4) (fun r : CReg => r.2.2)
      (tAddSub false) (tAddSub true) (cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)) flip)

/-- Final `z` of signed add/sub on `(a, b)`. -/
def runAddSub (flip : Bool) (a b : ℤ) : Option (List Sym) :=
  (runMach (addShow flip b) (none, none, none, none, (none, none, .eq)) (.inl 0) (.inl 2)
    (intSyms a) 1000000).map (·.2)

#guard runAddSub false 5 (-7) = some (intSyms (-2))
#guard runAddSub false (-5) 7 = some (intSyms 2)
#guard runAddSub false 5 (-5) = some [.pos]
#guard runAddSub false (-3) (-4) = some (intSyms (-7))
#guard runAddSub false 0 0 = some [.pos]
#guard runAddSub false 9 3 = some (intSyms 12)
#guard runAddSub true 3 3 = some [.pos]
#guard runAddSub true 3 (-4) = some (intSyms 7)
#guard runAddSub true (-3) 4 = some (intSyms (-7))
#guard runAddSub true 0 5 = some (intSyms (-5))
#guard runAddSub true 5 0 = some (intSyms 5)
-- `b = 0` with `flip`: the "negative zero" effective operand
#guard runAddSub true 0 0 = some [.pos]
#guard runAddSub true (-2) 0 = some (intSyms (-2))
#guard runAddSub true 2 9 = some (intSyms (-7))

#eval [runCmpInt (-5) 3, runCmpInt (-5) (-6)]
#eval [runAddSub false 5 (-7), runAddSub true (-2) 0, runAddSub true 2 9]

end TMFw.W3b.Smoke
