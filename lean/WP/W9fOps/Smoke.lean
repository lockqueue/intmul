import WP.W9fOps.LeInd
import WP.W9fOps.MulPow2
import WP.W9fOps.ShrFloor

/-!
# WP.W9fOps.Smoke — runs of the W9f ops on the machine (`machine p σ0`, Mathlib's `TM2.step`)

The programs are instantiated with concrete subroutines:
* the seed-library programs of the proved W3 instances: `cmpNum` (`w3_cmpNat`), `copyBlock`
  (`w3_copyNat`), `dec` (`w3_decNat`), `inc` (`w3_incNat`);
* **test-only, unverified** counter loops `tShl` / `tShr` for the open `W3_shlVar` /
  `W3_shrVar` (count a copy of `c` down with `dec`; push / pop one low bit per step).
Operand `b` is preloaded on `y` by a prefix program; `x` holds `a`; the output is `z`.
Runs go through `runMach` (no `toFinTM2` bundle, whose `Fintype σ` field would enumerate the
register type). Results are checked with `#guard`.
-/

namespace WP.W9fOps.Smoke

open TMFw TMFw.Lib TMFw.Contracts Turing

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

/-- Push the symbols of `l` onto stack `k` so that `l` ends up on top, in order. -/
def preload {K σ : Type} (k : K) (l : List Sym) : Prog K (fun _ => Sym) σ :=
  l.reverse.foldl (fun p x => .seq p (.push k fun _ => x)) (.load id)

/-- **Test only, unverified**: `x ↦ x·2^c` (number `x`, counter `c` restored). -/
def tShl : SProg (Loc 2 2) :=
  .seq (pushC (.inr 0) .mark)
  (.seq (copyBlock (.inl 1) (.inr 0) (.inr 1))
  (.seq (peekR (.inr 0))
  (.seq (.loop optIsBit (.seq (dec (.inr 0) (.inr 1))
      (.seq (peekR (.inl 0)) (.seq (.ite optIsBit (pushC (.inl 0) (.bit false)) skip)
        (peekR (.inr 0))))))
  (popR (.inr 0)))))

/-- **Test only, unverified**: `x ↦ x / 2^c` (number `x`, counter `c` restored). -/
def tShr : SProg (Loc 2 2) :=
  .seq (pushC (.inr 0) .mark)
  (.seq (copyBlock (.inl 1) (.inr 0) (.inr 1))
  (.seq (peekR (.inr 0))
  (.seq (.loop optIsBit (.seq (dec (.inr 0) (.inr 1))
      (.seq (peekR (.inl 0)) (.seq (.ite optIsBit (popR (.inl 0)) skip) (peekR (.inr 0))))))
  (popR (.inr 0)))))

/-- `z` after running `p` (over `Loc 3 4`) on `x = a`, `y = b`. -/
def runOp {σ : Type} (p : Prog (Loc 3 4) (fun _ => Sym) σ) (σ0 : σ) (a b : ℤ) :
    Option (ℕ × List Sym) :=
  runMach (.seq (preload (.inl 1) (intSyms b)) p) σ0 (.inl 0) (.inl 2) (intSyms a) 1000000

/-- `[a ≤ b]` with the seed comparator. -/
def runLe (a b : ℤ) : Option (ℕ × List Sym) :=
  runOp (leIndProg (by decide : 2 ≤ 4) (fun r : CReg => r.2.2)
    (cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1))) (none, none, (none, none, .eq)) a b

/-- `a·2^|b|` with `copyBlock` and the test shifter. -/
def runShl (a b : ℤ) : Option (List Sym) :=
  (runOp (mulPow2Prog (by decide : 1 ≤ 4) (by decide : 2 ≤ 4) (copyBlock (.inl 0) (.inl 1) (.inr 0))
    tShl) ((none, none, none, none) : RegM (Option Sym) (Option Sym)) a b).map (·.2)

/-- `a >>> |b|` with `copyBlock`, `dec`, `inc` and the test shifter. -/
def runShr (a b : ℤ) : Option (List Sym) :=
  (runOp (shrFloorProg (by decide : 1 ≤ 4) (by decide : 1 ≤ 4) (by decide : 2 ≤ 4)
    (by decide : 1 ≤ 4) (copyBlock (.inl 0) (.inl 1) (.inr 0)) (dec (.inl 0) (.inr 0)) tShr
    (inc (.inl 0) (.inr 0)))
    ((none, none, none, none, none, none) : RegF (Option Sym) (Option Sym) (Option Sym) (Option Sym))
    a b).map (·.2)

/-! ## `[a ≤ b]` (exact step counts: preload `1 + |intSyms b|`, pops 2, `cmpNum` `12·min + 15`,
branch 2 or 3, pushes 2, halt 1) -/

-- 3 ≤ 5: 5 + (2 + 39 + 3 + 2) + 1 = 52
#guard runLe 3 5 = some (52, intSyms 1)
-- 5 ≤ 3 fails: 4 + (2 + 39 + 2 + 2) + 1 = 50
#guard runLe 5 3 = some (50, intSyms 0)
#guard (runLe (-2) (-2)).map (·.2) = some (intSyms 1)
#guard (runLe (-1) (-3)).map (·.2) = some (intSyms 0)
#guard (runLe 0 0).map (·.2) = some (intSyms 1)
#guard (runLe (-5) 3).map (·.2) = some (intSyms 1)
#guard (runLe 5 (-3)).map (·.2) = some (intSyms 0)

/-! ## `a·2^|b|` (test shifter) -/

#guard runShl 3 2 = some (intSyms 12)
#guard runShl (-3) 2 = some (intSyms (-12))
#guard runShl 0 5 = some (intSyms 0)
#guard runShl 5 0 = some (intSyms 5)
#guard runShl (-5) (-2) = some (intSyms (-20))

/-! ## `a >>> |b|` (floor; test shifter) -/

#guard runShr 13 2 = some (intSyms 3)
#guard runShr (-13) 2 = some (intSyms (-4))
#guard runShr (-1) 5 = some (intSyms (-1))
#guard runShr (-4) 1 = some (intSyms (-2))
#guard runShr 4 3 = some (intSyms 0)
#guard runShr 0 3 = some (intSyms 0)
#guard runShr (-8) 3 = some (intSyms (-1))
#guard runShr 7 0 = some (intSyms 7)
#guard runShr (-7) 0 = some (intSyms (-7))
#guard runShr 5 (-1) = some (intSyms 2)
#guard runShr (-9) (-2) = some (intSyms (-3))

#eval [runLe 3 5, runLe 5 3]
#eval [runShl (-3) 2, runShr (-13) 2, runShr (-1) 5]

end WP.W9fOps.Smoke
