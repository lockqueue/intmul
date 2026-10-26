import WP.W5.Main
import WP.W3b.Smoke
import WP.W3b.SmallOp

/-!
# WP.W5.Smoke — compiled runs of the multiplier (test subroutines; test only)

The W3 subroutines are **test-only, unverified** programs with finite registers, except the
verified W3b small ops:
* `addInt` / `subInt`: W3b's signed glue `addSubProg` over its test adder `tAddSub` (which counts
  the second operand down, so only tiny values are run) and the seed comparator;
* `smallOpInt`: W3b's `mul2Prog`, `div2Prog`, `div3Prog`;
* `splitAt`, `shlVar`: counter loops (`dec`) popping / pushing one bit per round.

`runMach` (W3b) steps the compiled machine (`machine p σ0`, Mathlib's `TM2.step`) of the contract
program `(mulP U).mapStk skLoc` from `x = a`, with `b` preloaded on `y` (`1 + |intSyms b|` steps).
The `#guard`s check `z = intSyms (a·b)` (base-case inputs: the test adder is not linear, so the
Toom-3 branch, `w ≥ 10`, is out of reach of a `< 60 s` run). Steps are printed next to the proved
per-level bound of `body_spec` evaluated at `Cu = 50` (an estimate for the test subroutines).
-/

namespace WP.W5.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.W3b TMFw.W3b.Smoke

/-- Test `splitAt` (`x`, `c`, `y`; scratch: counter copy, copy temp, popped bits). -/
def tSplit : SProg (Loc 3 3) :=
  .seq (pushC (.inr 0) .mark) (.seq (copyBlock (.inl 1) (.inr 0) (.inr 1))
  (.seq (pushC (.inr 2) .mark) (.seq (peekR (.inr 0))
  (.seq (.loop optIsBit (.seq (peekR (.inl 0))
      (.seq (.ite optIsBit (.seq (popR (.inl 0)) (pushR (.inr 2))) skip)
        (.seq (dec (.inr 0) (.inr 1)) (peekR (.inr 0))))))
  (.seq (popR (.inr 0)) (.seq (peekR (.inr 2))
  (.seq (.loop (fun r => decide (r = some (.bit false))) (.seq (popR (.inr 2)) (peekR (.inr 2))))
  (.seq (moveBlock (.inr 2) (.inl 2)) (popR (.inr 2))))))))))

/-- Test `shlVar` (`x`, `c`; scratch `t`, `u`). -/
def tShl : SProg (Loc 2 2) :=
  .seq (peekR (.inl 0)) (.ite optIsBit
    (.seq (pushC (.inr 0) .mark) (.seq (copyBlock (.inl 1) (.inr 0) (.inr 1))
      (.seq (peekR (.inr 0)) (.seq (.loop optIsBit (.seq (pushC (.inl 0) (.bit false))
        (.seq (dec (.inr 0) (.inr 1)) (peekR (.inr 0))))) (popR (.inr 0))))))
    skip)

/-- Test signed add (`flip = false`) / subtract (`flip = true`). -/
def tAdd (flip : Bool) : Prog (Loc 3 4) (fun _ => Sym) (RegA (Option Sym) (Option Sym) CReg) :=
  addSubProg (le_refl 4) (le_refl 4) (by decide : 2 ≤ 4) (fun r : CReg => r.2.2) (tAddSub false)
    (tAddSub true) (cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)) flip

/-- The test subroutine bundle. -/
def tU : Subs where
  add := ⟨4, le_rfl, RegA (Option Sym) (Option Sym) CReg, tAdd false⟩
  sub := ⟨4, le_rfl, RegA (Option Sym) (Option Sym) CReg, tAdd true⟩
  mul2 := ⟨0, by norm_num, Reg2, mul2Prog⟩
  div2 := ⟨0, by norm_num, Reg2, div2Prog⟩
  div3 := ⟨1, by norm_num, D3R, div3Prog⟩
  split := ⟨3, by norm_num, Option Sym, tSplit⟩
  shl := ⟨2, by norm_num, Option Sym, tShl⟩

/-- Initial registers. -/
def σ0 : tU.σ :=
  ((none : Option Sym),
    ((none, none, none, none, (none, none, .eq)) : RegA (Option Sym) (Option Sym) CReg),
    ((none, none, none, none, (none, none, .eq)) : RegA (Option Sym) (Option Sym) CReg),
    ((none, none) : Reg2), ((none, none) : Reg2), ((none, none, 0, false) : D3R),
    (none : Option Sym), (none : Option Sym))

/-- Preload `b` on `y`, then the multiplier (the contract program). -/
def mulShow (b : ℤ) : Prog (Loc 3 8) (fun _ => Sym) tU.σ :=
  .seq (preload (.inl 1) (intSyms b)) ((mulP tU).mapStk skLoc)

/-- Run on `(a, b)`: `(steps, z)`. -/
def runMul (a b : ℤ) : Option (ℕ × List Sym) :=
  runMach (mulShow b) σ0 (.inl 0) (.inl 2) (intSyms a) 400000

#guard (runMul 0 0).map (·.2) = some (intSyms 0)
#guard (runMul 3 (-5)).map (·.2) = some (intSyms (-15))
#guard (runMul (-2) (-3)).map (·.2) = some (intSyms 6)

/-- The per-level bound of `body_spec` in the base case, plus the call (`+2`) and the reset
(`+1`), at `Cu = 50`. -/
def baseBound (w : ℕ) : ℕ := 3 * unit 50 w + 38 * ((w + 2) / 3) + 26 + schoolCost 50 + 3

/-- Steps vs the bound (plus the preload). -/
def report (a b : ℤ) : String :=
  let w := max (bitLen a.natAbs) (bitLen b.natAbs)
  match runMul a b with
  | none => s!"a={a} b={b}: no halt"
  | some (n, z) =>
    s!"a={a} b={b} w={w}: z_ok={decide (z = intSyms (a * b))} steps={n} bound={baseBound w}"

#eval [report 0 0, report 3 (-5), report (-2) (-3)]

/-- The Toom-3 branch (`w = 10`, `K = 4`): parts and point values stay tiny, so the test adder
(which counts its second operand down) stays fast. -/
def runToom : Option (ℕ × List Sym) :=
  runMach (mulShow 3) σ0 (.inl 0) (.inl 2) (intSyms (-512)) 3000000

#guard runToom.map (·.2) = some (intSyms (-1536))

#eval runToom.map (·.1)

end WP.W5.Smoke
