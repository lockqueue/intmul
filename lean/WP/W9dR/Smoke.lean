import WP.W9dR.RoundShift
import WP.W3b.Smoke

/-!
# WP.W9dR.Smoke — compiled runs of the round shift (test subroutines; test only)

The ten instances are **test-only, unverified** programs with finite registers:
* `shrConst 1`, `natToInt`, `splitSign`, `dropNat`: one-line framework macros;
* `decNat`, `incNat`, `copyNat`: the framework's `dec`, `inc`, `copyBlock`;
* `shlVar`, `shrVar`: copy the counter onto a marked scratch stack and count it down with `dec`,
  pushing a `0` bit (`shlVar`, only on a nonzero number) or popping one bit (`shrVar`) per round;
* `addInt`: W3b's signed glue `addSubProg` over its test adder `tAddSub` and the seed comparator.

`runMach` (W3b) steps the compiled machine (`machine p σ0`, Mathlib's `TM2.step`) from `x = v`, with
`s` preloaded on `c` (`1 + |natSyms s|` steps). The `#guard`s check `z = intSyms (divRoundPow2 v s)`.
The step counts are printed next to `30·(C+1)·(|v| + s + 1)` at `C = 50` (the test subroutines are
not linear; on these tiny inputs each costs below `50·(size + 1)`).
-/

namespace WP.W9dR.Smoke

open TMFw TMFw.Lib TMFw.Contracts WP.W7k2 WP.W9dR TMFw.W3b TMFw.W3b.Smoke

/-- No `recur` anywhere. -/
def noRecur {K : Type} {Γ : K → Type} {σ : Type} : Prog K Γ σ → Bool
  | .seq p q => noRecur p && noRecur q
  | .ite _ p q => noRecur p && noRecur q
  | .loop _ p => noRecur p
  | .fix b => noRecur b
  | .recur _ => false
  | _ => true

theorem freeBelow_of_noRecur {K : Type} {Γ : K → Type} {σ : Type} :
    ∀ (p : Prog K Γ σ) (d : ℕ), noRecur p = true → p.FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => by
    simp only [noRecur, Bool.and_eq_true] at h
    exact ⟨freeBelow_of_noRecur p d h.1, freeBelow_of_noRecur q d h.2⟩
  | .ite _ p q, d, h => by
    simp only [noRecur, Bool.and_eq_true] at h
    exact ⟨freeBelow_of_noRecur p d h.1, freeBelow_of_noRecur q d h.2⟩
  | .loop _ p, d, h => freeBelow_of_noRecur p d h
  | .fix b, d, h => freeBelow_of_noRecur b (d + 1) h
  | .recur _, _, h => absurd h (by simp [noRecur])

/-- Test `shlVar` (`x`, `c`; scratch `t`, `u`). -/
def tShlV : SProg (Loc 2 2) :=
  .seq (peekR (.inl 0)) (.ite optIsBit
    (.seq (pushC (.inr 0) .mark) (.seq (copyBlock (.inl 1) (.inr 0) (.inr 1))
      (.seq (peekR (.inr 0)) (.seq (.loop optIsBit (.seq (pushC (.inl 0) (.bit false))
        (.seq (dec (.inr 0) (.inr 1)) (peekR (.inr 0))))) (popR (.inr 0))))))
    skip)

/-- Test `shrVar`. -/
def tShrV : SProg (Loc 2 2) :=
  .seq (pushC (.inr 0) .mark) (.seq (copyBlock (.inl 1) (.inr 0) (.inr 1))
    (.seq (peekR (.inr 0)) (.seq (.loop optIsBit (.seq (peekR (.inl 0))
      (.seq (.ite optIsBit (popR (.inl 0)) skip) (.seq (dec (.inr 0) (.inr 1)) (peekR (.inr 0))))))
      (popR (.inr 0)))))

/-- Test `shrConst 1`. -/
def tShr1 : SProg (Loc 1 0) := .seq (peekR (.inl 0)) (.ite optIsBit (popR (.inl 0)) skip)

/-- Test `dropNat`. -/
def tDrop : SProg (Loc 1 0) :=
  .seq (peekR (.inl 0)) (.loop optIsBit (.seq (popR (.inl 0)) (peekR (.inl 0))))

/-- Test `addInt`. -/
def tAdd : Prog (Loc 3 4) (fun _ => Sym) (RegA (Option Sym) (Option Sym) CReg) :=
  addSubProg (le_refl 4) (le_refl 4) (by decide : 2 ≤ 4) (fun r : CReg => r.2.2) (tAddSub false)
    (tAddSub true) (cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)) false

/-- The test instances. -/
def tJ : RSInst where
  shlV := ⟨2, Option Sym, fun _ => (), tShlV, by norm_num, inferInstance, inferInstance,
    freeBelow_of_noRecur _ 0 rfl⟩
  shr1 := ⟨0, Option Sym, fun _ => (), tShr1, by norm_num, inferInstance, inferInstance,
    freeBelow_of_noRecur _ 0 rfl⟩
  n2i := ⟨0, Option Sym, fun _ => (), pushC (.inl 0) .pos, by norm_num, inferInstance,
    inferInstance, freeBelow_of_noRecur _ 0 rfl⟩
  add := ⟨4, RegA (Option Sym) (Option Sym) CReg, fun _ => (), tAdd, le_rfl, inferInstance,
    inferInstance, freeBelow_of_noRecur _ 0 rfl⟩
  sgn := ⟨0, Option Sym, fun r => decide (r = some .neg), popR (.inl 0), by norm_num,
    inferInstance, inferInstance, freeBelow_of_noRecur _ 0 rfl⟩
  shrV := ⟨2, Option Sym, fun _ => (), tShrV, by norm_num, inferInstance, inferInstance,
    freeBelow_of_noRecur _ 0 rfl⟩
  dec := ⟨1, Option Sym, fun _ => (), dec (.inl 0) (.inr 0), by norm_num, inferInstance,
    inferInstance, freeBelow_of_noRecur _ 0 rfl⟩
  inc := ⟨1, Option Sym, fun _ => (), inc (.inl 0) (.inr 0), by norm_num, inferInstance,
    inferInstance, freeBelow_of_noRecur _ 0 rfl⟩
  copy := ⟨1, Option Sym, fun _ => (), copyBlock (.inl 0) (.inl 1) (.inr 0), by norm_num,
    inferInstance, inferInstance, freeBelow_of_noRecur _ 0 rfl⟩
  drop := ⟨0, Option Sym, fun _ => (), tDrop, by norm_num, inferInstance, inferInstance,
    freeBelow_of_noRecur _ 0 rfl⟩

/-- Initial registers. -/
def σ0 : tJ.Reg :=
  ((none : Option Sym), (none : Option Sym), (none : Option Sym),
    ((none, none, none, none, (none, none, .eq)) : RegA (Option Sym) (Option Sym) CReg),
    (none : Option Sym), (none : Option Sym), (none : Option Sym), (none : Option Sym),
    (none : Option Sym), (none : Option Sym))

/-- Preload `s` on `c`, then the round shift. -/
def rsShow (s : ℕ) : Prog RL (fun _ => Sym) tJ.Reg := .seq (preload (.inl 1) (natSyms s)) (rsProg tJ)

/-- Run on `(v, s)`: `(steps, z)`. -/
def runRS (v : ℤ) (s : ℕ) : Option (ℕ × List Sym) :=
  runMach (rsShow s) σ0 (.inl 0) (.inl 2) (intSyms v) 200000

#guard (runRS 5 1).map (·.2) = some (intSyms (IntMul.divRoundPow2 5 1))
#guard (runRS (-5) 1).map (·.2) = some (intSyms (IntMul.divRoundPow2 (-5) 1))
#guard (runRS 6 2).map (·.2) = some (intSyms (IntMul.divRoundPow2 6 2))
#guard (runRS (-6) 2).map (·.2) = some (intSyms (IntMul.divRoundPow2 (-6) 2))
#guard (runRS 3 0).map (·.2) = some (intSyms (IntMul.divRoundPow2 3 0))
#guard (runRS 0 2).map (·.2) = some (intSyms (IntMul.divRoundPow2 0 2))

/-- Steps vs `30·(C+1)·(|v| + s + 1)` at `C = 50` (plus the preload). -/
def report (v : ℤ) (s : ℕ) : String :=
  match runRS v s with
  | none => s!"v={v} s={s}: no halt"
  | some (n, z) =>
    s!"v={v} s={s}: z_ok={decide (z = intSyms (IntMul.divRoundPow2 v s))} steps={n} " ++
      s!"bound={30 * 51 * (bitLen v.natAbs + s + 1)}"

#eval [report 5 1, report (-5) 1, report 6 2, report (-6) 2, report 3 0, report 0 2]

end WP.W9dR.Smoke
