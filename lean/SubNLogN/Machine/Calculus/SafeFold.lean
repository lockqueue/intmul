/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.SafeTransport
import SubNLogN.Machine.Contracts.Family

/-!
# Framed procedure calculus: safe symbolic folds (`Calculus/SafeFold.lean`)

The `SafeRunsIn` forms of the fixed-sequence rules of `Calculus/Rules.lean`, for a fixed framed
set and with the same costs. Step `i` of a fixed sequence runs safely from `st i` to `st (i + 1)`:
* `SafeRunsIn.forEachProg` for `forEachProg l f`;
* `SafeRunsIn.forEachRange` for `forEachRange n f`;
* `SafeRunsIn.forEachFin` for `forEachFin n f`, for example one step per role stack.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

section SafeFold

variable {K σ : Type} [DecidableEq K] {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}

/-- **Safe fixed sequences** (`forEachProg`): step `i` runs safely from `st i` to `st (i + 1)`
within `T l[i]`. The terminal `skip` costs `1`. -/
theorem SafeRunsIn.forEachProg {α : Type} (f : α → Prog K (fun _ => Sym) σ) (T : α → ℕ) :
    ∀ (l : List α) (st : ℕ → K → List Sym),
      (∀ (i : ℕ) (hi : i < l.length),
        SafeRunsIn framed ρ (f l[i]) (st i) (st (i + 1)) (fun _ => True) (T l[i])) →
      SafeRunsIn framed ρ (SubNLogN.Machine.forEachProg l f) (st 0) (st l.length) (fun _ => True)
        ((l.map T).sum + 1)
  | [], st, _ => by
    intro v
    exact ⟨id v, 1, SafeEval.load ρ id v (st 0), trivial, le_rfl⟩
  | a :: l, st, h => by
    have h0 : SafeRunsIn framed ρ (f a) (st 0) (st 1) (fun _ => True) (T a) := h 0 (by simp)
    have ih := SafeRunsIn.forEachProg f T l (fun i => st (i + 1)) (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simpa using this)
    have hs := SafeRunsIn.seq h0 ih
    refine SafeRunsIn.mono hs (fun _ _ => trivial) ?_
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Safe `forEachRange`. -/
theorem SafeRunsIn.forEachRange (n : ℕ) (f : ℕ → Prog K (fun _ => Sym) σ) (T : ℕ → ℕ)
    (st : ℕ → K → List Sym)
    (h : ∀ i < n, SafeRunsIn framed ρ (f i) (st i) (st (i + 1)) (fun _ => True) (T i)) :
    SafeRunsIn framed ρ (SubNLogN.Machine.forEachRange n f) (st 0) (st n) (fun _ => True)
      (((List.range n).map T).sum + 1) := by
  have hr := SafeRunsIn.forEachProg f T (List.range n) st (fun i hi => by
    have hi' : i < n := by simpa using hi
    simpa using h i hi')
  rw [List.length_range] at hr
  exact hr

/-- Safe `forEachFin` (for example one step per role stack of a fixed family). -/
theorem SafeRunsIn.forEachFin (n : ℕ) (f : Fin n → Prog K (fun _ => Sym) σ) (T : Fin n → ℕ)
    (st : ℕ → K → List Sym)
    (h : ∀ i : Fin n,
      SafeRunsIn framed ρ (f i) (st (i : ℕ)) (st ((i : ℕ) + 1)) (fun _ => True) (T i)) :
    SafeRunsIn framed ρ (SubNLogN.Machine.forEachFin n f) (st 0) (st n) (fun _ => True)
      (((List.finRange n).map T).sum + 1) := by
  have hr := SafeRunsIn.forEachProg f T (List.finRange n) st (fun i hi => by
    have hi' : i < n := by simpa using hi
    simpa using h ⟨i, hi'⟩)
  rw [List.length_finRange] at hr
  exact hr

end SafeFold

#assert_std_axioms SafeRunsIn.forEachProg SafeRunsIn.forEachRange SafeRunsIn.forEachFin

end SubNLogN.Machine.Calculus
