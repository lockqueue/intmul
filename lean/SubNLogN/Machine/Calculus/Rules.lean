/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Basic
import SubNLogN.Machine.Contracts.Family

/-!
# Framed procedure calculus (`Calculus/Rules.lean`): more `RunsIn` rules

Environment-general versions of the remaining composition rules, for use inside procedure bodies
(where `recur` calls make the environment non-empty):
* `RunsIn.recur`: a call `recur n` to the body of the `n`-th enclosing `fix`;
* `RunsIn.forEachProg`, `RunsIn.forEachRange`, `RunsIn.forEachFin`: the fixed-sequence builders of
  `SubNLogN/Machine/Contracts/Family.lean` (for example "for each child `i`: …; `recur 0`; …"),
  with an exact-stacks invariant `st i` and cost `(l.map T).sum + 1`.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

section Rules

variable {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

/-- **A call to an outer procedure**: `recur n` runs the body `b` of the `n`-th enclosing `fix`
in the environment `ρ.drop n`, plus the call/return cost `2`. -/
theorem RunsIn.recur {n : ℕ} {b : Prog K (fun _ => Sym) σ} (hb : ρ[n]? = some b)
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : RunsIn (ρ.drop n) b S S' Q T) :
    RunsIn ρ (.recur n) S S' Q (T + 2) :=
  Triple.recur_of_body hb h

/-- **Fixed sequences** (`forEachProg`), in any environment: step `i` runs from `st i` to
`st (i + 1)` within `T l[i]`. -/
theorem RunsIn.forEachProg {α : Type} (f : α → Prog K (fun _ => Sym) σ) (T : α → ℕ) (l : List α)
    (st : ℕ → K → List Sym)
    (h : ∀ (i : ℕ) (hi : i < l.length), RunsIn ρ (f l[i]) (st i) (st (i + 1)) (fun _ => True) (T l[i])) :
    RunsIn ρ (SubNLogN.Machine.forEachProg l f) (st 0) (st l.length) (fun _ => True)
      ((l.map T).sum + 1) := by
  have ht := SubNLogN.Machine.triple_forEachProg (ρ := ρ) f T l (fun i s => s.stk = st i)
    (fun i hi => Triple.post (h i hi) (fun _ hs => hs.1))
  exact Triple.post ht (fun _ hs => ⟨hs, trivial⟩)

/-- `forEachRange` in any environment. -/
theorem RunsIn.forEachRange (n : ℕ) (f : ℕ → Prog K (fun _ => Sym) σ) (T : ℕ → ℕ)
    (st : ℕ → K → List Sym)
    (h : ∀ i < n, RunsIn ρ (f i) (st i) (st (i + 1)) (fun _ => True) (T i)) :
    RunsIn ρ (SubNLogN.Machine.forEachRange n f) (st 0) (st n) (fun _ => True)
      (((List.range n).map T).sum + 1) := by
  have hr := RunsIn.forEachProg f T (List.range n) st (fun i hi => by
    have hi' : i < n := by simpa using hi
    simpa using h i hi')
  rw [List.length_range] at hr
  exact hr

/-- `forEachFin` in any environment (for example one step per role stack of a fixed family). -/
theorem RunsIn.forEachFin (n : ℕ) (f : Fin n → Prog K (fun _ => Sym) σ) (T : Fin n → ℕ)
    (st : ℕ → K → List Sym)
    (h : ∀ i : Fin n, RunsIn ρ (f i) (st (i : ℕ)) (st ((i : ℕ) + 1)) (fun _ => True) (T i)) :
    RunsIn ρ (SubNLogN.Machine.forEachFin n f) (st 0) (st n) (fun _ => True)
      (((List.finRange n).map T).sum + 1) := by
  have hr := RunsIn.forEachProg f T (List.finRange n) st (fun i hi => by
    have hi' : i < n := by simpa using hi
    simpa using h ⟨i, hi'⟩)
  rw [List.length_finRange] at hr
  exact hr

end Rules

#assert_std_axioms RunsIn.recur RunsIn.forEachProg RunsIn.forEachRange RunsIn.forEachFin

end SubNLogN.Machine.Calculus
