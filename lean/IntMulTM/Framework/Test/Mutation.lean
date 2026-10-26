import IntMulTM.Framework.Lib.Counter
import IntMulTM.Framework.Test.EndToEnd

/-!
# Tests: mutation (hidden work is caught by the cost), non-vacuity, counter machine runs

* `incMutant` hides an `O(L)` copy of the counter before incrementing. Determinism makes the cost
  intrinsic: any triple for the mutant must allow `≥ 7·|L| + 7` steps
  (`incMutant_cost_ge`), so it cannot meet the honest `inc` bound `6·ones L + 9`
  (`incMutant_not_inc_bound`, a concrete refutation).
* The compiled `inc` machine is run on small inputs (`#eval`), and the honest bound is checked.
-/

namespace TMFw.Test

open TMFw TMFw.Lib Turing Computability

variable {K : Type} [DecidableEq K]

/-- Mutant increment: first copy the whole counter to `junk` (hidden `O(L)` work), then `inc`. -/
def incMutant (k t junk : K) : SProg K := .seq (copyBlock k junk t) (inc k t)

/-- **Mutation test**: the hidden copy is visible in the cost of every valid triple. -/
theorem incMutant_cost_ge {k t junk : K} (hkj : k ≠ junk) (hkt : k ≠ t) (hjt : junk ≠ t)
    (ρ : List (SProg K)) (v : Option Sym) (L : List Bool) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = L.map Sym.bit ++ rest) {Q : SSt K → Prop} {T : ℕ}
    (h : Triple ρ (· = ⟨v, S⟩) (incMutant k t junk) Q T) : 7 * L.length + 7 ≤ T := by
  have e1 := copyBlock_eval hkj hkt hjt ρ v L rest S hrest hS
  obtain ⟨c, -, e2⟩ := inc_eval hkt ρ (some .mark) L rest
    (Function.update S junk (L.map Sym.bit ++ S junk)) hrest
    (by rw [Function.update_of_ne hkj]; exact hS)
  have := h.cost_ge rfl (Eval.seq e1 e2)
  omega

/-- The honest increment meets `6 · ones L + 9`. -/
theorem inc_triple {k t : K} (hkt : k ≠ t) (ρ : List (SProg K)) (v : Option Sym) (L : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hS : S k = L.map Sym.bit ++ rest) :
    Triple ρ (· = ⟨v, S⟩) (inc k t)
      (· = ⟨some .mark, Function.update S k ((incBits L).map Sym.bit ++ rest)⟩) (6 * ones L + 9) := by
  obtain ⟨c, hc, e⟩ := inc_eval hkt ρ v L rest S hrest hS
  exact (Triple.exact e).cost_mono hc

/-- Concrete refutation: on the counter `2 = [0,1]` (`ones = 0`), the mutant cannot meet the honest
`inc` bound `6 · 0 + 9 = 9`. -/
theorem incMutant_not_inc_bound :
    ¬ Triple ([] : List (SProg (Fin 3))) (· = ⟨none, fun _ => [Sym.bit false, Sym.bit true]⟩)
      (incMutant 0 1 2) (fun _ => True) (6 * ones [false, true] + 9) := by
  intro h
  have := incMutant_cost_ge (k := (0 : Fin 3)) (t := 1) (junk := 2) (by decide) (by decide)
    (by decide) [] none [false, true] [] (fun _ => [Sym.bit false, Sym.bit true]) TermOK.nil rfl h
  simp [ones] at this

/-! ## Non-vacuity: the honest bound is attained by real runs of the compiled machine -/

/-- The compiled counter machine: counter on stack `true`, temporary stack `false`. -/
def incTM : FinTM2 := toFinTM2 (Γ := fun _ : Bool => Sym) true true (inc true false) (none : Option Sym)

/-- Run `inc` on `encodeNat n`; returns (steps, counter as bits). -/
def runInc (n fuel : ℕ) : Option (ℕ × List Bool) :=
  (runTM incTM ((encodeNat n).map Sym.bit) fuel).map fun r =>
    (r.1, (r.2 : List Sym).map fun x => match x with | .bit b => b | _ => false)

-- 11 = [1,1,0,1] ↦ 12 = [0,0,1,1]: steps ≤ 6·2 + 9 + 1 = 22;  7 = [1,1,1] ↦ 8 = [0,0,0,1];
-- 0 ↦ 1.
#eval (runInc 11 1000, runInc 7 1000, runInc 0 1000, encodeNat 12, encodeNat 8)

#print axioms incMutant_cost_ge
#print axioms incMutant_not_inc_bound
#print axioms inc_triple

end TMFw.Test
