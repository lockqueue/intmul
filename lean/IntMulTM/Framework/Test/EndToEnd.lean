import IntMulTM.Framework.Accept
import IntMulTM.Framework.IO

/-!
# Test: end-to-end acceptance instance + `#eval` harness

`idProg := copyIn; copyOut` over the production layout (one work stack) computes the identity on
`ℕ` with Mathlib's binary encoding. We derive the acceptance-theorem shape for it (non-vacuity of
`acceptance_of_spec`), and run the compiled `FinTM2` with a generic fuel-bounded harness.
-/

namespace TMFw.Test

open TMFw Turing Computability

/-- copy-in then copy-out (one work stack, index `()`). -/
def idProg : IOProg Unit finEncodingNatBool.Γ :=
  .seq (copyIn (fun b => Sym.bit b) ()) (copyOut ())

theorem idProg_spec (n : ℕ) :
    ∃ v t, Eval [] idProg ⟨none, inputStk (encodeNat n)⟩ ⟨v, outputStk (encodeNat n)⟩ t ∧
      t ≤ 6 * (encodeNat n).length + 5 := by
  set S0 : ∀ k : StackId Unit, List (StackId.Γ finEncodingNatBool.Γ k) :=
    inputStk (encodeNat n) with hS0
  have hin : S0 .input = encodeNat n := by simp [hS0, inputStk, stkOnly]
  have hw0 : S0 (.work ()) = [] := by simp [hS0, inputStk, stkOnly]
  have ho0 : S0 .output = [] := by simp [hS0, inputStk, stkOnly]
  have e1 := copyIn_eval (fun b => Sym.bit b) () [] none S0
  set S1 := Function.update (Function.update S0 .input []) (.work ())
    (((S0 .input).map (fun b => Sym.bit b)).reverse ++ S0 (.work ())) with hS1
  have hS1w : S1 (.work ()) = ((encodeNat n).reverse).map Sym.bit ++ [] := by
    rw [hS1, Function.update_self, hin, hw0, List.map_reverse]
  obtain ⟨t2, ht2, e2⟩ := copyOut_eval_encodeNat () [] none ((encodeNat n).reverse) [] S1
    TermOK.nil hS1w
  refine ⟨none, _, (Eval.seq e1 e2).of_eq ?_ rfl, ?_⟩
  · congr 1
    rw [List.reverse_reverse, bitsVal_encodeNat]
    apply StackId.stk_ext
    · simp [hS1, outputStk, stkOnly]
    · simp [hS1, ho0, outputStk, stkOnly]
    · intro w
      cases w
      simp [hS1, outputStk, stkOnly]
  · rw [hin]
    simp only [List.length_reverse] at ht2
    omega

/-- **Non-vacuity of the acceptance packaging**: identity on `ℕ`, linear time. -/
theorem id_acceptance :
    ∃ M : TM2ComputableInTime encodingNatBool.encode encodingNatBool.encode id,
      (∀ k, Finite (M.tm.Γ k)) ∧ ∃ C N₀, ∀ L ≥ N₀, M.time L ≤ C * L * Nat.log2 L :=
  acceptance_of_spec encodingNatBool id idProg none (fun L => 6 * L + 5)
    (fun n => idProg_spec n) (linear_nlogn 6 5)

/-! ## `#eval` harness -/

/-- Run a `FinTM2` from `initList` for at most `fuel` steps; `some (steps, output)` if it halts. -/
def runTM (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (fuel : ℕ) :
    Option (ℕ × List (tm.Γ tm.k₁)) :=
  go fuel 0 (initList tm input)
where
  /-- the loop -/
  go : ℕ → ℕ → tm.Cfg → Option (ℕ × List (tm.Γ tm.k₁))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match tm.step c with
      | none => some (n, c.stk tm.k₁)
      | some c' => go fuel (n + 1) c'

/-- The compiled identity machine (computable). -/
def idTM : FinTM2 := toFinTM2 (Γ := StackId.Γ finEncodingNatBool.Γ) .input .output idProg none

/-- Run the identity machine on `encodeNat n`. -/
def runId (n fuel : ℕ) : Option (ℕ × List Bool) := runTM idTM (encodeNat n) fuel

-- 11 = [1,1,0,1]: output [1,1,0,1]; steps = 3·4+2 + (2·4+4+3) + 1 = 30 ≤ 6·4+5+1.
#eval (runId 11 1000, runId 0 1000, runId 1024 1000)

#print axioms idProg_spec
#print axioms id_acceptance

end TMFw.Test
