import IntMulTM.Framework.Accept
import IntMulTM.Framework.AxiomGuard
import IntMulTM.Spec

/-!
# Contracts.Top.W12 — assembly: from a top-level correctness triple to `IntMulTM.IntMulNLogN`

The last step of the project. Suppose a closed top-level program `P` over the production layout
(`StackId W`: the input stack over `PairSym`, the output stack over `Bool`, work stacks over `Sym`)
has these properties:
* for every input `(a, b)`, `P` runs from the initial machine state (input stack
  `encNatPair.encode (a, b)`, everything else empty, registers `σ0`) to a state whose stacks are
  exactly `outputStk (encodeNat (a * b))`, i.e. the binary product on the output stack and every
  other stack empty, within `T (input length)` source steps;
* `T L + 1 ≤ C·L·log₂ L` eventually. The `+ 1` is the wrapper's final cleanup step.

Then the acceptance statement `IntMulTM.IntMulNLogN` holds.

`P` stands for copy-in, the input stage (W0m), tables (W7), the level-synchronous pipeline (W9),
copy-out and cleanup. `W12_assembly_holds` is a thin wrapper over the framework's
`TMFw.acceptance_of_triple`, i.e. the exact compiler `TMFw.sim` plus the `TM2ComputableInTime`
packaging.
-/

namespace IntMulTM.Contracts.Top

open TMFw Computability

/-- **W12_assembly.** A closed top-level program with a correctness triple from the `encNatPair`
input to the `encodeNat (a * b)` output, whose cost `T` satisfies `T L + 1 ≤ C·L·log₂ L`
eventually, yields `IntMulNLogN`.

The closedness premise is not used by the proof. It records that the assembled program is a
self-contained `Prog` with no free `recur`. -/
def W12_assembly : Prop :=
  ∀ (W σ : Type) [DecidableEq W] [Fintype W] [Fintype σ]
    (P : Prog (StackId W) (StackId.Γ encNatPair.Γ) σ) (σ0 : σ) (T : ℕ → ℕ),
    P.Closed →
    (∀ a b : ℕ, Triple [] (· = ⟨σ0, inputStk (encNatPair.encode (a, b))⟩) P
      (fun s => s.stk = outputStk (encodeNat (a * b))) (T (encNatPair.encode (a, b)).length)) →
    (∃ C N₀ : ℕ, ∀ L ≥ N₀, T L + 1 ≤ C * L * Nat.log2 L) →
    IntMulNLogN

theorem W12_assembly_holds : W12_assembly := by
  intro W σ _ _ _ P σ0 T _ hspec hT
  obtain ⟨C, N₀, hC⟩ := hT
  exact acceptance_of_triple encNatPair (fun p => p.1 * p.2) P σ0 T (fun p => hspec p.1 p.2)
    ⟨C, N₀, fun L hL => by have := hC L hL; omega⟩

#assert_std_axioms W12_assembly_holds

end IntMulTM.Contracts.Top
