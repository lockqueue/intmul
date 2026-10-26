import Contracts.W8
import IntMulTM.SpecFacts
import IntMulTM.Framework.AxiomGuard

/-!
# Contracts.Top.W11 — refinement interface: machine pipeline output = snapshot pipeline value

W11 closes the correctness chain of the parametric refinement route (`Contracts/W8.lean`, header
"Refinement route"):
1. W7: the machine's table hierarchy decodes to some `cSpec` with `TablesFaithful cSpec (W8.hSpec n)`.
2. W8: the TM-friendly reformulations equal the snapshot functions, for all inputs and tables.
3. **W9**: the level-synchronous pipeline (`Contracts.W9`) is bit-exact to the reformulations;
   `W11` is parameterized over the pipeline contract and output relation so it compiles independently.
4. W11 (this file): the machine pipeline's output equals
   `computablePaperFastDFTMultiply cSpec (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) A B` for the decoded
   hierarchy `cSpec`. By `W8_machineInterface_holds`, that value is `A * B`.

## Parameterized W9 interface

To decouple `W11` from `Contracts.W9`, `W11` takes two parameters:
* `W9 : Prop`, standing for the W9 pipeline contract;
* `MOut : ℕ → ℕ → ℕ → ℕ → Prop`, the machine pipeline's output relation. `MOut n A B out` means: run
  on the input-stage outputs for `(n, A, B)` (W0m) and on the machine's tables (W7), the pipeline
  leaves `natSyms out`.

`W11_refinement W9 MOut` is the refinement obligation. At top-level composition:
* instantiate `W9 :=` the W9 pipeline contract, and `MOut :=` the output relation of its program;
* the proof of `W11_refinement` is then: W9's triple, rewritten through the W8 reformulation
  equalities and the `_fst` bridges (`W8_costErasure`), with `cSpec` and its `TablesFaithful` proof
  from W7.

The consumer side is proved here (`W11_output_eq_mul`, `W11_output_eq_mul_input`). It needs nothing
beyond the obligation.
-/

namespace IntMulTM.Contracts.Top

open IntMul IntMulTM.Contracts

/-- **W11_refinement (parameterized refinement interface).** Under the W9 pipeline contract `W9`, every
machine pipeline output `out` on `(n, A, B)` with `A, B < 2^n` is the snapshot's parametric pipeline
value for a decoded table hierarchy `cSpec` faithful to the headline schedule `W8.hSpec n`. -/
def W11_refinement (W9 : Prop) (MOut : ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  W9 → ∀ n A B out : ℕ, A < 2 ^ n → B < 2 ^ n → MOut n A B out →
    ∃ cSpec : ComputablePaperFastDFTSpec, TablesFaithful cSpec (W8.hSpec n) ∧
      out = computablePaperFastDFTMultiply cSpec (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) A B

/-- **Consumer (proved):** refinement plus the W9 contract give the exact product, through
`W8_machineInterface`. -/
theorem W11_output_eq_mul {W9 : Prop} {MOut : ℕ → ℕ → ℕ → ℕ → Prop}
    (h : W11_refinement W9 MOut) (h9 : W9) {n A B out : ℕ} (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (ho : MOut n A B out) : out = A * B :=
  W8_machineInterface_holds n A B out hA hB (h h9 n A B out hA hB ho)

/-- **Consumer at the input stage's bit length (proved):** with `n = operandBits a b`, computed by
W0m, the operand-range premises come from the input bridge. -/
theorem W11_output_eq_mul_input {W9 : Prop} {MOut : ℕ → ℕ → ℕ → ℕ → Prop}
    (h : W11_refinement W9 MOut) (h9 : W9) {a b out : ℕ}
    (ho : MOut (operandBits a b) a b out) : out = a * b :=
  W11_output_eq_mul h h9 (input_bridge a b).1 (input_bridge a b).2.1 ho

#assert_std_axioms W11_output_eq_mul W11_output_eq_mul_input

end IntMulTM.Contracts.Top
