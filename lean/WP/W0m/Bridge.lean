import WP.W0m.Main
import Contracts.W8

/-!
# WP.W0m.Bridge — the input stage's outputs in the W8 interface's vocabulary

* The local schedule functions are the W8 contract's headline parameters
  (`IntMulTM.Contracts.W8.hB …`, CSWS:2264-2269), by `rfl`.
* `W0m_outputs` restates `outW` with these names. It adds the input bridge for
  `n = operandBits a b`: `a, b < 2^n` (the premise of `W8_machineInterface`) and
  `n ≤ L ≤ 2n + 1` (for the cost proof).
-/

namespace WP.W0m

open IntMulTM IntMulTM.Contracts TMFw.Contracts

theorem sB_eq_W8 (n : ℕ) : sB n = W8.hB n := rfl
theorem sK_eq_W8 (n : ℕ) : sK n = W8.hK n := rfl
theorem sK0_eq_W8 (n : ℕ) : sK0 n = W8.hK0 n := rfl
theorem sL_eq_W8 (n : ℕ) : sL n = W8.hL n := rfl
theorem sP0_eq_W8 (n : ℕ) : sP0 n = W8.hP0 n := rfl

/-- The outputs of the input stage, named as in the W8 interface, with the input bridge. -/
theorem W0m_outputs (a b : ℕ) :
    outW a b .oa = natSyms a ∧ outW a b .ob = natSyms b ∧
    outW a b .nn = natSyms (operandBits a b) ∧
    outW a b .bb = natSyms (W8.hB (operandBits a b)) ∧
    outW a b .kk = natSyms (W8.hK (operandBits a b)) ∧
    outW a b .k0 = natSyms (W8.hK0 (operandBits a b)) ∧
    outW a b .lf = natSyms (W8.hL (operandBits a b)) ∧
    outW a b .p0 = natSyms (W8.hP0 (operandBits a b)) ∧
    a < 2 ^ operandBits a b ∧ b < 2 ^ operandBits a b ∧
    operandBits a b ≤ (encNatPair.encode (a, b)).length ∧
    (encNatPair.encode (a, b)).length ≤ 2 * operandBits a b + 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, input_bridge a b⟩

#assert_std_axioms sB_eq_W8 sK_eq_W8 sK0_eq_W8 sL_eq_W8 sP0_eq_W8 W0m_outputs

end WP.W0m
