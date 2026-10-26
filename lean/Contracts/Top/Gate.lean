import IntMulTM.Gate
import Contracts.Top.W12
import Contracts.Top.W11
import Contracts.Top.W10

/-!
# Contracts.Top.Gate — G1 gate for the top-level integration contracts
-/

#intmul_gate_modules Contracts.Top

#intmul_gate_check [IntMulTM.Contracts.Top.W12_assembly_holds,
  IntMulTM.Contracts.Top.W11_output_eq_mul, IntMulTM.Contracts.Top.W11_output_eq_mul_input,
  IntMulTM.Contracts.Top.nlogn_succ, IntMulTM.Contracts.Top.cost_le_at_inputLength]
