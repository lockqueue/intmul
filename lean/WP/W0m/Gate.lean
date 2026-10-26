import IntMulTM.Gate
import WP.W0m.Bridge
import WP.W0m.Smoke

/-!
# WP.W0m.Gate — G1 gate for the input stage
-/

#intmul_gate_modules WP.W0m

#intmul_gate_check [WP.W0m.W0m_inputStage_holds, WP.W0m.W0m_outputs, WP.W0m.workProg_runs,
  WP.W0m.inputStage_triple, WP.W0m.inputStage_closed, WP.W0m.workProg_closed]
