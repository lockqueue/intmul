import IntMulTM.Gate
import WP.W9comp.Kernels
import WP.W9comp.Smoke

/-!
# WP.W9comp.Gate — G1 trust gate for the W9 composites and kernel assembly

Module mode covers every constant of every `WP.W9comp.*` module (Kit, Shapes, PreProg, PreNode,
PostProg, PostNode, Kernels, Smoke). Declaration mode covers the cones of the main theorems.
-/

#intmul_gate_modules WP.W9comp

#intmul_gate_check [WP.W9comp.W9_preNode_of_phases_holds, WP.W9comp.W9_postNode_of_phases_holds,
  WP.W9comp.W9_kernels_of_machine_holds, WP.W9comp.W9_nodes_of_machine]
