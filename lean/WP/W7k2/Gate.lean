import IntMulTM.Gate
import WP.W7k2.Canon.Smoke
import WP.W7k2.B.Top
import WP.W7k2.ConcreteRun

/-!
# WP.W7k2.Gate — G1 gate for W7k2 (W7 kernels part 2 and the table-tape builder)

Main theorems: `W7_buildTablesRef_holds` (the table builder, `B/Top.lean`), `W7_colRecip_holds`
(`ColRecip.lean`), the canonical forms of the snapshot's table integers (`Canon/*`), and the builder's
layers (`buildProg_spec`, `levels_spec`, `stepPart_spec`, `leafPart_spec`).
-/

#intmul_gate_modules WP.W7k2

#intmul_gate_check [WP.W7k2.W7_buildTablesRef_holds, WP.W7k2.buildProg_spec, WP.W7k2.levels_spec,
  WP.W7k2.stepPart_spec, WP.W7k2.leafPart_spec, WP.W7k2.W7_colRecip_holds, WP.W7k2.tape_ref_eq,
  WP.W7k2.stdCharC_eq, WP.W7k2.tapC_eq, WP.W7k2.c0c1C_eq, WP.W7k2.colRecip_eq_colRecipC,
  WP.W7k2.T3_le_quad]
