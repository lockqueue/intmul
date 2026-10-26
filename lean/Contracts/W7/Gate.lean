import Contracts.W7.Tables
import IntMulTM.Gate

/-!
# Contracts.W7.Gate — G1 trust gate over every `Contracts.W7.*` module

Checks every constant of every `Contracts.W7.*` module (no `sorry`, no `native_decide`-style
axioms, no non-standard axioms, no `implemented_by`/`extern`/`unsafe` in project code), and the
cone of the proved W7 theorems.
-/

#intmul_gate_modules Contracts.W7

#intmul_gate_check [TMFw.Contracts.W7_buildTables_of_ref, TMFw.Contracts.W7_deliverable_of_plan,
  TMFw.Contracts.W7_headline_compose, TMFw.Contracts.W7_tableCost_headline,
  TMFw.Contracts.W7.canonical_buildComputablePaperTables, TMFw.Contracts.W7.sameShape_of_faithful]
