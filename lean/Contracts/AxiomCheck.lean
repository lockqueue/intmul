import Contracts.W6
import Lean

/-!
Axiom audit for the contract modules. It uses the same mechanism as the snapshot's
`AxiomCheck.lean`: one shared `CollectAxioms` traversal over every constant defined in modules
under the `Contracts` prefix.
-/

open Lean Elab Command

elab "#contracts_axiom_union " pfx:ident : command => do
  let env ← getEnv
  let pfxName := pfx.getId
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      if pfxName.isPrefixOf (env.allImportedModuleNames[idx]!) then
        names := names.push n
    | none => pure ()
  let mut axs : Array Name := #[]
  for n in names do
    for a in (← collectAxioms n) do
      unless axs.contains a do
        axs := axs.push a
  logWarning m!"AXIOM_UNION: {names.size} constants under {pfxName}; union of reachable axioms = {axs}"

#contracts_axiom_union Contracts

#print axioms IntMulTM.Contracts.W8_parametricHeadline_holds
#print axioms IntMulTM.Contracts.W8_staticStride_sixP_row_holds
#print axioms IntMulTM.Contracts.W8_barrettEuclid_exact_holds
#print axioms IntMulTM.Contracts.W8_columnSolve_callSite_holds
#print axioms IntMulTM.Contracts.W8_columnDivisor_pos_of_faithful_holds
