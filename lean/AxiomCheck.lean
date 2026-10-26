import IntMul
import Lean

open Lean Elab Command

/-- Fast axiom audit: one shared `CollectAxioms` traversal over every constant defined in modules
under the given prefix; reports the union of all reachable axioms. -/
elab "#axiom_union " pfx:ident : command => do
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

#axiom_union IntMul

#print axioms IntMul.computablePaperMultiplyOfBitLength_correct_and_isBigO
