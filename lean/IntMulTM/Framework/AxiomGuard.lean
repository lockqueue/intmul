import IntMulTM.Framework.Prog

/-!
# IntMulTM.Framework.AxiomGuard — a build-failing axiom check

`#assert_std_axioms c₁ c₂ …` fails the build unless every listed constant depends only on
`propext`, `Quot.sound` and `Classical.choice` (so `sorryAx`, `Lean.ofReduceBool` from
`native_decide`, and any user axiom are rejected). It also logs the axiom list of each constant, in
the same shape as `#print axioms`.

The Lean elaborator API used here (`collectAxioms`, `CommandElabM`) is in scope transitively through
Mathlib; no extra import is needed.
-/

namespace TMFw

open Lean Elab Command

/-- The axioms a finished proof may use. -/
def stdAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- `#assert_std_axioms c₁ c₂ …`: error unless each `cᵢ` depends only on `stdAxioms`. -/
elab "#assert_std_axioms " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !stdAxioms.contains a
    unless bad.isEmpty do
      throwErrorAt id "{n} depends on non-standard axioms: {bad} (all: {axs})"
    logInfo m!"{n} depends on axioms: {axs}"

end TMFw
