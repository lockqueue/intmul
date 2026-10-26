import Lean
open Lean

/-!
Environment statistics for the two headline modules: number of imported modules and number of
constants in the import closure (= what `leanchecker --fresh <module>` replays into a fresh kernel).
Run with `lake env lean --run replay/EnvStats.lean` from the project root.
-/

unsafe def stats (mod : Name) : IO Unit := do
  Lean.withImportModules #[{module := mod}] {} fun env => do
    let nMods := env.header.moduleNames.size
    let consts := env.constants.map₁
    let n := consts.size
    let mut nUnsafe := 0
    let mut nPartial := 0
    let mut nAx := 0
    let mut axs : Array Name := #[]
    let mut byKind : Std.HashMap String Nat := {}
    for (_, ci) in consts.toList do
      if ci.isUnsafe then nUnsafe := nUnsafe + 1
      if ci.isPartial then nPartial := nPartial + 1
      let k := match ci with
        | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      byKind := byKind.insert k (byKind.getD k 0 + 1)
      if let .axiomInfo _ := ci then
        nAx := nAx + 1
        axs := axs.push ci.name
    IO.println s!"module {mod}: {nMods} imported modules (incl. itself), {n} constants in the import closure"
    IO.println s!"  unsafe: {nUnsafe}, partial: {nPartial} (leanchecker skips unsafe/partial constants)"
    IO.println s!"  by kind: {byKind.toList}"
    IO.println s!"  axiom declarations present in the environment ({nAx}): {axs.qsort (·.toString < ·.toString)}"
    -- which top-level packages do the imported modules come from?
    let mut roots : Std.HashMap String Nat := {}
    for m in env.header.moduleNames do
      let r := m.getRoot.toString
      roots := roots.insert r (roots.getD r 0 + 1)
    IO.println s!"  imported modules by root namespace: {roots.toList}"

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  for a in args do
    stats a.toName
