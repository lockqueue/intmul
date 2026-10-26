import Lean

/-!
# `SubNLogN.Gate`: the kernel-environment trust gate

Commands that inspect the *elaborated* environment (the kernel's constant table, not source tokens)
and make the build fail when a forbidden construct reaches a checked declaration.

* `#subnlogn_gate_check [d₁, …, dₖ]` checks the dependency cone of the given declarations.
* `#subnlogn_gate_modules P₁ … Pₖ` (identifiers or string literals) checks the cone of every constant
  defined in a module whose name has some `Pᵢ` as a component-wise prefix. The current file counts if
  its module name matches. A prefix that matches no module is an error, so a typo cannot pass
  vacuously.
-/

namespace SubNLogN.Gate

open Lean Elab Command

/-! ## Policy -/

/-- The only axioms allowed in a checked cone. -/
def allowedAxioms : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]

/-- Axioms that put the Lean compiler and interpreter in the trusted base. -/
def nativeAxioms : Array Name := #[``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- Opaque constants that the kernel reduces by running compiled code. -/
def nativeConsts : Array Name := #[``Lean.reduceBool, ``Lean.reduceNat]

/-- Module-name prefixes of trusted library code: Lean core, Std, Lake, Mathlib and Mathlib's
dependencies. Constants of all other modules, and of the current file, are *project* constants. -/
def trustedModulePrefixes : Array Name :=
  #[`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient]

/-- At most this many detail lines are printed per finding kind. -/
def maxLinesPerKind : Nat := 25

/-- At most this many direct users are recorded per forbidden constant. -/
def maxUsers : Nat := 20

/-! ## Findings and reports -/

/-- The kind of a finding. -/
inductive GateKind where
  | sorryDep
  | nativeDep
  | badAxiom
  | missingConst
  | implementedBy
  | externAttr
  | unsafeDecl
  | partialDef
  | opaqueConst
  deriving BEq, Inhabited

namespace GateKind

def tag : GateKind → String
  | .sorryDep => "sorry"
  | .nativeDep => "native"
  | .badAxiom => "axiom"
  | .missingConst => "missing"
  | .implementedBy => "implemented_by"
  | .externAttr => "extern"
  | .unsafeDecl => "unsafe"
  | .partialDef => "partial"
  | .opaqueConst => "opaque"

def isError : GateKind → Bool
  | .partialDef => false
  | .opaqueConst => false
  | _ => true

def all : Array GateKind :=
  #[.sorryDep, .nativeDep, .badAxiom, .missingConst, .implementedBy, .externAttr, .unsafeDecl,
    .partialDef, .opaqueConst]

end GateKind

structure GateFinding where
  kind : GateKind
  const : Name
  detail : String := ""
  deriving Inhabited

structure GateReport where
  mainModule : Name
  scope : String
  roots : Array Name
  coneSize : Nat
  projectCount : Nat
  libraryCount : Nat
  axioms : Array Name
  findings : Array GateFinding
  parent : Std.HashMap Name Name
  users : Std.HashMap Name (Array Name)
  libExtern : Nat
  libImplementedBy : Nat
  projectModules : Array (Name × Nat)

/-! ## Traversal -/

def constDeps (info : ConstantInfo) : Array Name :=
  let push : Name → Array Name → Array Name := fun c cs => cs.push c
  let acc := info.type.getUsedConstants
  match info with
  | .defnInfo v => v.value.foldConsts acc push
  | .thmInfo v => v.value.foldConsts acc push
  | .opaqueInfo v => v.value.foldConsts acc push
  | .inductInfo v => acc ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => acc.push v.induct
  | .recInfo v => v.rules.foldl (fun acc r => r.rhs.foldConsts acc push) (acc ++ v.all.toArray)
  | .axiomInfo _ => acc
  | .quotInfo _ => acc

def isForbiddenTarget (c : Name) (info? : Option ConstantInfo) : Bool :=
  match info? with
  | some (.axiomInfo _) => !allowedAxioms.contains c
  | _ => nativeConsts.contains c

def isDefnOrOpaque : Option ConstantInfo → Bool
  | some (.defnInfo _) => true
  | some (.opaqueInfo _) => true
  | _ => false

def runGate (env : Environment) (scope : String) (roots : Array Name) : GateReport := Id.run do
  let kenv := env.toKernelEnv
  let modNames := env.allImportedModuleNames
  let trusted : Array Bool := modNames.map fun m => trustedModulePrefixes.any (·.isPrefixOf m)
  let mut visited : Std.HashSet Name := {}
  let mut parent : Std.HashMap Name Name := {}
  let mut queue : Array (Name × Option ConstantInfo) := #[]
  let mut forbidden : Std.HashSet Name := {}
  let mut users : Std.HashMap Name (Array Name) := {}
  for r in roots do
    unless visited.contains r do
      visited := visited.insert r
      let info? := kenv.find? r
      if isForbiddenTarget r info? then
        forbidden := forbidden.insert r
      queue := queue.push (r, info?)
  let mut axioms : Array Name := #[]
  let mut findings : Array GateFinding := #[]
  let mut projectCount := 0
  let mut libraryCount := 0
  let mut libExtern := 0
  let mut libImpl := 0
  let mut modCounts : Std.HashMap Name Nat := {}
  let mut head := 0
  while head < queue.size do
    let (c, info?) := queue[head]!
    head := head + 1
    match info? with
    | none =>
      findings := findings.push
        { kind := .missingConst, const := c, detail := " is not in the kernel environment" }
    | some info =>
      if info matches .axiomInfo _ then
        axioms := axioms.push c
        if c == ``sorryAx then
          findings := findings.push { kind := .sorryDep, const := c }
        else if nativeAxioms.contains c then
          findings := findings.push { kind := .nativeDep, const := c }
        else if !allowedAxioms.contains c then
          findings := findings.push { kind := .badAxiom, const := c }
      if nativeConsts.contains c then
        findings := findings.push
          { kind := .nativeDep, const := c,
            detail := " (the kernel reduces it by running compiled code)" }
      let modIdx? := env.getModuleIdxFor? c
      let isProject : Bool := match modIdx? with
        | some idx => !(trusted[idx.toNat]?.getD false)
        | none => true
      let impl? := Compiler.getImplementedBy? env c
      let ext := isExtern env c
      if isProject then
        projectCount := projectCount + 1
        let modName : Name := match modIdx? with
          | some idx => modNames[idx.toNat]?.getD .anonymous
          | none => env.mainModule
        modCounts := modCounts.insert modName (modCounts.getD modName 0 + 1)
        if info.isUnsafe then
          findings := findings.push { kind := .unsafeDecl, const := c }
        if let some impl := impl? then
          findings := findings.push
            { kind := .implementedBy, const := c, detail := s!" (implemented_by {impl})" }
        if ext then
          findings := findings.push { kind := .externAttr, const := c }
        match info with
        | .opaqueInfo _ =>
          if (kenv.find? (Compiler.mkUnsafeRecName c)).isSome then
            findings := findings.push { kind := .partialDef, const := c, detail := " (partial def)" }
          else if !info.isUnsafe && impl?.isNone && !ext then
            findings := findings.push { kind := .opaqueConst, const := c }
        | .defnInfo v =>
          if v.safety == DefinitionSafety.«partial» then
            let isAux : Bool := match Compiler.isUnsafeRecName? c with
              | some base => isDefnOrOpaque (kenv.find? base)
              | none => false
            if !isAux then
              findings := findings.push { kind := .partialDef, const := c }
        | _ => pure ()
      else
        libraryCount := libraryCount + 1
        if impl?.isSome then
          libImpl := libImpl + 1
        if ext then
          libExtern := libExtern + 1
      for d in constDeps info do
        unless visited.contains d do
          visited := visited.insert d
          parent := parent.insert d c
          let dInfo? := kenv.find? d
          if isForbiddenTarget d dInfo? then
            forbidden := forbidden.insert d
          queue := queue.push (d, dInfo?)
        if forbidden.contains d then
          let us := users.getD d #[]
          if us.back? != some c && us.size < maxUsers then
            users := users.insert d (us.push c)
  let projectModules := modCounts.toArray.qsort fun a b => decide (a.1.toString < b.1.toString)
  return {
    mainModule := env.mainModule, scope, roots, coneSize := queue.size, projectCount,
    libraryCount, axioms, findings, parent, users, libExtern, libImplementedBy := libImpl,
    projectModules }

/-! ## Rendering -/

def sortNames (ns : Array Name) : Array Name :=
  ns.qsort fun a b => decide (a.toString < b.toString)

def bracket (xs : Array String) : String :=
  "[" ++ ",".intercalate xs.toList ++ "]"

def preview (xs : Array String) (k : Nat) : String :=
  let more := if xs.size > k then s!",+{xs.size - k}" else ""
  ",".intercalate (xs.toList.take k) ++ more

def normTags (xs : Array String) : Array String :=
  xs.toList.eraseDups.toArray.qsort fun a b => decide (a < b)

def pathStr (p : Array Name) : String :=
  let ss := p.toList.map toString
  let ss := if ss.length > 12 then ss.take 5 ++ ["..."] ++ ss.drop (ss.length - 6) else ss
  " -> ".intercalate ss

namespace GateReport

def errors (r : GateReport) : Array GateFinding := r.findings.filter (·.kind.isError)

def warnings (r : GateReport) : Array GateFinding := r.findings.filter fun f => !f.kind.isError

def ok (r : GateReport) : Bool := r.errors.isEmpty

def pathTo (r : GateReport) (c : Name) : Array Name := Id.run do
  let mut path : Array Name := #[c]
  let mut cur := c
  let mut fuel := r.coneSize + 1
  while fuel > 0 do
    fuel := fuel - 1
    match r.parent[cur]? with
    | some p =>
      path := path.push p
      cur := p
    | none =>
      fuel := 0
  return path.reverse

def summaryLine (r : GateReport) : String :=
  let status := if r.ok then "OK" else "FAIL"
  let axs := bracket ((sortNames r.axioms).map toString)
  s!"SUBNLOGN_GATE: {status} module={r.mainModule} scope={r.scope} roots={r.roots.size} " ++
    s!"n={r.coneSize} project={r.projectCount} library={r.libraryCount} axioms={axs} " ++
    s!"errors={r.errors.size} warnings={r.warnings.size}"

def render (r : GateReport) : String := Id.run do
  let mut lines : Array String := #[r.summaryLine]
  for k in GateKind.all do
    let fs := r.findings.filter (·.kind == k)
    let sev := if k.isError then "ERROR" else "WARN"
    let mut i := 0
    for f in fs do
      if i < maxLinesPerKind then
        let us := r.users.getD f.const #[]
        let capped := if us.size ≥ maxUsers then s!" (first {maxUsers} recorded)" else ""
        let usersStr :=
          if us.isEmpty then "" else s!" (direct users: {preview (us.map toString) 10}{capped})"
        lines := lines.push (s!"SUBNLOGN_GATE: {sev} [{k.tag}] {f.const}{f.detail}{usersStr}; " ++
          s!"path: {pathStr (r.pathTo f.const)}")
      i := i + 1
    if fs.size > maxLinesPerKind then
      lines := lines.push s!"SUBNLOGN_GATE: {sev} [{k.tag}] ... and {fs.size - maxLinesPerKind} more"
  lines := lines.push s!"roots: {preview (r.roots.map toString) 5}"
  let mods := r.projectModules.map fun (m, cnt) => s!"{m}:{cnt}"
  lines := lines.push s!"project modules in cone: {preview mods 40}"
  lines := lines.push (s!"trusted library constants in cone: {r.libraryCount}, of which " ++
    s!"{r.libExtern} have @[extern] and {r.libImplementedBy} have @[implemented_by] " ++
    "(these affect compiled code only)")
  return "\n".intercalate lines.toList

end GateReport

/-! ## Commands -/

def emitReport (r : GateReport) : CommandElabM Unit := do
  let msg := r.render
  if !r.ok then
    logError m!"{msg}"
  else if !r.warnings.isEmpty then
    logWarning m!"{msg}"
  else
    logInfo m!"{msg}"

def checkExpect (r : GateReport) (expErrs expWarns : Array String) : CommandElabM Unit := do
  let known := GateKind.all.map (·.tag)
  for k in expErrs ++ expWarns do
    unless known.contains k do
      throwError m!"SUBNLOGN_GATE_TEST: unknown kind {k}; known kinds: {bracket known}"
  let gotE := normTags (r.errors.map (·.kind.tag))
  let gotW := normTags (r.warnings.map (·.kind.tag))
  let expE := normTags expErrs
  let expW := normTags expWarns
  let gate := if r.ok then "OK" else "FAIL"
  if gotE == expE && gotW == expW then
    logInfo m!"SUBNLOGN_GATE_TEST: PASS scope={r.scope} gate={gate} errors={bracket gotE} \
      warnings={bracket gotW} (as expected)"
  else
    logError m!"SUBNLOGN_GATE_TEST: FAIL scope={r.scope} expected errors={bracket expE} \
      warnings={bracket expW} but got errors={bracket gotE} warnings={bracket gotW}\n{r.render}"

def crossCheck (r : GateReport) : CommandElabM Unit := do
  let mut acc : Array Name := #[]
  for c in r.roots do
    for a in (← collectAxioms c) do
      unless acc.contains a do
        acc := acc.push a
  let theirs := sortNames acc
  let ours := sortNames r.axioms
  let theirsStr := bracket (theirs.map toString)
  let oursStr := bracket (ours.map toString)
  if theirs.all (ours.contains ·) then
    let rel := if theirs.size == ours.size then "equal" else "gate set is larger"
    logInfo m!"SUBNLOGN_GATE_TEST: PASS crosscheck scope={r.scope} collectAxioms={theirsStr} \
      gate={oursStr} ({rel})"
  else
    logError m!"SUBNLOGN_GATE_TEST: FAIL crosscheck scope={r.scope} collectAxioms={theirsStr} \
      gate={oursStr}: the gate missed an axiom"

def resolveDecls (ids : Array Ident) : CommandElabM (Array Name) := do
  if ids.isEmpty then
    throwError m!"SUBNLOGN_GATE: FAIL empty declaration list"
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

def declScope (roots : Array Name) : String :=
  s!"decls:{preview (roots.map toString) 3}"

def moduleRoots (prefixes : Array Name) : CommandElabM (String × Array Name) := do
  let env ← getEnv
  let header := env.header
  let modNames := header.moduleNames
  let mut roots : Array Name := #[]
  let mut nMods := 0
  let mut i := 0
  for m in modNames do
    if prefixes.any (·.isPrefixOf m) then
      nMods := nMods + 1
      if let some data := header.moduleData[i]? then
        roots := roots ++ data.constNames
    i := i + 1
  if prefixes.any (·.isPrefixOf env.mainModule) then
    nMods := nMods + 1
    roots := env.toKernelEnv.constants.foldStage2 (fun acc n _ => acc.push n) roots
  let scope := s!"modules:{",".intercalate (prefixes.map toString).toList}({nMods})"
  for p in prefixes do
    unless modNames.any (p.isPrefixOf ·) || p.isPrefixOf env.mainModule do
      throwError m!"SUBNLOGN_GATE: FAIL scope={scope}: prefix {p} matches no module; refusing to pass vacuously"
  if nMods == 0 then
    throwError m!"SUBNLOGN_GATE: FAIL scope={scope}: no module matches; refusing to pass vacuously"
  if roots.isEmpty then
    throwError m!"SUBNLOGN_GATE: FAIL scope={scope}: the matching modules define no constants"
  return (scope, sortNames roots)

def prefixOf (stx : Syntax) : CommandElabM Name := do
  if let some s := stx.isStrLit? then
    return s.toName
  else if stx.isIdent then
    return stx.getId
  else
    throwErrorAt stx "SUBNLOGN_GATE: expected a module prefix (identifier or string literal)"

syntax (name := gateCheckCmd) "#subnlogn_gate_check " "[" ident,* "]" : command

syntax (name := gateModulesCmd) "#subnlogn_gate_modules " (ident <|> str)+ : command

syntax (name := gateExpectCmd) "#subnlogn_gate_expect " "[" ident,* "]"
  &" errors " "[" str,* "]" &" warnings " "[" str,* "]" : command

syntax (name := gateExpectModulesCmd) "#subnlogn_gate_expect_modules " "[" ident,* "]"
  &" errors " "[" str,* "]" &" warnings " "[" str,* "]" : command

syntax (name := gateCrossCheckCmd) "#subnlogn_gate_crosscheck " "[" ident,* "]" : command

syntax (name := gateCrossCheckModulesCmd) "#subnlogn_gate_crosscheck_modules " "[" ident,* "]" :
  command

elab_rules : command
  | `(#subnlogn_gate_check [$ids,*]) => do
    let roots ← resolveDecls ids.getElems
    emitReport (runGate (← getEnv) (declScope roots) roots)
  | `(#subnlogn_gate_expect [$ids,*] errors [$es,*] warnings [$ws,*]) => do
    let roots ← resolveDecls ids.getElems
    checkExpect (runGate (← getEnv) (declScope roots) roots)
      (es.getElems.map (·.getString)) (ws.getElems.map (·.getString))
  | `(#subnlogn_gate_expect_modules [$ids,*] errors [$es,*] warnings [$ws,*]) => do
    let (scope, roots) ← moduleRoots (ids.getElems.map (·.getId))
    checkExpect (runGate (← getEnv) scope roots)
      (es.getElems.map (·.getString)) (ws.getElems.map (·.getString))
  | `(#subnlogn_gate_crosscheck [$ids,*]) => do
    let roots ← resolveDecls ids.getElems
    crossCheck (runGate (← getEnv) (declScope roots) roots)
  | `(#subnlogn_gate_crosscheck_modules [$ids,*]) => do
    let (scope, roots) ← moduleRoots (ids.getElems.map (·.getId))
    crossCheck (runGate (← getEnv) scope roots)

@[command_elab gateModulesCmd]
def elabGateModules : CommandElab := fun stx => do
  let prefixes ← stx[1].getArgs.mapM prefixOf
  let (scope, roots) ← moduleRoots prefixes
  emitReport (runGate (← getEnv) scope roots)

end SubNLogN.Gate
