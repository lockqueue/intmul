import Lean

/-!
# `IntMulTM.Gate`: the G1 trust gate

Commands that inspect the *elaborated* environment (the kernel's constant table, not source tokens)
and make the build fail when a forbidden construct reaches a checked declaration.

* `#intmul_gate_check [d₁, …, dₖ]` checks the dependency cone of the given declarations.
* `#intmul_gate_modules P₁ … Pₖ` (identifiers or string literals) checks the cone of every constant
  defined in a module whose name has some `Pᵢ` as a component-wise prefix. The current file counts if
  its module name matches. A prefix that matches no module is an error, so a typo cannot pass
  vacuously.

Both log one message. Its first line is a machine-greppable summary,
`INTMUL_GATE: OK …` or `INTMUL_GATE: FAIL …`, followed by one line
`INTMUL_GATE: ERROR [kind] …` or `INTMUL_GATE: WARN [kind] …` per finding. On failure the message is
a Lean error, so the file, and hence its build target, fails to build. A pass with warnings is
logged as a Lean warning, a clean pass as information.

The test harness commands `#intmul_gate_expect` and `#intmul_gate_expect_modules` run the same
check and succeed iff the sets of error kinds and warning kinds are exactly the given ones.
`#intmul_gate_crosscheck` and `#intmul_gate_crosscheck_modules` check that the gate's axiom set
contains the one that `#print axioms` (`Lean.CollectAxioms`) computes from the same roots.

## The cone

The cone of a set of roots is the least set of constants that contains the roots and is closed
under "is mentioned by": the type of every constant, the value of definitions, theorems and
opaques, the constructors (and mutual siblings) of an inductive, the inductive of a constructor,
and the mutual inductives and rules of a recursor. This is a superset of what `#print axioms`
(`Lean.CollectAxioms`) traverses. The targets of `@[implemented_by]` and `@[extern]` are *not*
followed: the kernel never sees them.

## What is checked

| kind | severity | condition |
|---|---|---|
| `sorry` | error | `sorryAx` is in the cone |
| `native` | error | `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, `Lean.reduceBool` or `Lean.reduceNat` is in the cone (`native_decide`, `bv_decide`, …) |
| `axiom` | error | any other axiom outside `propext`, `Quot.sound`, `Classical.choice` is in the cone |
| `missing` | error | a mentioned constant is not in the kernel environment |
| `implemented_by` | error | a project constant in the cone has `@[implemented_by]` |
| `extern` | error | a project constant in the cone has `@[extern]` |
| `unsafe` | error | a project constant in the cone is `unsafe` |
| `partial` | warning | a project constant in the cone is a `partial def` |
| `opaque` | warning | a project constant in the cone is any other `opaque` |

*Project* constants are the ones defined outside the trusted library module prefixes
`trustedModulePrefixes` (Lean core, Std, Mathlib and Mathlib's dependencies); the current file is
always project code. The `sorry`, `native`, `axiom` and `missing` checks apply to the whole cone,
library included. The attribute and safety checks apply to project constants only: Lean core and
Mathlib necessarily use `@[extern]` and `@[implemented_by]` (`Nat.add`, `Array.foldlM`, …). Those
attributes change compiled code only, and no kernel-checked proof can observe compiled code once the
`native` kinds are excluded. Library constants carrying them are counted in the report.

The compiler's `f._unsafe_rec` copies of structurally or well-founded recursive definitions are
`partial` kernel definitions that no safe constant can mention; they are not reported.

## What is not checked

* Whether the statements mean what they should (specification honesty): that is gate G2.
* Declarations added without kernel checking (`set_option debug.skipKernelTC true`, or a
  metaprogram calling `Lean.Kernel.Environment.addDeclWithoutChecking`): the environment does not
  record this.
* Modules named under a trusted prefix (for example a project file `Mathlib/Foo.lean`) get only
  the whole-cone checks; the path policy of G1 must forbid them.
* Adversarial metaprograms in imported project modules (macros or elaborators that override these
  commands, `initialize` blocks): the gate runs in the same Lean process and cannot rule them out.
* As in `#print axioms`, the structure name inside a primitive projection `Expr.proj S i e` is not
  collected; in a well-typed closed term `S` is normally reached through the type of `e`.
* `@[csimp]` lemmas: kernel-checked theorems that only change compiled code; outside a declaration's
  cone, but checked as roots in module mode.
* In module mode, the current file's declarations *after* the command.
-/

namespace IntMulTM.Gate

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
  /-- `sorryAx` is in the cone. -/
  | sorryDep
  /-- A constant that trusts the compiler (`native_decide` and friends) is in the cone. -/
  | nativeDep
  /-- Another axiom outside the allow-list is in the cone. -/
  | badAxiom
  /-- A mentioned constant is not in the kernel environment. -/
  | missingConst
  /-- A project constant has `@[implemented_by]`. -/
  | implementedBy
  /-- A project constant has `@[extern]`. -/
  | externAttr
  /-- A project constant is `unsafe`. -/
  | unsafeDecl
  /-- A project constant is a `partial def` (warning). -/
  | partialDef
  /-- A project constant is another `opaque` (warning). -/
  | opaqueConst
  deriving BEq, Inhabited

namespace GateKind

/-- The tag printed in reports and accepted by `#intmul_gate_expect`. -/
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

/-- Errors fail the gate; warnings are only listed. -/
def isError : GateKind → Bool
  | .partialDef => false
  | .opaqueConst => false
  | _ => true

/-- All kinds, in report order. -/
def all : Array GateKind :=
  #[.sorryDep, .nativeDep, .badAxiom, .missingConst, .implementedBy, .externAttr, .unsafeDecl,
    .partialDef, .opaqueConst]

end GateKind

/-- One finding about one constant. -/
structure GateFinding where
  /-- What is wrong. -/
  kind : GateKind
  /-- The offending constant. -/
  const : Name
  /-- Extra text printed after the constant. -/
  detail : String := ""
  deriving Inhabited

/-- The result of running the gate on one cone. -/
structure GateReport where
  /-- The module that ran the check. -/
  mainModule : Name
  /-- `decls:…` or `modules:…`. -/
  scope : String
  /-- The roots of the cone. -/
  roots : Array Name
  /-- Number of constants inspected (the size of the cone). -/
  coneSize : Nat
  /-- Number of project constants in the cone. -/
  projectCount : Nat
  /-- Number of trusted library constants in the cone. -/
  libraryCount : Nat
  /-- All axioms in the cone. -/
  axioms : Array Name
  /-- All findings, in breadth-first order. -/
  findings : Array GateFinding
  /-- Breadth-first-search tree: the constant through which each non-root was first reached. -/
  parent : Std.HashMap Name Name
  /-- Direct users (in the cone) of each forbidden axiom or native constant. -/
  users : Std.HashMap Name (Array Name)
  /-- Library constants in the cone that carry `@[extern]`. -/
  libExtern : Nat
  /-- Library constants in the cone that carry `@[implemented_by]`. -/
  libImplementedBy : Nat
  /-- Project modules contributing to the cone, with constant counts. -/
  projectModules : Array (Name × Nat)

/-! ## Traversal -/

/-- The constants that a declaration mentions, in the kernel's view. -/
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

/-- Constants whose direct users are recorded: forbidden axioms and native-reduction constants. -/
def isForbiddenTarget (c : Name) (info? : Option ConstantInfo) : Bool :=
  match info? with
  | some (.axiomInfo _) => !allowedAxioms.contains c
  | _ => nativeConsts.contains c

/-- Is this a definition or an opaque constant? -/
def isDefnOrOpaque : Option ConstantInfo → Bool
  | some (.defnInfo _) => true
  | some (.opaqueInfo _) => true
  | _ => false

/-- Run the gate on the cone of `roots`: one breadth-first traversal of the kernel's constant
graph, visiting each constant once. -/
def runGate (env : Environment) (scope : String) (roots : Array Name) : GateReport := Id.run do
  -- The kernel environment; `toKernelEnv` waits for all pending asynchronous declarations.
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
            -- `f._unsafe_rec` is the compiler's copy of a recursive `f` (a definition, or the opaque
            -- of a `partial def`, which is reported itself). It is still traversed.
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

/-- Names sorted by their string form. -/
def sortNames (ns : Array Name) : Array Name :=
  ns.qsort fun a b => decide (a.toString < b.toString)

/-- `[a,b,c]`. -/
def bracket (xs : Array String) : String :=
  "[" ++ ",".intercalate xs.toList ++ "]"

/-- The first `k` items, comma-separated, then `,+N` for the rest. -/
def preview (xs : Array String) (k : Nat) : String :=
  let more := if xs.size > k then s!",+{xs.size - k}" else ""
  ",".intercalate (xs.toList.take k) ++ more

/-- Sorted, deduplicated tags. -/
def normTags (xs : Array String) : Array String :=
  xs.toList.eraseDups.toArray.qsort fun a b => decide (a < b)

/-- `a -> b -> c`, eliding the middle of long paths. -/
def pathStr (p : Array Name) : String :=
  let ss := p.toList.map toString
  let ss := if ss.length > 12 then ss.take 5 ++ ["..."] ++ ss.drop (ss.length - 6) else ss
  " -> ".intercalate ss

namespace GateReport

/-- Findings that fail the gate. -/
def errors (r : GateReport) : Array GateFinding := r.findings.filter (·.kind.isError)

/-- Findings that are only listed. -/
def warnings (r : GateReport) : Array GateFinding := r.findings.filter fun f => !f.kind.isError

/-- Did the gate pass? -/
def ok (r : GateReport) : Bool := r.errors.isEmpty

/-- A shortest dependency path from a root to `c`, along the breadth-first-search tree. -/
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

/-- The machine-greppable summary line. -/
def summaryLine (r : GateReport) : String :=
  let status := if r.ok then "OK" else "FAIL"
  let axs := bracket ((sortNames r.axioms).map toString)
  s!"INTMUL_GATE: {status} module={r.mainModule} scope={r.scope} roots={r.roots.size} " ++
    s!"n={r.coneSize} project={r.projectCount} library={r.libraryCount} axioms={axs} " ++
    s!"errors={r.errors.size} warnings={r.warnings.size}"

/-- The full report: summary line, one line per finding, then statistics. -/
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
        lines := lines.push (s!"INTMUL_GATE: {sev} [{k.tag}] {f.const}{f.detail}{usersStr}; " ++
          s!"path: {pathStr (r.pathTo f.const)}")
      i := i + 1
    if fs.size > maxLinesPerKind then
      lines := lines.push s!"INTMUL_GATE: {sev} [{k.tag}] ... and {fs.size - maxLinesPerKind} more"
  lines := lines.push s!"roots: {preview (r.roots.map toString) 5}"
  let mods := r.projectModules.map fun (m, cnt) => s!"{m}:{cnt}"
  lines := lines.push s!"project modules in cone: {preview mods 40}"
  lines := lines.push (s!"trusted library constants in cone: {r.libraryCount}, of which " ++
    s!"{r.libExtern} have @[extern] and {r.libImplementedBy} have @[implemented_by] " ++
    "(these affect compiled code only)")
  return "\n".intercalate lines.toList

end GateReport

/-! ## Commands -/

/-- Log a report: an error if the gate fails (so that the build fails), a warning if it passes with
warnings, information otherwise. -/
def emitReport (r : GateReport) : CommandElabM Unit := do
  let msg := r.render
  if !r.ok then
    logError m!"{msg}"
  else if !r.warnings.isEmpty then
    logWarning m!"{msg}"
  else
    logInfo m!"{msg}"

/-- Check a report against expected error and warning kinds (test harness). -/
def checkExpect (r : GateReport) (expErrs expWarns : Array String) : CommandElabM Unit := do
  let known := GateKind.all.map (·.tag)
  for k in expErrs ++ expWarns do
    unless known.contains k do
      throwError m!"INTMUL_GATE_TEST: unknown kind {k}; known kinds: {bracket known}"
  let gotE := normTags (r.errors.map (·.kind.tag))
  let gotW := normTags (r.warnings.map (·.kind.tag))
  let expE := normTags expErrs
  let expW := normTags expWarns
  let gate := if r.ok then "OK" else "FAIL"
  if gotE == expE && gotW == expW then
    logInfo m!"INTMUL_GATE_TEST: PASS scope={r.scope} gate={gate} errors={bracket gotE} \
      warnings={bracket gotW} (as expected)"
  else
    logError m!"INTMUL_GATE_TEST: FAIL scope={r.scope} expected errors={bracket expE} \
      warnings={bracket expW} but got errors={bracket gotE} warnings={bracket gotW}\n{r.render}"

/-- Test harness: the gate's axiom set must contain the one computed by `Lean.CollectAxioms`, the
traversal behind `#print axioms`, from the same roots. (The gate's cone has more edges, so its set
can only be larger.) -/
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
    logInfo m!"INTMUL_GATE_TEST: PASS crosscheck scope={r.scope} collectAxioms={theirsStr} \
      gate={oursStr} ({rel})"
  else
    logError m!"INTMUL_GATE_TEST: FAIL crosscheck scope={r.scope} collectAxioms={theirsStr} \
      gate={oursStr}: the gate missed an axiom"

/-- Resolve declaration identifiers (recording hover information). -/
def resolveDecls (ids : Array Ident) : CommandElabM (Array Name) := do
  if ids.isEmpty then
    throwError m!"INTMUL_GATE: FAIL empty declaration list"
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

/-- The scope string of a declaration-list check. -/
def declScope (roots : Array Name) : String :=
  s!"decls:{preview (roots.map toString) 3}"

/-- All constants defined in modules whose name has one of `prefixes` as a prefix, including the
current file's constants if the current module matches. Fails if nothing matches. -/
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
  if nMods == 0 then
    throwError m!"INTMUL_GATE: FAIL scope={scope}: no module matches; refusing to pass vacuously"
  if roots.isEmpty then
    throwError m!"INTMUL_GATE: FAIL scope={scope}: the matching modules define no constants"
  -- Sorted, so that the traversal order does not depend on hash-map iteration order.
  return (scope, sortNames roots)

/-- A module prefix: an identifier or a string literal. -/
def prefixOf (stx : Syntax) : CommandElabM Name := do
  if let some s := stx.isStrLit? then
    return s.toName
  else if stx.isIdent then
    return stx.getId
  else
    throwErrorAt stx "INTMUL_GATE: expected a module prefix (identifier or string literal)"

/-- `#intmul_gate_check [d₁, …, dₖ]` runs the G1 trust gate on the dependency cone of the given
declarations and fails the build if a forbidden construct is reachable. -/
syntax (name := gateCheckCmd) "#intmul_gate_check " "[" ident,* "]" : command

/-- `#intmul_gate_modules P₁ … Pₖ` runs the G1 trust gate on the dependency cone of every constant
defined in a module whose name has some `Pᵢ` (identifier or string literal) as a prefix. -/
syntax (name := gateModulesCmd) "#intmul_gate_modules " (ident <|> str)+ : command

/-- Test harness: `#intmul_gate_expect [d₁, …] errors ["kind", …] warnings ["kind", …]` runs the
gate and succeeds iff the error kinds and the warning kinds are exactly the given sets. -/
syntax (name := gateExpectCmd) "#intmul_gate_expect " "[" ident,* "]"
  &" errors " "[" str,* "]" &" warnings " "[" str,* "]" : command

/-- Test harness, module form:
`#intmul_gate_expect_modules [P₁, …] errors ["kind", …] warnings ["kind", …]`. -/
syntax (name := gateExpectModulesCmd) "#intmul_gate_expect_modules " "[" ident,* "]"
  &" errors " "[" str,* "]" &" warnings " "[" str,* "]" : command

/-- Test harness: `#intmul_gate_crosscheck [d₁, …]` checks that the gate's axiom set contains the
one `#print axioms` (`Lean.CollectAxioms`) computes from the same roots. -/
syntax (name := gateCrossCheckCmd) "#intmul_gate_crosscheck " "[" ident,* "]" : command

/-- Test harness, module form: `#intmul_gate_crosscheck_modules [P₁, …]`. -/
syntax (name := gateCrossCheckModulesCmd) "#intmul_gate_crosscheck_modules " "[" ident,* "]" :
  command

elab_rules : command
  | `(#intmul_gate_check [$ids,*]) => do
    let roots ← resolveDecls ids.getElems
    emitReport (runGate (← getEnv) (declScope roots) roots)
  | `(#intmul_gate_expect [$ids,*] errors [$es,*] warnings [$ws,*]) => do
    let roots ← resolveDecls ids.getElems
    checkExpect (runGate (← getEnv) (declScope roots) roots)
      (es.getElems.map (·.getString)) (ws.getElems.map (·.getString))
  | `(#intmul_gate_expect_modules [$ids,*] errors [$es,*] warnings [$ws,*]) => do
    let (scope, roots) ← moduleRoots (ids.getElems.map (·.getId))
    checkExpect (runGate (← getEnv) scope roots)
      (es.getElems.map (·.getString)) (ws.getElems.map (·.getString))
  | `(#intmul_gate_crosscheck [$ids,*]) => do
    let roots ← resolveDecls ids.getElems
    crossCheck (runGate (← getEnv) (declScope roots) roots)
  | `(#intmul_gate_crosscheck_modules [$ids,*]) => do
    let (scope, roots) ← moduleRoots (ids.getElems.map (·.getId))
    crossCheck (runGate (← getEnv) scope roots)

/-- Elaborator of `#intmul_gate_modules`. -/
@[command_elab gateModulesCmd]
def elabGateModules : CommandElab := fun stx => do
  let prefixes ← stx[1].getArgs.mapM prefixOf
  let (scope, roots) ← moduleRoots prefixes
  emitReport (runGate (← getEnv) scope roots)

end IntMulTM.Gate
