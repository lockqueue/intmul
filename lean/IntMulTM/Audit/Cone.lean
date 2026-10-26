import Lean
import IntMulTM.Gate

/-!
# `IntMulTM.Audit.Cone`: reports on dependency cones

Read-only report commands. Like the gate (`IntMulTM.Gate`), they inspect the kernel's
constant table after elaboration; they add nothing to any proof.

* `#intmul_cone_report d [q₁, …, qₖ]` reports the gate's dependency cone of the declaration `d`:
  - its size and axioms, and its project constants per module family;
  - the constants of the vendored snapshot (modules `IntMul.*`) per module;
  - which of the snapshot's 44 sealed cost primitives and 5 cost-monad combinators occur, with
    one shortest dependency path each;
  - the snapshot constants in the cone whose names mention a cost;
  - for each query `qᵢ`: whether it occurs, with one shortest dependency path from `d`. A query is
    a full constant name, or else a name suffix (all constants whose name ends with it).
* `#intmul_statement_boundary d` reports the *meaning cone* of a statement `d`: the same traversal,
  except that a theorem contributes only its type, never its proof. These are the definitions that
  fix what `d` says. The report lists them per module, and the command fails if one of them comes
  from a project module other than `d`'s own module.
* `#intmul_cone_excludes d [q₁, …]` fails if some query occurs in the cone of `d`, and
  `#intmul_cone_includes d [q₁, …]` fails unless every query occurs in it. Both fail on a query
  that names no constant, so they cannot pass vacuously. They freeze facts found with the report.
* `#intmul_not_imported [q₁, …]` fails if some query names a constant of the current environment.
  In a file that imports only a declaration's module, it shows that the queried constants are
  outside that declaration's import closure, hence outside its cone.

The cone is the gate's (`IntMulTM.Gate.runGate`): the type of every constant, the values of
definitions, theorems and opaques, the constructors and mutual siblings of inductives, and the
rules of recursors.
-/

namespace IntMulTM.Audit

open Lean Elab Command IntMulTM.Gate

/-! ## The vendored snapshot's cost layer -/

/-- Module prefix of `IntMul` (our independent pure-math and cost-monad specification of `[MS]`'s 2D multiplier). -/
def snapshotPrefix : Name := `IntMul

/-- The snapshot's 44 sealed cost primitives: the private list `sealedCostPrimitives` in the
snapshot's `IntMul.lean`. Its `CostMonadKernelLinter` trusts their prices by inspection. -/
def snapshotSealedPrimitives : Array Name := #[
  `IntMul.costedAddInt, `IntMul.costedSubInt, `IntMul.costedMulInt,
  `IntMul.costedDivRoundRatInt, `IntMul.costedGAdd, `IntMul.costedGSub,
  `IntMul.costedGAltTerm, `IntMul.costedZHomInit,
  `IntMul.costedGMulScaled, `IntMul.costedGRescale, `IntMul.costedGPreTwistU,
  `IntMul.costedGRatioQuantize, `IntMul.costedGCombineQuantize,
  `IntMul.costedGNyqStepQuantize, `IntMul.costedGNyqAltSumScale,
  `IntMul.costedGQuantizeCoordToScale, `IntMul.costedGQuantizeRat,
  `IntMul.costedButterflyAvg, `IntMul.costedPackSignedLeaf,
  `IntMul.costedCombineSignedPack, `IntMul.costedUnpackSignedSlot,
  `IntMul.costedSplitSignedPower, `IntMul.costedAddCarrySignedPower,
  `IntMul.costedSplitChunkLeaf, `IntMul.costedSplitChunkStep,
  `IntMul.costedReconstructChunkLeaf, `IntMul.costedReconstructChunkStep,
  `IntMul.accumBucketIntWithCost, `IntMul.computableNegacyclicDirectWithCost,
  `IntMul.costedNatSqrt, `IntMul.costedClampInt,
  `IntMul.costedShiftLeftNat, `IntMul.costedShiftLeftInt,
  `IntMul.costedNegInt0, `IntMul.costedCondNegInt0,
  `IntMul.costedSymmClampPow2Int, `IntMul.costedAddShiftLeftInt,
  `IntMul.costedSubShiftLeftInt, `IntMul.costedSubNatToInt0,
  `IntMul.costedSubNatAbsInt0, `IntMul.costedFoldRawTapRow,
  `IntMul.costedPackRootChunkPair, `IntMul.costedExtractRootSlot,
  `IntMul.recurrenceStepCosted]

/-- The snapshot's trusted cost-monad combinators: the private list `costMonadCombinators` in the
snapshot's `IntMul.lean`. -/
def snapshotCostCombinators : Array Name := #[
  `IntMul.BitCostM.tick, `IntMul.BitCostM.ofFnM, `IntMul.BitCostM.mapListM,
  `IntMul.runSequentialScanCostedSteps, `IntMul.runScan2DCostedWithSteps]

/-! ## Helpers -/

/-- The module that defines `c` (the current module for constants of this file). -/
def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => env.allImportedModuleNames[idx.toNat]?.getD .anonymous
  | none => env.mainModule

/-- Is `m` a trusted library module (Lean core, Std, Mathlib, …), by the gate's policy? -/
def isTrustedModule (m : Name) : Bool :=
  trustedModulePrefixes.any (·.isPrefixOf m)

/-- Is `c` in the cone of the report's roots? -/
def inCone (r : GateReport) (c : Name) : Bool :=
  r.roots.contains c || r.parent.contains c

/-- All constants of the cone: the roots and every constant reached from them. -/
def coneConsts (r : GateReport) : Array Name :=
  r.parent.fold (fun acc k _ => acc.push k) r.roots

/-- Does `n`'s component list end with `q`'s? -/
def isSuffixName (q n : Name) : Bool :=
  let qs := q.components
  let ns := n.components
  qs.length ≤ ns.length && ns.drop (ns.length - qs.length) == qs

/-- Resolve a query: the constant itself if it exists, else every constant whose name ends with
the query (component-wise; this also finds private names). Sorted. -/
def resolveQuery (env : Environment) (q : Name) : Array Name :=
  if env.contains q then #[q]
  else sortNames <| env.constants.fold (fun acc n _ => if isSuffixName q n then acc.push n else acc) #[]

/-- `a -> b -> c`, in full. -/
def fullPath (p : Array Name) : String :=
  " -> ".intercalate (p.toList.map toString)

/-- Does the name mention a cost (`Cost` or `cost` in its string form)? -/
def mentionsCost (c : Name) : Bool :=
  (c.toString.splitOn "ost").length > 1

/-! ## `#intmul_cone_report` -/

/-- The text of `#intmul_cone_report root [queries]`. -/
def coneReport (env : Environment) (root : Name) (queries : Array Name) : String := Id.run do
  let r := runGate env s!"decls:{root}" #[root]
  let consts := coneConsts r
  let axs := bracket ((sortNames r.axioms).map toString)
  let mut lines : Array String := #[
    s!"INTMUL_CONE: root={root} n={r.coneSize} project={r.projectCount} " ++
      s!"library={r.libraryCount} axioms={axs}"]
  -- Project constants per module family (first component of the module name).
  let mut fam : Std.HashMap Name Nat := {}
  for (m, k) in r.projectModules do
    let f := m.getRoot
    fam := fam.insert f (fam.getD f 0 + k)
  let famSorted := fam.toArray.qsort fun a b => decide (a.1.toString < b.1.toString)
  let famStrs := famSorted.map fun (f, k) => s!"{f}:{k}"
  lines := lines.push s!"INTMUL_CONE: project constants per module family: {", ".intercalate famStrs.toList}"
  -- The vendored snapshot, per module.
  let snapMods := r.projectModules.filter fun (m, _) => snapshotPrefix.isPrefixOf m
  let snapTotal := snapMods.foldl (fun acc (_, k) => acc + k) 0
  lines := lines.push
    s!"INTMUL_CONE: snapshot (IntMul.*) constants in cone: {snapTotal}, from {snapMods.size} modules"
  for (m, k) in snapMods do
    lines := lines.push s!"INTMUL_CONE:   {m}: {k}"
  -- The snapshot's sealed cost primitives and cost-monad combinators.
  let groups : Array (String × Array Name) :=
    #[("sealed cost primitives", snapshotSealedPrimitives),
      ("cost-monad combinators", snapshotCostCombinators)]
  for (label, names) in groups do
    let present := names.filter (inCone r)
    let undefined := names.filter fun c => !env.contains c
    lines := lines.push (s!"INTMUL_CONE: snapshot {label} in cone: {present.size}/{names.size} " ++
      s!"(not defined in this environment: {undefined.size})")
    for c in present do
      lines := lines.push s!"INTMUL_CONE:   {c}; path: {pathStr (r.pathTo c)}"
    let absent := names.filter fun c => env.contains c && !inCone r c
    unless absent.isEmpty do
      lines := lines.push s!"INTMUL_CONE:   not in cone: {", ".intercalate (absent.map toString).toList}"
    unless undefined.isEmpty do
      lines := lines.push
        s!"INTMUL_CONE:   not in this environment: {", ".intercalate (undefined.map toString).toList}"
  -- Snapshot constants whose names mention a cost.
  let costNamed := sortNames <| consts.filter fun c =>
    snapshotPrefix.isPrefixOf (moduleOf env c) && mentionsCost c
  lines := lines.push (s!"INTMUL_CONE: snapshot constants in cone whose name mentions a cost: " ++
    s!"{costNamed.size}: {preview (costNamed.map toString) 200}")
  -- Queries.
  for q in queries do
    let cands := resolveQuery env q
    if cands.isEmpty then
      lines := lines.push s!"INTMUL_CONE: query {q}: not in this environment, hence not in the cone"
    for c in cands do
      if inCone r c then
        lines := lines.push s!"INTMUL_CONE: query {q}: {c} IS in the cone; path: {fullPath (r.pathTo c)}"
      else
        lines := lines.push s!"INTMUL_CONE: query {q}: {c} is not in the cone"
  return "\n".intercalate lines.toList

/-! ## `#intmul_statement_boundary` -/

/-- The constants that fix the meaning of a declaration: as `IntMulTM.Gate.constDeps`, except that
a theorem contributes only its statement, never its proof. -/
def meaningDeps (info : ConstantInfo) : Array Name :=
  match info with
  | .thmInfo v => v.type.getUsedConstants
  | _ => constDeps info

/-- The meaning cone of `root`, breadth first: the constants in visiting order, the
breadth-first-search parent map, and the mentioned names missing from the kernel environment. -/
def meaningCone (env : Environment) (root : Name) :
    Array Name × Std.HashMap Name Name × Array Name := Id.run do
  let kenv := env.toKernelEnv
  let mut visited : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  let mut parent : Std.HashMap Name Name := {}
  let mut queue : Array Name := #[root]
  let mut missing : Array Name := #[]
  let mut head := 0
  while head < queue.size do
    let c := queue[head]!
    head := head + 1
    match kenv.find? c with
    | none => missing := missing.push c
    | some info =>
      for d in meaningDeps info do
        unless visited.contains d do
          visited := visited.insert d
          parent := parent.insert d c
          queue := queue.push d
  return (queue, parent, missing)

/-- A shortest path from the root to `c` along a breadth-first-search parent map. -/
def pathIn (parent : Std.HashMap Name Name) (c : Name) (fuel : Nat) : Array Name := Id.run do
  let mut path : Array Name := #[c]
  let mut cur := c
  let mut k := fuel
  while k > 0 do
    k := k - 1
    match parent[cur]? with
    | some p =>
      path := path.push p
      cur := p
    | none => k := 0
  return path.reverse

/-- Modules whose definitions are listed in full by `#intmul_statement_boundary` (besides the
statement's own module): the computability library that defines Turing machines and encodings. -/
def boundaryListedPrefixes : Array Name := #[`Mathlib.Computability]

/-- The verdict and text of `#intmul_statement_boundary root`. -/
def boundaryReport (env : Environment) (root : Name) : Bool × String := Id.run do
  let (consts, parent, missing) := meaningCone env root
  let home := moduleOf env root
  let mut perMod : Std.HashMap Name (Array Name) := {}
  for c in consts do
    let m := moduleOf env c
    perMod := perMod.insert m ((perMod.getD m #[]).push c)
  let mods := perMod.toArray.qsort fun a b => decide (a.1.toString < b.1.toString)
  let bad := mods.filter fun (m, _) => m != home && !isTrustedModule m
  let axs := sortNames <| consts.filter fun c =>
    match env.find? c with
    | some (.axiomInfo _) => true
    | _ => false
  let ok := bad.isEmpty && missing.isEmpty
  let status := if ok then "OK" else "FAIL"
  let mut lines : Array String := #[
    s!"INTMUL_BOUNDARY: {status} root={root} home={home} n={consts.size} modules={mods.size} " ++
      s!"outside_home_and_library={bad.size} missing={missing.size} " ++
      s!"axioms={bracket (axs.map toString)}"]
  for (m, cs) in bad do
    for c in sortNames cs do
      lines := lines.push
        s!"INTMUL_BOUNDARY: ERROR {c} from project module {m}; path: {fullPath (pathIn parent c consts.size)}"
  for c in missing do
    lines := lines.push s!"INTMUL_BOUNDARY: ERROR {c} is not in the kernel environment"
  lines := lines.push "INTMUL_BOUNDARY: definitions per module (listed in full for the statement's own module and Mathlib.Computability):"
  for (m, cs) in mods do
    if m == home || boundaryListedPrefixes.any (·.isPrefixOf m) then
      lines := lines.push s!"INTMUL_BOUNDARY:   {m} ({cs.size}): {", ".intercalate ((sortNames cs).map toString).toList}"
    else
      lines := lines.push s!"INTMUL_BOUNDARY:   {m} ({cs.size})"
  return (ok, "\n".intercalate lines.toList)

/-! ## Commands -/

/-- `#intmul_cone_report d [q₁, …, qₖ]`: report the dependency cone of `d`, with queries. -/
syntax (name := coneReportCmd) "#intmul_cone_report " ident "[" ident,* "]" : command

/-- `#intmul_statement_boundary d`: report the definitions that fix the meaning of `d`; fail if one
comes from a project module other than `d`'s own. -/
syntax (name := statementBoundaryCmd) "#intmul_statement_boundary " ident : command

/-- `#intmul_cone_excludes d [q₁, …]`: fail if some query occurs in the cone of `d`. -/
syntax (name := coneExcludesCmd) "#intmul_cone_excludes " ident "[" ident,* "]" : command

/-- `#intmul_cone_includes d [q₁, …]`: fail unless every query occurs in the cone of `d`. -/
syntax (name := coneIncludesCmd) "#intmul_cone_includes " ident "[" ident,* "]" : command

/-- `#intmul_not_imported [q₁, …]`: fail if some query names a constant of this environment. -/
syntax (name := notImportedCmd) "#intmul_not_imported " "[" ident,* "]" : command

/-- Check membership of queries in the cone of `root`. With `expectIn := true` every query must
occur, with `expectIn := false` none may. Unresolvable queries are errors. -/
def checkMembership (root : Name) (queries : Array Name) (expectIn : Bool) :
    CommandElabM Unit := do
  let env ← getEnv
  let r := runGate env s!"decls:{root}" #[root]
  let mut bad : Array String := #[]
  let mut good : Array String := #[]
  for q in queries do
    let cands := resolveQuery env q
    if cands.isEmpty then
      bad := bad.push s!"{q}: names no constant in this environment"
    else
      let hits := cands.filter (inCone r)
      if expectIn then
        if hits.isEmpty then
          bad := bad.push s!"{q}: not in the cone"
        else
          good := good.push s!"{q}: in the cone ({hits.size} match(es))"
      else
        for c in hits do
          bad := bad.push s!"{q}: {c} IS in the cone; path: {fullPath (r.pathTo c)}"
        if hits.isEmpty then
          good := good.push s!"{q}: not in the cone ({cands.size} constant(s) checked)"
  let kind := if expectIn then "includes" else "excludes"
  if bad.isEmpty then
    logInfo m!"INTMUL_CONE_EXPECT: OK {kind} root={root} n={r.coneSize}\n{"\n".intercalate good.toList}"
  else
    logError m!"INTMUL_CONE_EXPECT: FAIL {kind} root={root} n={r.coneSize}\n{"\n".intercalate bad.toList}"

elab_rules : command
  | `(#intmul_cone_report $d:ident [$qs,*]) => do
    let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
    logInfo m!"{coneReport (← getEnv) root (qs.getElems.map (·.getId))}"
  | `(#intmul_statement_boundary $d:ident) => do
    let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
    let (ok, msg) := boundaryReport (← getEnv) root
    if ok then logInfo m!"{msg}" else logError m!"{msg}"
  | `(#intmul_cone_excludes $d:ident [$qs,*]) => do
    let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
    checkMembership root (qs.getElems.map (·.getId)) false
  | `(#intmul_cone_includes $d:ident [$qs,*]) => do
    let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
    checkMembership root (qs.getElems.map (·.getId)) true
  | `(#intmul_not_imported [$qs,*]) => do
    let env ← getEnv
    let qs := qs.getElems.map (·.getId)
    let found := qs.filterMap fun q =>
      let cands := resolveQuery env q
      if cands.isEmpty then none else some s!"{q}: {", ".intercalate (cands.map toString).toList}"
    if found.isEmpty then
      logInfo m!"INTMUL_NOT_IMPORTED: OK none of {qs.size} queries names a constant here: \
        {", ".intercalate (qs.map toString).toList}"
    else
      logError m!"INTMUL_NOT_IMPORTED: FAIL these queries name constants here:\n\
        {"\n".intercalate found.toList}"

end IntMulTM.Audit
