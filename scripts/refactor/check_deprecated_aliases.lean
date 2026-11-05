/-
Validate namespace migration aliases, including kernel types, exact constant bodies,
attributes, safety, universes and axioms. An optional full alias map permits literal
alias expansion in types; each expanded constant body is independently checked.
-/
import Lean
open Lean Meta

def graphAxioms (env : Environment) (root : Name) : Json := Id.run do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut missing : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.checked.get.find? name | missing := missing.push name; continue
    pending := ci.type.getUsedConstants.toList ++ pending
    if let some value := ci.value? (allowOpaque := true) then
      pending := value.getUsedConstants.toList ++ pending
    match ci with
    | .axiomInfo _ => axioms := axioms.insert name
    | .inductInfo v => pending := v.ctors ++ pending
    | _ => pure ()
  return Json.mkObj [("name",toJson root.toString),
    ("axioms",toJson (axioms.toArray.qsort Name.quickLt |>.map Name.toString)),
    ("visited",toJson seen.size), ("missing",toJson (missing.map Name.toString))]

def checkAlias (mapping : NameMap Name) (row : Json) : MetaM Json := do
  let old := (← ofExcept (row.getObjValAs? String "old")).toName
  let new := (← ofExcept (row.getObjValAs? String "new")).toName
  let oi ← getConstInfo old
  let ni ← getConstInfo new
  let env ← getEnv
  let mut errors : Array String := #[]
  if isPrivateName old then errors := errors.push "private alias"
  if oi.numLevelParams != ni.numLevelParams then errors := errors.push "universe arity"
  let levels := ni.levelParams.mapIdx fun i _ => mkLevelParam <| Name.num `_f2_alias i
  let ot := oi.instantiateTypeLevelParams levels
  let nt := ni.instantiateTypeLevelParams levels
  let rawEq ← withReducible <| isDefEqGuarded ot nt
  -- Only literal delta expansion is allowed: validate every referenced alias
  -- against its actual kernel body before substituting a name in a type.
  let mut validated : NameMap Name := {}
  for n in ot.getUsedConstants ++ nt.getUsedConstants do
    if let some targetName := mapping.find? n then
      if let some info := (env.setExporting false).find? n then
        let expected := mkConst targetName (info.levelParams.map mkLevelParam)
        if info.value? (allowOpaque := true) == some expected then
          validated := validated.insert n targetName
        else errors := errors.push s!"normalization alias body mismatch: {n}"
      else errors := errors.push s!"normalization alias missing: {n}"
  let normalize (e : Expr) : Expr := e.replace fun e => match e with
    | .const n us => (validated.find? n).map fun target => mkConst target us
    | _ => none
  let exactNormalized := normalize ot == normalize nt
  unless rawEq || exactNormalized do errors := errors.push "type mismatch"

  let some val := oi.value? (allowOpaque := true) | throwError "alias has no value: {old}"
  let value := val.instantiateLevelParams oi.levelParams levels
  let target := mkConst new levels
  if value != target then errors := errors.push "body is not exactly the canonical constant"
  if ni.isTheorem != oi.isTheorem then errors := errors.push "theorem kind"
  if !ni.isTheorem && getReducibilityStatusCore env old != .reducible then errors := errors.push "not abbreviation"
  if (← getInstancePriority? old).isSome then errors := errors.push "duplicate instance registration"
  let simp ← getSimpTheorems
  if simp.isLemma (.decl old) || simp.isLemma (.decl old false) ||
      simp.isLemma (.decl old true true) || simp.isLemma (.decl old false true) ||
      simp.isDeclToUnfold old || simp.toUnfoldThms.contains old then
    errors := errors.push "duplicate simp registration"
  let rec binders : Expr → List BinderInfo
    | .forallE _ _ body info => info :: binders body
    | _ => []
  if binders oi.type != binders ni.type then errors := errors.push "binder annotations"
  if oi.isUnsafe != (ni.isUnsafe || ni.isPartial) then errors := errors.push "alias safety"

  if Linter.getDeprecatedNewName env old != some new then errors := errors.push "deprecated target"
  let date := (Linter.deprecatedAttr.getParam? env old).bind (·.since?)
  if date != some "2026-11-05" then errors := errors.push "deprecated date"
  let oa := (← collectAxioms old).toList.mergeSort Name.quickLt
  let na := (← collectAxioms new).toList.mergeSort Name.quickLt
  let mut freshAxioms := Json.null
  if oa != na then
    let og := graphAxioms env old
    let ng := graphAxioms env new
    let oldAxioms ← ofExcept <| og.getObjValAs? (Array String) "axioms"
    let newAxioms ← ofExcept <| ng.getObjValAs? (Array String) "axioms"
    let oldMissing ← ofExcept <| og.getObjValAs? (Array String) "missing"
    let newMissing ← ofExcept <| ng.getObjValAs? (Array String) "missing"
    freshAxioms := Json.mkObj [("old",og),("new",ng)]
    unless oldMissing.isEmpty && newMissing.isEmpty do
      errors := errors.push "incomplete axiom dependency graph"
    if oldAxioms != newAxioms then errors := errors.push "axioms differ"
  return Json.mkObj [("old",toJson old.toString),("new",toJson new.toString),
    ("cached_axioms_old",toJson (oa.map Name.toString)),("cached_axioms_new",toJson (na.map Name.toString)),("fresh_axioms",freshAxioms),("raw_reducible_type_check",toJson rawEq),("expanded_types_exactly_identical",toJson exactNormalized),("errors",toJson errors),("value_is_target_constant",toJson (value == target)),
    ("universe_parameters",toJson oi.numLevelParams)]

unsafe def runAliases (args : List String) : IO UInt32 := do
  let (input, output, mappingFile) ← match args with
    | [input, output] => pure (input, output, none)
    | [input, output, mapping] => pure (input, output, some mapping)
    | _ => throw <| IO.userError "usage: input.json output.json [normalization-aliases.json]"
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile input)
  let mods ← IO.ofExcept (j.getObjValAs? (Array String) "modules")
  let rows ← IO.ofExcept (j.getObjValAs? (Array Json) "aliases")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (mods.map fun s => {module := s.toName, importAll := true}) {} (loadExts := true)
  let mappingRows ← match mappingFile with
    | none => pure rows
    | some path => do
      let data ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
      IO.ofExcept <| fromJson? (α := Array Json) data
  let mapping := mappingRows.foldl (fun mp row => mp.insert
    ((row.getObjValAs? String "old").toOption.getD "").toName
    ((row.getObjValAs? String "new").toOption.getD "").toName) ({} : NameMap Name)
  let results ← (rows.mapM (checkAlias mapping)).run'.toIO' {fileName := "<f2-alias-check>",fileMap := default} {env := env}
  let failed := results.filter fun r => (r.getObjValAs? (Array String) "errors").toOption.getD #[] |>.isEmpty |>.not
  IO.FS.writeFile output ((Json.mkObj [("checked",toJson rows.size),("failed",toJson failed.size),("results",toJson results)]).pretty ++ "\n")
  return if failed.isEmpty then 0 else 1

unsafe def runAxiomGraph (args : List String) : IO UInt32 := do
  let [input, output] := args | throw <| IO.userError "input output"
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile input)
  let mods ← IO.ofExcept (j.getObjValAs? (Array String) "modules")
  let pairs ← IO.ofExcept (j.getObjValAs? (Array Json) "pairs")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (mods.map fun s => {module := s.toName, importAll := true}) {} (loadExts := true)
  let mut results := #[]
  for pair in pairs do
    let old ← IO.ofExcept <| pair.getObjValAs? String "old"
    let new ← IO.ofExcept <| pair.getObjValAs? String "new"
    let a := graphAxioms env old.toName
    let b := if old == new then a else graphAxioms env new.toName
    results := results.push <| Json.mkObj [("old",a),("new",b)]
  IO.FS.writeFile output ((toJson results).pretty ++ "\n")
  return 0

unsafe def main (args : List String) : IO UInt32 :=
  match args with
  | ["--axioms", input, output] => runAxiomGraph [input, output]
  | _ => runAliases args
