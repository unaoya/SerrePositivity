import Lean

open Lean Meta

private def binders (type : Expr) (value : Option Expr) : Array Json := Id.run do
  let mut type := type.consumeMData
  let mut value := value.map Expr.consumeMData
  let mut result := #[]
  while let .forallE name domain rest info := type do
    let (used, nextValue) := match value with
      | some (.lam _ _ body _) => (some (body.hasLooseBVar 0), some body.consumeMData)
      | _ => (none, none)
    let inst := info == .instImplicit
    let head := if inst then domain.getAppFn'.constName? else none
    result := result.push <| Json.arr #[toJson name.toString, toJson used,
      toJson (rest.hasLooseBVar 0), toJson inst, toJson (head.map Name.toString),
      toJson (domain.hasLooseBVars)]
    type := rest.consumeMData
    value := nextValue
  return result

private unsafe def inspectModule (path : System.FilePath) (out : IO.FS.Handle)
    (owner : String) (project : Bool) : IO Unit := do
  let (pub, pubRegion) ← readModuleData path
  let parts ← if pub.isModule then do
    let (server, serverRegion) ← CompactedRegion.read (α := ModuleData)
      (OLeanLevel.server.adjustFileName path) #[pubRegion]
    let (priv, _) ← CompactedRegion.read (α := ModuleData)
      (OLeanLevel.private.adjustFileName path) #[pubRegion, serverRegion]
    pure #[pub, server, priv]
  else pure #[pub]
  let mut registrations : Std.HashSet (Name × Option Name) := {}
  let mut classes : Std.HashSet Name := {}
  for part in parts do
    for (ext, entries) in part.entries do
      if ext == classExtension.name then
        for ptr in entries do
          let entry : ClassEntry := unsafeCast ptr
          unless classes.contains entry.name do
            classes := classes.insert entry.name
            out.putStrLn <| (Json.arr #[toJson "class", toJson owner,
              toJson entry.name.toString]).compress
        continue
      if ext != instanceExtension.ext.name then continue
      for ptr in entries do
        let entry : ScopedEnvExtension.Entry InstanceEntry := unsafeCast ptr
        let i : InstanceEntry := match entry with
          | .global i | .«scoped» _ i => i
        let className := match i.keys[0]? with
          | some (DiscrTree.Key.const n _) => some n
          | _ => none
        let registration := (i.globalName?.getD .anonymous, className)
        unless registrations.contains registration do
          registrations := registrations.insert registration
          out.putStrLn <| (Json.arr #[toJson "instance", toJson owner,
            toJson (i.globalName?.map Name.toString), toJson (className.map Name.toString)]).compress
  let some privatePart := parts.back? | throw <| IO.userError owner
  out.putStrLn <| (Json.arr #[toJson "module", toJson owner,
    toJson privatePart.constants.size]).compress
  if project then
    for ci in privatePart.constants do
      let rows := binders ci.type (ci.value? true)
      -- Empty telescope rows are accounted for by the per-module total.
      unless rows.isEmpty do
        out.putStrLn <| (Json.arr #[toJson "binders", toJson owner, toJson ci.name.toString,
          toJson rows]).compress

private unsafe def inspect (requests output : String) : IO Unit := do
  let out ← IO.FS.Handle.mk output .write
  for line in ← IO.FS.lines requests do
    let [scope, owner, path] := line.splitOn "\t" | throw <| IO.userError s!"bad row: {line}"
    unless scope == "project" || scope == "dependency" do
      throw <| IO.userError s!"bad scope: {scope}"
    inspectModule path out owner (scope == "project")
  out.flush

/-- Fresh traversal of kernel records. A per-root visited set handles recursive
declarations without reusing potentially incomplete results from another root. -/
private def walk (env : Environment) (start : Name) : IO (Array String × Nat) := do
  let mut visited : Std.HashSet Name := {}
  let mut axs := #[]
  let mut todo := #[start]
  while let some name := todo.back? do
    todo := todo.pop
    if visited.contains name then continue
    visited := visited.insert name
    let some ci := env.checked.get.find? name |
      throw <| IO.userError s!"{start}: dependency absent from kernel environment: {name}"
    if let .quotInfo _ := ci then continue
    if let .axiomInfo _ := ci then axs := axs.push name.toString
    if let .inductInfo val := ci then todo := todo ++ val.ctors.toArray
    todo := todo ++ ci.type.getUsedConstants
    if let some value := ci.value? true then todo := todo ++ value.getUsedConstants
  return (axs.qsort (· < ·), visited.size)

private def recompute (roots output : String) : IO Unit := do
  let owners := (← IO.FS.lines roots).map String.toName
  initSearchPath (← findSysroot)
  let before ← IO.monoMsNow
  let env ← importModules (owners.map fun n => { module := n }) {} (leakEnv := true)
  let loaded ← IO.monoMsNow
  let out ← IO.FS.Handle.mk output .write
  out.putStrLn <| (Json.arr #[toJson "environment", toJson env.header.moduleNames.size,
    toJson (loaded - before)]).compress
  let mut seen := 0
  for i in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[i]!
    unless owners.contains owner do continue
    seen := seen + 1
    for ci in env.header.moduleData[i]!.constants do
      unless env.getModuleIdxFor? ci.name |>.any (·.toNat == i) do
        throw <| IO.userError s!"shadowed root: {owner}: {ci.name}"
      let (axs, size) ← walk env ci.name
      out.putStrLn <| (Json.arr #[toJson owner.toString, toJson ci.name.toString,
        toJson axs, toJson size]).compress
  unless seen == owners.size do throw <| IO.userError "requested module absent"
  out.putStrLn <| (Json.arr #[toJson "traversal_ms", toJson ((← IO.monoMsNow) - loaded)]).compress
  out.flush

unsafe def main (args : List String) : IO Unit :=
  match args with
  | ["inspect", requests, output] => inspect requests output
  | ["walk", roots, output] => recompute roots output
  | _ => throw <| IO.userError "Inspection.lean (inspect REQUESTS | walk ROOTS) OUTPUT"
