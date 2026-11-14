import Lean

open Lean Elab Server
open Lean.Language.Lean (CommandParsedSnapshot)

private def span (stx : Syntax) : List (String × Json) :=
  match stx.getRange? with
  | none => []
  | some r => [("start", toJson r.start.byteIdx), ("stop", toJson r.stop.byteIdx)]

private def refRow (ref : Reference) : Option Json := do
  -- Explicit universes belong to the application, not the constant's name.
  -- Keep their exact source spelling and edit only the parsed identifier.
  let stx := if ref.stx.isOfKind ``Parser.Term.explicitUniv && ref.stx[0].isIdent then
      ref.stx[0] else ref.stx
  let kind := match ref.info with
    | .ofFieldInfo _ => "field"
    | .ofTermInfo _ =>
      if ref.isBinder then "binder" else if stx.isIdent then "term" else "syntax"
    | _ => "syntax"
  let (module, name, kind) := match ref.ident with
    | .const module name => (module, name, kind)
    | .fvar _ _ => ("", "", "local")
  let fields := span stx
  if fields.isEmpty then none else
    some <| Json.mkObj (fields ++ [("kind", toJson kind), ("module", toJson module),
      ("name", toJson name), ("namespace", toJson ref.ci.currNamespace.toString)])

private def scopeRow (kind : String) (stx : Syntax) (before after : Command.State) : Json :=
  Json.mkObj <| span stx ++ [
    ("kind", toJson kind), ("before", toJson before.scopes.length),
    ("after", toJson after.scopes.length),
    ("parent", toJson before.scopes.head!.currNamespace.toString),
    ("name", toJson after.scopes.head!.currNamespace.toString)]

private def resolveOpen (state : Command.State) (id : Name) : List Name :=
  if rootNamespace.isPrefixOf id then
    [removeRoot id]
  else
    let scope := state.scopes.head!
    ResolveName.resolveNamespace state.env scope.currNamespace scope.openDecls id

private def openRow (mode : String) (stx : Syntax) (id : Syntax) (state : Command.State) : Json :=
  let names := (resolveOpen state id.getId).map Name.toString
  Json.mkObj <| span id ++ [
    ("kind", toJson "open"), ("mode", toJson mode), ("names", toJson names),
    ("command", Json.mkObj (span stx))]

/-- Capture parsed namespace operands and structure field labels. Nested opens
    use the outer command's scope and are marked for conservative review. -/
private partial def syntaxRows (stx : Syntax) (state : Command.State) (top : Bool := true) (nested : Bool := false) : Array Json := Id.run do
  let kind := stx.getKind
  let mode :=
    if kind == ``Parser.Command.openSimple then "simple"
    else if kind == ``Parser.Command.openScoped then "scoped"
    else if kind == ``Parser.Command.openOnly then "only"
    else if kind == ``Parser.Command.openHiding then "hiding"
    else if kind == ``Parser.Command.openRenaming then "renaming"
    else ""
  if mode != "" then
    let ids := if mode == "simple" then stx[0].getArgs else
      if mode == "scoped" then stx[1].getArgs else #[stx[0]]
    return ids.map fun id => openRow (if nested then "local-" ++ mode else mode) stx id state
  if kind == ``Parser.Command.export then
    return #[openRow "export" stx stx[1] state]
  if kind == ``Parser.Command.«open» && top then
    return syntaxRows stx[1] state false nested
  -- For an open in a local term or macro, treat the entire construct as a guard.
  if stx.getArgs.any (fun arg =>
      [``Parser.Command.openSimple, ``Parser.Command.openScoped, ``Parser.Command.openOnly,
       ``Parser.Command.openHiding, ``Parser.Command.openRenaming].contains arg.getKind) then
    return stx.getArgs.flatMap fun arg =>
      syntaxRows arg state false true
  let children := stx.getArgs.flatMap fun arg => syntaxRows arg state false nested
  if kind == ``Parser.Term.structInstField then
    return #[Json.mkObj (span stx[0] ++ [("kind", toJson "record-label")])] ++ children
  return children

private partial def commandRows (state : Command.State) (cmd : CommandParsedSnapshot)
    (acc : Array Json := #[]) : Array Json := Id.run do
  let stx := cmd.stx
  let after := cmd.elabSnap.resultSnap.get.cmdState
  let mut acc := acc ++ syntaxRows stx state
  if stx.getKind == ``Parser.Command.namespace then
    acc := acc.push (scopeRow "namespace" stx[1] state after)
  else if stx.getKind == ``Parser.Command.«end» then
    acc := acc.push (scopeRow "end" stx[1] state after)
  else if stx.getKind == ``Parser.Command.withWeakNamespace then
    acc := acc.push (scopeRow "weak-namespace" stx state after)
  else if stx.getKind == ``Parser.Command.declaration then
    acc := acc.push <| Json.mkObj <| span stx ++ [("kind", toJson "declaration-command")]
  if let some next := cmd.nextCmdSnap? then
    commandRows after next.get acc
  else acc

unsafe def main (args : List String) : IO UInt32 := do
  if args.length < 3 || args.length > 4 then
    IO.eprintln "usage: lean --run klw1_collect_refs.lean MODULE SOURCE OUTPUT [SETUP.json]"
    return 2
  let [module, source, output] := args.take 3 | return 2
  let moduleSetup? ← (args[3]?).mapM (fun path : String => ModuleSetup.load path)
  let name ← moduleNameOfFileName source none
  if name.toString != module then
    IO.eprintln s!"source module mismatch: expected {module}, inferred {name}"
    return 2
  if let some config := moduleSetup? then
    if config.name != name && config.name != `_unknown then
      IO.eprintln s!"setup module mismatch: expected {name}, got {config.name}"
      return 2
  let input ← IO.FS.readFile source
  initSearchPath (← getBuildDir)
  enableInitializersExecution
  let ictx := Parser.mkInputContext input source
  let setup stx := do
    let config := moduleSetup?.getD { name }
    liftM <| config.dynlibs.forM Lean.loadDynlib
    return .ok {
      mainModuleName := name, package? := config.package?,
      imports := config.imports?.getD stx.imports,
      isModule := config.isModule || stx.isModule,
      importArts := config.importArts, plugins := config.plugins,
      -- Synchronous snapshots are the only intentional elaboration override.
      opts := Elab.async.set config.options.toOptions false
    }
  let snap ← Language.Lean.process setup none { ictx with }
  let snapshots := Language.toSnapshotTree snap
  if ← snapshots.runAndReport {} false then return 1
  let some header := snap.processedResult.get | return 1
  let trees := snapshots.getAll.flatMap fun s => s.infoTree?.toArray
  let refs := (findReferences ictx.fileMap trees).filterMap refRow
  let commands := commandRows header.cmdState header.firstCmdSnap.get
  IO.FS.writeFile output <| (Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("module", toJson module), ("source", toJson input),
    ("refs", toJson refs), ("commands", toJson commands),
    ("elaboration", Json.mkObj [
      ("configured", toJson moduleSetup?.isSome),
      ("setup_options", toJson (moduleSetup?.map (·.options) |>.getD {})),
      ("async", toJson false)])]).compress
  Runtime.forget snapshots
  return 0
