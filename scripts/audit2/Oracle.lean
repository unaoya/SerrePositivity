import Lean

open Lean Meta

/-- A generated name can occur in several modules. For a shadowed
definition/theorem, add the exact type and value under a fresh name in a
temporary kernel-checked environment, then ask Lean about that record. -/
private def collectExact (env : Environment) (ci : ConstantInfo) : CoreM (Array Name) := do
  let probe := `Audit2.«shadowed record»
  if env.contains probe then throwError "audit probe name already exists"
  let decl ← match ci with
    | .thmInfo v => pure <| Declaration.thmDecl { v with name := probe, all := [probe] }
    | .defnInfo v => pure <| Declaration.defnDecl { v with name := probe, all := [probe] }
    | .opaqueInfo v => pure <| Declaration.opaqueDecl { v with name := probe, all := [probe] }
    | _ => throwError "cannot independently collect shadowed declaration {ci.name}"
  let env' ← ofExceptKernelException (env.addDeclCore 0 100000 decl none)
  withEnv env' <| collectAxioms probe

private def axiomRow (owner : Name) (ci : ConstantInfo) (axs : Array Name)
    (mode : String) : Json :=
  Json.arr #[toJson owner.toString, toJson ci.name.toString,
    toJson (axs.map Name.toString), toJson mode]

unsafe def main (args : List String) : IO Unit := do
  let [roots, requested, output, mode] := args
    | throw <| IO.userError "Oracle.lean ROOTS REQUESTED OUTPUT (all|missing)"
  unless mode == "all" || mode == "missing" do
    throw <| IO.userError "expected all or missing"
  let imports := (← IO.FS.lines roots).map (fun n => { module := n.toName : Import })
  let mut wanted : Std.HashMap Name (Std.HashSet String) := {}
  for line in ← IO.FS.lines requested do
    match line.splitOn "\t" with
    | [m] =>
      if mode != "all" then throw <| IO.userError s!"missing name: {line}"
      wanted := wanted.insert m.toName {}
    | [m, n] =>
      if mode != "missing" then throw <| IO.userError s!"unexpected name: {line}"
      let previous := wanted[m.toName]?.getD {}
      wanted := wanted.insert m.toName (previous.insert n)
    | _ => throw <| IO.userError s!"bad request: {line}"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules imports {} (leakEnv := true) (loadExts := true)
  let out ← IO.FS.Handle.mk output .write
  let mut visited : Std.HashSet Name := {}
  for i in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[i]!
    let some names := wanted[owner]? | continue
    visited := visited.insert owner
    let mut remaining := names
    let data := env.header.moduleData[i]!
    out.putStrLn (Json.arr #[toJson owner.toString, toJson data.constants.size]).compress
    for ci in data.constants do
      if mode == "missing" && !names.contains ci.name.toString then continue
      remaining := remaining.erase ci.name.toString
      let sameOwner := env.getModuleIdxFor? ci.name |>.any (·.toNat == i)
      let task : CoreM (Array Name) := if sameOwner then collectAxioms ci.name else collectExact env ci
      let axs ← task.toIO' {fileName := "<audit2-oracle>", fileMap := default, maxHeartbeats := 0}
        {env}
      out.putStrLn (axiomRow owner ci axs (if sameOwner then "import" else "owner-record")).compress
    unless remaining.isEmpty do
      throw <| IO.userError s!"{owner}: omitted {remaining.size} requested declarations, e.g. {remaining.toList.take 3}"
  unless visited.size == wanted.size do
    throw <| IO.userError s!"omitted modules: {wanted.size - visited.size}"
  out.flush
