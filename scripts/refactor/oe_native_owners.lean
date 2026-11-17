import Lean

/-!
Read native ownership for OE-W1 without computing expression fingerprints.
This tool does not check preservation. Final v3b capture/comparison remains mandatory.
-/
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [input, output] := args | throw <| IO.userError "usage: modules.json owners.json"
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile input)
  let names ← IO.ofExcept <| fromJson? (α := Array String) json
  let modules := names.map String.toName
  let selected := modules.foldl (init := ({} : NameSet)) fun s n => s.insert n
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun n => { module := n, importAll := true }) {}
    (loadExts := true)
  let rows := env.constants.fold (init := #[]) fun rows name _ => Id.run do
    let some index := env.getModuleIdxFor? name | return rows
    let owner := env.header.modules[index.toNat]!.module
    if !selected.contains owner then return rows
    return rows.push <| Json.mkObj [
      ("kernel_name", toJson name.toString),
      ("name", toJson (privateToUserName name).toString),
      ("module", toJson owner.toString),
      ("is_private", toJson (isPrivateName name))]
  let sorted := rows.qsort fun a b =>
    (a.getObjValAs? String "kernel_name").toOption.getD "" <
      (b.getObjValAs? String "kernel_name").toOption.getD ""
  IO.FS.writeFile output <| (Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("policy", toJson "Native owner inventory only; not a preservation comparison"),
    ("modules", toJson names), ("count", toJson sorted.size),
    ("declarations", toJson sorted)]).pretty ++ "\n"
  return 0
