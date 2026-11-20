import Lean
import Lake.Build.Trace

open Lean Meta

/-- The private part contains the full kernel records. Keep the first two
regions live until the private part has been read. -/
private unsafe def moduleParts (path : System.FilePath) :
    IO (Array (ModuleData × CompactedRegion)) := do
  let exported ← readModuleData path
  if !exported.1.isModule then return #[exported]
  let server ← CompactedRegion.read (α := ModuleData)
    (OLeanLevel.server.adjustFileName path) #[exported.2]
  let priv ← CompactedRegion.read (α := ModuleData)
    (OLeanLevel.private.adjustFileName path) #[exported.2, server.2]
  return #[exported, server, priv]

private structure ModuleEntries where
  axioms : Std.HashMap Name (Array Name) := {}
  instances : Std.HashMap Name (Array Json) := {}
  implementation : Std.HashMap Name Name := {}
  externs : Std.HashSet Name := {}

/-- Serialized entries are version-specific. The extension names and the
casts here correspond to the actual registered payload types in Lean. -/
private unsafe def entriesOf (parts : Array (ModuleData × CompactedRegion)) :
    ModuleEntries := Id.run do
  let mut r : ModuleEntries := {}
  for (part, _) in parts do
    for (ext, entries) in part.entries do
      if ext.toString.endsWith ".exportedAxiomsExt" then
        for ptr in entries do
          let (n, a) : Name × Array Name := unsafeCast ptr
          r := { r with axioms := r.axioms.insert n a }
      else if ext == instanceExtension.ext.name then
        for ptr in entries do
          let ent : Lean.ScopedEnvExtension.Entry InstanceEntry := unsafeCast ptr
          let (scope, i) := match ent with
            | .global x => (none, x)
            | .«scoped» n x => (some n, x)
          if let some n := i.globalName? then
            let row := Json.arr #[toJson (scope.map Name.toString), toJson i.priority]
            let prev := r.instances[n]?.getD #[]
            unless prev.contains row do
              r := { r with instances := r.instances.insert n (prev.push row) }
      else if ext == Lean.Compiler.implementedByAttr.ext.name then
        for ptr in entries do
          let (n, impl) : Name × Name := unsafeCast ptr
          r := { r with implementation := r.implementation.insert n impl }
      else if ext == Lean.externAttr.ext.name then
        for ptr in entries do
          let (n, _) : Name × Lean.ExternAttrData := unsafeCast ptr
          r := { r with externs := r.externs.insert n }
  return r

private def kind (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

private def strings (a : Array Name) : Json :=
  toJson (a.map Name.toString)

private def record (e : ModuleEntries) (n : Name) (ci : ConstantInfo)
    (visible : Bool) : Json :=
  let value := ci.value? true
  let ctors := match ci with | .inductInfo v => v.ctors.toArray | _ => #[]
  Json.arr #[toJson n.toString, toJson (kind ci), toJson visible,
    toJson (isPrivateName n), toJson n.isInternalDetail,
    toJson (toString (hash (ci.levelParams, ci.type))),
    toJson (value.map (fun v => toString (hash v))),
    strings ci.type.getUsedConstants, strings ((value.map Expr.getUsedConstants).getD #[]),
    strings ctors, toJson (e.axioms[n]?.map (·.map Name.toString)),
    toJson (e.instances[n]?.getD #[]), toJson ci.isUnsafe,
    toJson (e.implementation[n]?.map Name.toString), toJson (e.externs.contains n),
    toJson ci.isPartial]

private unsafe def extract (requests output : String) : IO Unit := do
  let out ← IO.FS.Handle.mk output .write
  for line in ← IO.FS.lines requests do
    let [owner, path] := line.splitOn "\t" | throw <| IO.userError s!"bad module row: {line}"
    let parts ← moduleParts path
    let some (pub, _) := parts[0]? | throw <| IO.userError owner
    let some (data, _) := parts.back? | throw <| IO.userError owner
    let entries := entriesOf parts
    let visible : Std.HashSet Name := pub.constNames.foldl (fun s n => s.insert n) {}
    let imports := data.imports.map fun i => i.module.toString
    out.putStrLn <| (Json.arr #[toJson owner, toJson imports,
      toJson data.constants.size]).compress
    for ci in data.constants do
      out.putStrLn <| (record entries ci.name ci (visible.contains ci.name)).compress
  out.flush

private def checkHashes (requests : String) : IO Unit := do
  let mut errors := 0
  for line in ← IO.FS.lines requests do
    let [path, expected] := line.splitOn "\t" | throw <| IO.userError s!"bad hash row: {line}"
    let digest ← Lake.computeBinFileHash path
    unless toString digest == expected do
      IO.eprintln s!"artifact hash mismatch: {path}: {digest} != {expected}"
      errors := errors + 1
  unless errors == 0 do throw <| IO.userError s!"{errors} artifact hashes differ"

unsafe def main (args : List String) : IO Unit :=
  match args with
  | ["extract", requests, output] => extract requests output
  | ["hashes", requests] => checkHashes requests
  | _ => throw <| IO.userError "Artifacts.lean (extract INPUT OUTPUT | hashes INPUT)"
