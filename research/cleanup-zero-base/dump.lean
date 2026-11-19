import Lean
open Lean Meta

def esc (s : String) : String := (toJson s).compress

unsafe def main (args : List String) : IO Unit := do
  let mods := (← IO.FS.lines args[0]!).toList.filter (· ≠ "") |>.map String.toName
  let out := args[1]!
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (mods.toArray.map fun m => {module := m}) {} (loadExts := true)
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  let names := env.header.moduleNames
  let h ← IO.FS.Handle.mk out .write
  let opts : Options := ({} : Options).insert `format.width (DataValue.ofNat 100)
  let ctx : Core.Context :=
    { fileName := "<dump>", fileMap := default, options := opts }
  let st : Core.State := {env}
  let work : MetaM Unit := do
    for (n, ci) in env.constants.toList do
      let some idx := env.getModuleIdxFor? n | continue
      let m := names[idx.toNat]!
      unless modSet.contains m do continue
      let kind := match ci with
        | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
        | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
      let tdeps := ci.type.getUsedConstants
      let vdeps := match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants | none => #[]
      let hasVal := (ci.value? (allowOpaque := true)).isSome
      let rng ← findDeclarationRanges? n
      let line := match rng with | some r => r.range.pos.line | none => 0
      let endLine := match rng with | some r => r.range.endPos.line | none => 0
      let doc ← findDocString? env n
      let inst ← isInstance n
      let isProp ← try isProp ci.type catch _ => pure false
      let ty ← try (do let f ← ppExpr ci.type; pure (f.pretty 100)) catch _ => pure "?"
      let ty := if ty.length > 1500 then (ty.take 1500).toString ++ " …" else ty
      let j := Json.mkObj [("name", toJson n.toString), ("module", toJson m.toString), ("kind", kind),
        ("inst", toJson inst), ("prop", toJson isProp), ("line", toJson line), ("endLine", toJson endLine),
        ("internal", toJson (n.isInternalDetail)), ("hasVal", toJson hasVal),
        ("doc", toJson (doc.getD "")), ("type", toJson ty),
        ("tdeps", toJson (tdeps.map (·.toString))), ("vdeps", toJson (vdeps.map (·.toString)))]
      h.putStrLn j.compress
  let _ ← (work.run' {} {}).toIO ctx st
  h.flush
