import Lean
/-!
指定したモジュール群（対象）が所有する宣言を、対象の外の本体の宣言がどこで使うかを書き出す。
使い方：lake env lean --run research/cleanup-zero-base/users.lean <対象モジュールの一覧> <出力.jsonl> [root モジュールの一覧のファイル]
出力は一行一宣言：{user, module, t: [型で使う対象の宣言], v: [値で使う対象の宣言]}。ソースは変えない。
-/
open Lean

unsafe def main (args : List String) : IO Unit := do
  let mods := (← IO.FS.lines args[0]!).toList.filter (· ≠ "") |>.map String.toName
  let out := args[1]!
  let roots : List Name ← match (args.drop 2).head? with
    | some f => do
        let ls ← IO.FS.lines (System.FilePath.mk f)
        pure (ls.toList.filter (· ≠ "") |>.map String.toName)
    | none => pure [`SerrePositivity]
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (roots.toArray.map fun m => {module := m}) {} (loadExts := false)
  let names := env.header.moduleNames
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  let mut target : NameSet := {}
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if modSet.contains names[idx.toNat]! then target := target.insert n
  IO.eprintln s!"target constants: {target.size}"
  let h ← IO.FS.Handle.mk out .write
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := names[idx.toNat]!
    if modSet.contains m then continue
    unless (`SerrePositivity).isPrefixOf m do continue
    let t := ci.type.getUsedConstants.filter target.contains
    let v := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants.filter target.contains | none => #[]
    if t.isEmpty && v.isEmpty then continue
    h.putStrLn (Json.mkObj [("user", toJson n.toString), ("module", toJson m.toString),
      ("t", toJson (t.map (·.toString))), ("v", toJson (v.map (·.toString)))]).compress
  h.flush
