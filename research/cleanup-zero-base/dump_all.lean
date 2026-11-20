import Lean
open Lean Meta

/-! 全モジュール用の軽い採取（塊に分けて実行できる）。使い方：
`lake env lean --run research/cleanup-zero-base/dump_all.lean <import するモジュールの一覧> <出力する接頭辞> <出すモジュールの一覧 または ALL>`
一つのプロセスで全モジュールを読むと vnode の上限（kern.maxvnodes、1 モジュールにつき 3〜4 ファイル）に届くので、root の閉包と残りを分けて読む。
定数は名前のハッシュ（`Name.hash`）で表すので、塊をまたいでつなげられる。
出力：<接頭辞>.modules.tsv（モジュール名・import する `SerrePositivity` のモジュール名）、<接頭辞>.decls.tsv（ハッシュ・名前・モジュール・種類・
instance・Prop・開始行・終了行・内部名か・docstring の長さ・値があるか・`SerrePositivity` の外の定数への依存数（型／値））、
<接頭辞>.deps.tsv（ハッシュ・型が使う本体の定数のハッシュ・値が使う本体の定数のハッシュ）、
<接頭辞>.xdeps.tsv（ハッシュ・型が使う本体の外の定数のハッシュ）、<接頭辞>.xnames.tsv（外の定数のハッシュと名前）。型の文字列は出さない。 -/

unsafe def main (args : List String) : IO Unit := do
  let mods := (← IO.FS.lines args[0]!).toList.filter (· ≠ "") |>.map String.toName
  let pre := args[1]!
  let emitAll := args[2]! == "ALL"
  let emit : NameSet ← if emitAll then pure {} else
    pure <| ((← IO.FS.lines args[2]!).toList.filter (· ≠ "") |>.map String.toName).foldl (·.insert ·) {}
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (mods.toArray.map fun m => {module := m}) {} (loadExts := true)
  let names := env.header.moduleNames
  let own (m : Name) : Bool := m.getRoot == `SerrePositivity
  let doEmit (m : Name) : Bool := own m && (emitAll || emit.contains m)
  let hm ← IO.FS.Handle.mk (pre ++ ".modules.tsv") .write
  for i in [0:names.size] do
    if doEmit names[i]! then
      let imps := env.header.moduleData[i]!.imports.filterMap fun im => if own im.module then some im.module.toString else none
      hm.putStrLn s!"{names[i]!}\t{" ".intercalate imps.toList}"
  hm.flush
  let ownConst (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some idx => own names[idx.toNat]! | none => false
  let hd ← IO.FS.Handle.mk (pre ++ ".decls.tsv") .write
  let he ← IO.FS.Handle.mk (pre ++ ".deps.tsv") .write
  let hx ← IO.FS.Handle.mk (pre ++ ".xdeps.tsv") .write
  let hn ← IO.FS.Handle.mk (pre ++ ".xnames.tsv") .write
  let seen ← IO.mkRef (∅ : Std.HashSet UInt64)
  let ctx : Core.Context := { fileName := "<dump>", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := {env}
  let work : MetaM Unit := do
    for (n, ci) in env.constants.toList do
      let some idx := env.getModuleIdxFor? n | continue
      let m := names[idx.toNat]!
      unless doEmit m do continue
      let kind := match ci with
        | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
        | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
      let tdeps := ci.type.getUsedConstants
      let v? := ci.value? (allowOpaque := true)
      let vdeps := match v? with | some v => v.getUsedConstants | none => #[]
      let tin := tdeps.filter ownConst
      let vin := vdeps.filter ownConst
      let rng ← findDeclarationRanges? n
      let line := match rng with | some r => r.range.pos.line | none => 0
      let endLine := match rng with | some r => r.range.endPos.line | none => 0
      let doc ← findDocString? env n
      let inst ← isInstance n
      let isProp ← match ci with
        | .thmInfo _ => pure true
        | _ => try withReducible (isProp ci.type) catch _ => pure false
      let b (x : Bool) := if x then 1 else 0
      let hs (a : Array Name) := " ".intercalate (a.toList.map fun x => toString x.hash)
      hd.putStrLn s!"{n.hash}\t{n}\t{m}\t{kind}\t{b inst}\t{b isProp}\t{line}\t{endLine}\t{b n.isInternalDetail}\t{(doc.getD "").length}\t{b v?.isSome}\t{tdeps.size - tin.size}\t{vdeps.size - vin.size}"
      he.putStrLn s!"{n.hash}\t{hs tin}\t{hs vin}"
      -- 型に現れる、本体の外（Mathlib など）の定数。名前は一度だけ xnames に出す
      let tout := tdeps.filter (fun x => !ownConst x)
      hx.putStrLn s!"{n.hash}\t{hs tout}"
      for x in tout do
        unless (← seen.get).contains x.hash do
          seen.modify (·.insert x.hash)
          hn.putStrLn s!"{x.hash}\t{x}"
  let _ ← (work.run' {} {}).toIO ctx st
  hd.flush; he.flush; hx.flush; hn.flush
