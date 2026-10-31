import Lean

/-!
## 概要
指定したビルド済みモジュールの公開宣言を、型・本体・公理・属性とともに保存する。
## 方針
表示文字列ではなく Expr の構造を直列化する。定理の証明は比較対象にしない。
## 規約
private のモジュール接頭辞を除き、補助宣言には親の名前を付ける。
## 使われ方
lake env lean --run scripts/refactor/decl_snapshot.lean --modules A,B --output before.json
--namespace N は選択を名前空間でも絞る。モジュール省略時は SerrePositivity を読む。
uses_modules は型・本体（定理の証明も含む）が使う定数の定義元。空の選択も count: 0 で保存する。
environment_parent は環境に存在する最長の真の名前接頭辞、parent_module はその定義元。
ソースとの照合と transient の分類は Python 側で行う。parent は従来のスナップショットとの互換用。
-/

open Lean

private def canonicalName (n : Name) : String := (privateToUserName n).toString

private def parentName : Name → Name
  | .str p s =>
    let ancestor := parentName p
    if ancestor != p then ancestor else
    if s.startsWith "_proof_" || s.startsWith "match_" || s.startsWith "_match_" ||
       s.startsWith "_aux_" then parentName p else .str p s
  | .num p _ => parentName p
  | .anonymous => .anonymous

private partial def environmentParent (env : Environment) (n : Name) : Option Name :=
  let p := n.getPrefix
  if p.isAnonymous then none
  else if env.contains p then some p else environmentParent env p

private def node (tag : String) (xs : List Json) : Json :=
  Json.arr (#[toJson tag] ++ xs.toArray)

private partial def levelData : Level → Json
  | .zero => node "zero" []
  | .succ l => node "succ" [levelData l]
  | .max a b => node "max" [levelData a, levelData b]
  | .imax a b => node "imax" [levelData a, levelData b]
  | .param n => node "param" [toJson (canonicalName n)]
  | .mvar n => node "level-mvar" [toJson (canonicalName n.name)]

private partial def exprData : Expr → Json
  | .bvar i => node "bvar" [toJson i]
  | .fvar i => node "fvar" [toJson (canonicalName i.name)]
  | .mvar i => node "mvar" [toJson (canonicalName i.name)]
  | .sort l => node "sort" [levelData l]
  | .const n ls => node "const" [toJson (canonicalName n), toJson (ls.map levelData)]
  | .app f a => node "app" [exprData f, exprData a]
  | .lam _ t b bi => node "lam" [toJson (reprStr bi), exprData t, exprData b]
  | .forallE _ t b bi => node "forall" [toJson (reprStr bi), exprData t, exprData b]
  | .letE _ t v b nondep => node "let" [exprData t, exprData v, exprData b, toJson nondep]
  | .lit (.natVal n) => node "nat" [toJson n]
  | .lit (.strVal s) => node "string" [toJson s]
  | .mdata _ b => exprData b
  | .proj n i b => node "proj" [toJson (canonicalName n), toJson i, exprData b]

private def declarationKind (env : Environment) (info : ConstantInfo) (inst : Bool) : String :=
  if inst then "instance" else
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo v => if v.hints == .abbrev then "abbrev" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => if isClass env info.name then "class" else if isStructure env info.name then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def snapshot (modules : Array Name) (namespacePrefix : Option Name) : CoreM Json := do
  let env ← getEnv
  let simp ← Meta.getSimpTheorems
  let mut rows : Array Json := #[]
  let constants := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  for (name, info) in constants do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    if namespacePrefix.isNone && !modules.contains mod then continue
    if let some selectedPrefix := namespacePrefix then
      unless selectedPrefix.isPrefixOf (privateToUserName name) do continue
    -- Private auxiliaries are retained and grouped with their public parent.
    -- Ordinary private declarations are not public API; their references still normalize.
    let normalized := privateToUserName name
    let ep := environmentParent env normalized
    let parent := parentName normalized
    let parentModule := ep.bind fun p => do
      let i ← env.getModuleIdxFor? p
      return env.header.modules[i.toNat]!.module.toString
    if isPrivateName name && parent == normalized then continue
    let ranges ← findDeclarationRanges? name
    let sourceRange := ranges.map fun r => Json.mkObj [
      ("start_line", toJson r.range.pos.line), ("end_line", toJson r.range.endPos.line),
      ("start_column", toJson r.range.pos.column), ("end_column", toJson r.range.endPos.column),
      ("selection_start_line", toJson r.selectionRange.pos.line),
      ("selection_end_line", toJson r.selectionRange.endPos.line)]
    let priority ← Meta.getInstancePriority? name
    let ty := exprData info.type
    let body := if info.isTheorem then none else (info.value? (allowOpaque := true)).map exprData
    let axs := (← collectAxioms name).toList.map canonicalName |>.mergeSort (· ≤ ·)
    let usedConstants := info.getUsedConstantsAsSet.toList
    let used := usedConstants.map canonicalName |>.mergeSort (· ≤ ·)
    let usedModules := (usedConstants.filterMap fun n => do
      let idx ← env.getModuleIdxFor? n
      return env.header.modules[idx.toNat]!.module.toString).mergeSort (· ≤ ·) |>.eraseDups
    let attrs := Json.mkObj [
      ("instance_priority", toJson priority),
      ("simp", toJson (simp.isLemma (.decl name) || simp.isLemma (.decl name false) ||
        simp.isLemma (.decl name true true) || simp.isLemma (.decl name false true) || simp.isDeclToUnfold name || simp.toUnfoldThms.contains name)),
      ("reducibility", toJson (reprStr (getReducibilityStatusCore env name))),
      ("expose", toJson (env.hasExposedBody name))]
    rows := rows.push <| Json.mkObj [
      ("name", toJson (canonicalName name)), ("parent", toJson parent.toString),
      ("environment_parent", toJson (ep.map canonicalName)), ("parent_module", toJson parentModule),
      ("source_range", toJson sourceRange),
      ("module", toJson mod.toString), ("kind", toJson (declarationKind env info priority.isSome)),
      ("type", ty), ("type_hash", toJson (toString (hash ty.compress))),
      ("body", toJson body), ("body_hash", toJson (body.map (fun j => toString (hash j.compress)))),
      ("axioms", toJson axs), ("attributes", attrs), ("used_constants", toJson used),
      ("used_modules", toJson usedModules), ("uses_modules", toJson usedModules)]
  let mut sources : Array Json := #[]
  for mod in modules do
    let path := mod.toString.replace "." "/" ++ ".lean"
    if ← System.FilePath.pathExists path then
      sources := sources.push <| Json.mkObj [("module", toJson mod.toString), ("source", toJson (← IO.FS.readFile path))]
  return Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("hash_algorithm", toJson "Lean String hash of canonical structural JSON; full structures included for name-map comparison"),
    ("modules", toJson (modules.map Name.toString)), ("sources", toJson sources),
    ("count", toJson rows.size), ("declarations", toJson rows)]

unsafe def main (args : List String) : IO UInt32 := do
  let mut modules : Array Name := #[]
  let mut namespacePrefix : Option Name := none
  let mut output : Option String := none
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--modules" :: value :: tail => modules := (value.splitOn ",").toArray.map String.toName; rest := tail
    | "--namespace" :: value :: tail => namespacePrefix := some value.toName; rest := tail
    | "--output" :: value :: tail => output := some value; rest := tail
    | _ => throw <| IO.userError "usage: --modules A,B [--namespace N] --output file.json"
  let some outputPath := output | throw <| IO.userError "--output is required"
  if modules.isEmpty then modules := #[`SerrePositivity]
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun n => { module := n, importAll := true }) {} (loadExts := true)
  let result ← (snapshot modules namespacePrefix).toIO' { fileName := "<decl_snapshot>", fileMap := default } { env := env }
  IO.FS.writeFile outputPath (result.pretty ++ "\n")
  IO.println s!"snapshot saved: {outputPath}"
  return 0
