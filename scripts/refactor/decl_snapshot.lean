import Lean

/-!
## 概要
指定したビルド済みモジュールの公開宣言を、型・本体・公理・属性とともに保存する。
## 方針
名前正規化後の Expr の DAG ハッシュを保存する。定理参照は型、生成定義参照は値を再帰的にハッシュする。
通常の定義参照は名前で区別する。Meta.transform で Prop の部分項を固定標識へ置き換え、定理自身の証明は比較対象にしない。
## 規約
private のモジュール接頭辞を除き、補助宣言には親の名前を付ける。
## 使われ方
lake env lean --run scripts/refactor/decl_snapshot.lean --modules A,B [--name-map names.json] --output before.json
--proof-irrelevant は既定で有効。--no-proof-irrelevant は旧方式の診断用（両側で同じ指定が必要）。
--stable-project は宣言の宇宙束縛を位置で正規化し、プロジェクトの公理依存をカーネル宣言から再計算する。
移動前後で使う場合は両側に同じ指定を渡す。
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

private abbrev Rename := String → String

private def orderedRename (rules : List (String × String)) (name : String) : String := Id.run do
  for (src, dst) in rules do
    if name == src || name.startsWith (src ++ ".") then
      return dst ++ (name.drop src.length).toString
  return name

private def indexedRename (rules : Std.HashMap String String) (name : String) : String := Id.run do
  if rules.isEmpty then return name
  let mut candidate := name
  let mut suffix := ""
  for part in (name.splitOn ".").reverse do
    if let some dst := rules[candidate]? then return dst ++ suffix
    candidate := (candidate.dropEnd (part.length + 1)).toString
    suffix := "." ++ part ++ suffix
  return name

private def hashName (rename : Rename) (n : Name) : String :=
  rename (canonicalName n)

-- The byte count describes the old compact structural JSON if expanded as a
-- tree. It is accumulated from children and never used to allocate a buffer.
private structure Digest where
  value : UInt64
  bytes : Nat
  recursive : Bool := false
  deriving Inhabited

private def scalar (j : Json) : Digest :=
  let encoded := j.compress
  ⟨hash encoded, encoded.utf8ByteSize, false⟩

private def arrayDigest (children : Array Digest) : Digest :=
  let seed := mixHash (hash "array") (hash children.size)
  children.foldl (init := ⟨seed, 2 + (children.size - 1), false⟩) fun acc c =>
    ⟨mixHash acc.value c.value, acc.bytes + c.bytes, acc.recursive || c.recursive⟩

private def tagged (tag : String) (args : Array Digest) : Digest :=
  arrayDigest (#[scalar (toJson tag)] ++ args)

private structure Memo where
  -- ExprStructEq uses full structural equality, including binder annotations.
  expressions : ExprStructMap Digest := {}
  levels : Std.HashMap Level Digest := {}
  unfolding : Array Name := #[]

private partial def levelDigest (rules : Rename) (l : Level) : StateM Memo Digest := do
  if let some result := (← get).levels[l]? then return result
  let child := levelDigest rules
  let result ← match l with
    | .zero => pure (tagged "zero" #[])
    | .succ a => do pure (tagged "succ" #[← child a])
    | .max a b => do pure (tagged "max" #[← child a, ← child b])
    | .imax a b => do pure (tagged "imax" #[← child a, ← child b])
    | .param n => pure (tagged "param" #[scalar (toJson (hashName rules n))])
    | .mvar n => pure (tagged "level-mvar" #[scalar (toJson (hashName rules n.name))])
  modify fun m => { m with levels := m.levels.insert l result }
  return result

-- Matchers are recognized by the environment extension, not a user-name prefix.
-- Other reserved elaborator suffixes are accepted only for definition constants.
private def generatedDefinition (env : Environment) (n : Name) : Bool :=
  (Meta.Match.Extension.getMatcherInfo? env n).isSome ||
  match n with
  | .str _ s => s == "_unsafe_rec" || s == "_sunfold" ||
      s.startsWith "_cstage" || s.startsWith "_spec_" || s.startsWith "_elambda"
  | _ => false

private partial def exprDigest (rules : Rename) (env : Option Environment)
    (proofIrrelevant : Bool) (e : Expr) : StateM Memo Digest := do
  if let some result := (← get).expressions[(e : ExprStructEq)]? then return result
  let child := exprDigest rules env proofIrrelevant
  let nameLeaf := fun n => scalar (toJson (hashName rules n))
  let result ← match e with
    | .bvar i => pure (tagged "bvar" #[scalar (toJson i)])
    | .fvar n => pure (tagged "fvar" #[nameLeaf n.name])
    | .mvar n => pure (tagged "mvar" #[nameLeaf n.name])
    | .sort l => do pure (tagged "sort" #[← levelDigest rules l])
    | .const n ls => do
      let replacement := do
        guard proofIrrelevant
        let env ← env
        let info ← env.find? n
        match info with
        | .thmInfo v => some ("proof", v.type.instantiateLevelParams v.levelParams ls)
        | .defnInfo v =>
          if generatedDefinition env n then
            some ("generated", v.value.instantiateLevelParams v.levelParams ls)
          else none
        | _ => none
      if let some (tag, value) := replacement then
        let stack := (← get).unfolding
        if let some idx := stack.toList.idxOf? n then
          -- Unsafe recursive auxiliaries can refer back to themselves. A stack
          -- distance is independent of their generated spelling. Digests with
          -- such a back-edge are not cached outside their unfolding context.
          let d := tagged "recursive-generated" #[scalar (toJson (stack.size - idx - 1))]
          pure { d with recursive := true }
        else
          modify fun m => { m with unfolding := stack.push n }
          let d ← child value
          modify fun m => { m with unfolding := stack }
          pure (tagged tag #[d])
      else
        let levels ← ls.mapM (levelDigest rules)
        pure (tagged "const" #[nameLeaf n, arrayDigest levels.toArray])
    | .app f a => do pure (tagged "app" #[← child f, ← child a])
    | .lam _ t b bi => do pure (tagged "lam" #[scalar (toJson (reprStr bi)), ← child t, ← child b])
    | .forallE _ t b bi => do pure (tagged "forall" #[scalar (toJson (reprStr bi)), ← child t, ← child b])
    | .letE _ t v b nd => do
      pure (tagged "let" #[← child t, ← child v, ← child b, scalar (toJson nd)])
    | .lit (.natVal n) => pure (tagged "nat" #[scalar (toJson n)])
    | .lit (.strVal v) => pure (tagged "string" #[scalar (toJson v)])
    | .mdata _ b => child b
    | .proj n i b => do pure (tagged "proj" #[nameLeaf n, scalar (toJson i), ← child b])
  unless result.recursive do
    modify fun m => { m with expressions := m.expressions.insert e result }
  return result

private def fingerprintWith (rename : Rename) (e : Expr)
    (env : Option Environment) (proofIrrelevant : Bool) : UInt64 × Nat × Nat :=
  let (d, memo) := (exprDigest rename env proofIrrelevant e).run {}
  (d.value, memo.expressions.size, d.bytes)

/-- DAG hash, distinct Expr count, and byte length of the hypothetical expanded encoding. -/
def DeclSnapshot.fingerprint (rules : List (String × String)) (e : Expr)
    (env : Option Environment := none) (proofIrrelevant : Bool := true) : UInt64 × Nat × Nat :=
  fingerprintWith (orderedRename rules) e env proofIrrelevant

/-- Erase proofs before DAG hashing, also under binders opened by Meta.transform. -/
def DeclSnapshot.eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    let isPrf ← try Meta.isProof e catch _ => pure false
    if isPrf then
      return .done (mkConst `_erased_proof)
    else return .continue)

private def termFingerprintWith (rename : Rename) (e : Expr)
    (proofIrrelevant : Bool) : MetaM (UInt64 × Nat × Nat) := do
  let normalized ← if proofIrrelevant then DeclSnapshot.eraseProofs e else pure e
  return fingerprintWith rename normalized (some (← getEnv)) proofIrrelevant

/-- Term-level proof irrelevance; the pure DAG hasher remains available for diagnostics. -/
def DeclSnapshot.termFingerprint (rules : List (String × String)) (e : Expr)
    (proofIrrelevant : Bool := true) : MetaM (UInt64 × Nat × Nat) :=
  termFingerprintWith (orderedRename rules) e proofIrrelevant

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

-- Resolve ambiguous generated names in one common import environment.
-- Source positions identify their parent; they do not select the defining module.
private def definingModule (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  return env.header.modules[idx.toNat]!.module

-- Lean's imported axiom cache is computed with a shared cycle sentinel.
-- An inductive and its constructor can reach the same axioms but export
-- different sets depending on which one is visited first. Compute the least
-- fixed point for project declarations, using unchanged dependencies as leaves.
private def projectAxioms (roots : Array Name) : MetaM (Std.HashMap Name NameSet) := do
  let env := (← getEnv).setExporting false
  let mut pending := roots
  let mut visited : Std.HashSet Name := {}
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut propagate : Array (Name × Name) := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if (definingModule env name).any (fun m => !((`SerrePositivity).isPrefixOf m)) then
      for ax in (← collectAxioms name) do
        propagate := propagate.push (name, ax)
      continue
    let some info := env.checked.get.find? name | continue
    if let .axiomInfo _ := info then
      propagate := propagate.push (name, name)
    if let .quotInfo _ := info then continue
    let mut deps := info.type.getUsedConstantsAsSet
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstantsAsSet
    if let .inductInfo val := info then
      deps := deps ++ NameSet.ofList val.ctors
    for dep in deps do
      users := users.insert dep ((users[dep]?.getD #[]).push name)
      if !visited.contains dep then pending := pending.push dep
  let mut result : Std.HashMap Name NameSet := {}
  while !propagate.isEmpty do
    let (name, ax) := propagate.back!
    propagate := propagate.pop
    let previous := result[name]?.getD {}
    if previous.contains ax then continue
    result := result.insert name (previous.insert ax)
    for user in users[name]?.getD #[] do
      propagate := propagate.push (user, ax)
  return result

private def snapshot (modules : Array Name) (namespacePrefix : Option Name)
    (rules : List (String × String)) (proofIrrelevant stableProject : Bool) : MetaM Json := do
  let rename := indexedRename (Std.HashMap.ofList rules)
  let env ← getEnv
  let simp ← Meta.getSimpTheorems
  let mut rows : Array Json := #[]
  let mut huge : Array Json := #[]
  let selected := modules.foldl (init := ({} : NameSet)) fun acc n => acc.insert n
  let constants := env.constants.fold (init := #[]) fun acc name info => Id.run do
    let some mod := definingModule env name | return acc
    let keep : Bool := match namespacePrefix with
      | some ns => ns.isPrefixOf (privateToUserName name)
      | none => selected.contains mod
    return if keep then acc.push (name, info, mod) else acc
  let exactAxioms ← if stableProject then projectAxioms (constants.map (·.1)) else pure {}
  for (name, info, mod) in constants.qsort (fun a b => Name.quickLt a.1 b.1) do
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
    -- Declaration universe parameters are binders. In particular, Lean's enum
    -- noConfusion declarations use fresh user names for them.
    let levelArgs := info.levelParams.zipIdx.map fun (_, i) =>
      mkLevelParam (.num `_snapshotLevel i)
    let fingerprint := fun e => termFingerprintWith rename
      (if stableProject then e.instantiateLevelParams info.levelParams levelArgs else e) proofIrrelevant
    let ty ← fingerprint info.type
    let body ← if info.isTheorem then pure none else
      (info.value? (allowOpaque := true)).mapM fingerprint
    for (field, stat) in [("type", some ty), ("body", body)] do
      if let some (_, distinct, bytes) := stat then
        if bytes > 1000000000 then
          huge := huge.push <| Json.mkObj [("module", toJson mod.toString),
            ("name", toJson name.toString), ("field", toJson field),
            ("distinct_subexpressions", toJson distinct), ("expanded_bytes", toJson bytes)]
    let axioms ← if stableProject then pure ((exactAxioms[name]?.getD {}).toArray) else collectAxioms name
    let axs := axioms.toList.map canonicalName |>.mergeSort (· ≤ ·)
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
      ("reference_kind", toJson (if info.isTheorem then "proof" else
        if generatedDefinition env name && (match info with | .defnInfo _ => true | _ => false)
        then "generated" else "named")),
      ("module", toJson mod.toString), ("kind", toJson (declarationKind env info priority.isSome)),
      ("type_hash", toJson (toString ty.1)), ("body_hash", toJson (body.map fun x => toString x.1)),
      ("axioms", toJson axs), ("attributes", attrs), ("used_constants", toJson used),
      ("used_modules", toJson usedModules), ("uses_modules", toJson usedModules)]
  let mut sources : Array Json := #[]
  for mod in modules do
    let path := mod.toString.replace "." "/" ++ ".lean"
    if ← System.FilePath.pathExists path then
      sources := sources.push <| Json.mkObj [("module", toJson mod.toString), ("source", toJson (← IO.FS.readFile path))]
  return Json.mkObj [("schema_version", toJson (2 : Nat)),
    ("hash_algorithm", toJson ((if proofIrrelevant then "normalized Expr DAG mixHash proof-irrelevant v3b (term-level, proof marker)" else "normalized Expr DAG mixHash v1") ++
      (if stableProject then " with bound universe parameters and project kernel axiom reachability" else ""))),
    ("proof_irrelevant", toJson proofIrrelevant),
    ("huge_terms", toJson huge), ("name_map", Json.mkObj (rules.map fun (k, v) => (k, toJson v))),
    ("modules", toJson (modules.map Name.toString)), ("sources", toJson sources),
    ("count", toJson rows.size), ("declarations", toJson rows)]

unsafe def main (args : List String) : IO UInt32 := do
  let mut modules : Array Name := #[]
  let mut namespacePrefix : Option Name := none
  let mut output : Option String := none
  let mut ownerNames : Option (List String) := none
  let mut rules : List (String × String) := []
  let mut proofIrrelevant := true
  let mut stableProject := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--stable-project" :: tail => stableProject := true; rest := tail
    | "--proof-irrelevant" :: tail => proofIrrelevant := true; rest := tail
    | "--no-proof-irrelevant" :: tail => proofIrrelevant := false; rest := tail
    | "--modules" :: value :: tail => modules := (value.splitOn ",").toArray.map String.toName; rest := tail
    | "--namespace" :: value :: tail => namespacePrefix := some value.toName; rest := tail
    | "--resolve-modules" :: path :: tail =>
      let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
      ownerNames := some (← IO.ofExcept (fromJson? (α := List String) json))
      rest := tail
    | "--name-map" :: path :: tail =>
      let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
      let obj ← IO.ofExcept json.getObj?
      rules ← obj.toList.mapM fun (k, v) => do return (k, ← IO.ofExcept v.getStr?)
      rules := rules.mergeSort (fun a b => a.1.length > b.1.length)
      rest := tail
    | "--output" :: value :: tail => output := some value; rest := tail
    | _ => throw <| IO.userError "usage: --modules A,B [--namespace N] [--name-map names.json] [--stable-project] --output file.json"
  let some outputPath := output | throw <| IO.userError "--output is required"
  if modules.isEmpty then modules := #[`SerrePositivity]
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun n => { module := n, importAll := true }) {} (loadExts := true)
  if let some names := ownerNames then
    let wanted := Std.HashSet.ofList names
    let byCanonical := env.constants.fold (init := ({} : Std.HashMap String (List Name))) fun acc raw _ => Id.run do
      let key := canonicalName raw
      if !wanted.contains key then return acc
      return acc.insert key (raw :: acc.getD key [])
    let owners ← names.mapM fun key => do
      let raws := byCanonical.getD key []
      let mods := (raws.filterMap (definingModule env)).eraseDups
      if let some mod := definingModule env key.toName then return (key, toJson mod.toString)
      if let [mod] := mods then return (key, toJson mod.toString)
      unless !raws.isEmpty && raws.all isPrivateName do
        throw (IO.userError s!"unresolved environment owner for {key}: {raws}")
      let aliases ← raws.mapM fun raw => do
        let some mod := definingModule env raw | throw (IO.userError s!"missing owner for {raw}")
        return Json.mkObj [("raw", toJson raw.toString), ("module", toJson mod.toString)]
      return (key, toJson aliases)
    IO.FS.writeFile outputPath ((Json.mkObj owners).pretty ++ "\n")
    return 0
  let result ← (snapshot modules namespacePrefix rules proofIrrelevant stableProject).run'.toIO' { fileName := "<decl_snapshot>", fileMap := default } { env := env }
  IO.FS.writeFile outputPath (result.pretty ++ "\n")
  IO.println s!"snapshot saved: {outputPath}"
  return 0
