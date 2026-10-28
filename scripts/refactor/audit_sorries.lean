import SerrePositivity
open Lean Elab Command

/-!
## 概要
根の定数閉包にある直接の sorry を、文献入力の集合と厳密に照合する。
## 方針
定理・opaque の本体も読み、補助宣言は親の宣言へまとめる。
## 規約
既定の許可集合は引用 3 件。kanQuillen_model_exists は閉包にあってはならない。
## 使われ方
verify.sh が実行する。SORRY_AUDIT_ROOT / SORRY_AUDIT_ALLOWED は試験専用。
-/

private def sorryAuditParent : Name → Name
  | .str p s =>
    if s.startsWith "_proof_" || s.startsWith "match_" || s.startsWith "_match_" ||
        s.startsWith "proof_" || s.startsWith "_aux_" then sorryAuditParent p
    else .str p s
  | .num p _ => sorryAuditParent p
  | .anonymous => .anonymous

#eval show CommandElabM Unit from do
  let root := ((← IO.getEnv "SORRY_AUDIT_ROOT").getD "SerrePositivity.main_statement").toName
  let defaults := "SerrePositivity.theorem_3_1_K0 SerrePositivity.Section4.supportedRankK0_descent " ++
    "SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3"
  let allowedText := (← IO.getEnv "SORRY_AUDIT_ALLOWED").getD defaults
  let allowed := (allowedText.splitOn " ").filterMap fun s =>
    if s.isEmpty then none else some s.toName
  let mut env ← getEnv
  -- A test theorem may live in a separately built module outside the root import.
  if (env.find? root).isNone then
    let mut candidate := root.getPrefix
    let mut found := false
    while candidate != .anonymous && !found do
      let path := candidate.toString.replace "." "/" ++ ".lean"
      if ← System.FilePath.pathExists path then
        env ← importModules #[{ module := `SerrePositivity }, { module := candidate }] {}
        found := true
      else
        candidate := candidate.getPrefix
  unless (env.find? root).isSome do
    throwError "sorry audit root not found: {root}"
  let forbidden := `SerrePositivity.Inputs.Homotopy.kanQuillen_model_exists
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut sorried : NameSet := {}
  let mut direct : Array Name := #[]
  let mut count : Nat := 0
  while h : stack ≠ [] do
    let n := stack.head h
    stack := stack.tail
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      count := count + 1
      let used := ci.getUsedConstantsAsSet
      -- value? defaults to allowOpaque=false: that used to discard theorem proofs.
      if used.contains ``sorryAx then
        direct := direct.push n
        sorried := sorried.insert (sorryAuditParent (privateToUserName n))
      for c in used.toList do
        if !visited.contains c then stack := c :: stack
  let actual := sorried.toList.mergeSort (fun a b => a.toString ≤ b.toString)
  let missing := allowed.filter (fun n => !sorried.contains n)
  let unexpected := actual.filter (fun n => !allowed.contains n)
  logInfo m!"visited {count} constants; root: {root}"
  logInfo m!"direct sorry declarations: {direct}"
  logInfo m!"sorry declarations grouped by parent: {actual}"
  logInfo m!"{forbidden} in closure: {visited.contains forbidden}"
  unless missing.isEmpty && unexpected.isEmpty do
    throwError "sorry closure mismatch; missing: {missing}; unexpected: {unexpected}"
  if visited.contains forbidden then
    throwError "forbidden declaration in closure: {forbidden}"
  logInfo "sorry closure PASS"
