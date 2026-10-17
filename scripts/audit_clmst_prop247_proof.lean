import SerrePositivity.CLMST.Prop247Proof
import SerrePositivity.CLMST.Inputs.PerfectoidIsogeny

-- 文献入力と公開証明の署名が定義上同じであることを検査する。
example : @SerrePositivity.CLMST.Inputs.proposition_2_4_7 =
    @SerrePositivity.CLMST.proposition_2_4_7_proved := Subsingleton.elim _ _

#print axioms SerrePositivity.CLMST.proposition_2_4_7_proved

meta section
open Lean Elab Command

private def permitted : List Name :=
  [``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral,
   ``SerrePositivity.BhattScholze.Inputs.perfectoidization_excision_isPullback]

private partial def checkDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx && !permitted.contains n then
      throwError "Prop 2.4.7：許可されていない未証明依存 {n}"
    checkDependencies (deps.toList ++ rest) seen

elab "assert_prop247_proof_dependencies" : command => do
  let seen ← liftCoreM <| checkDependencies
    [``SerrePositivity.CLMST.proposition_2_4_7_proved] {}
  unless seen.contains ``sorryAx do
    throwError "Prop 2.4.7：sorryAx への到達を確認できない"
  for n in permitted do
    unless seen.contains n do
      throwError "Prop 2.4.7：指定の外部入力が欠けている {n}"
    logInfo m!"Prop 2.4.7 の未証明入力：{n}"
  logInfo "Prop 2.4.7：型・証明の到達未証明宣言は指定の二件のみ。"
end

assert_prop247_proof_dependencies
