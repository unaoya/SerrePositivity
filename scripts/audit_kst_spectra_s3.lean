import SerrePositivity.KST.Spectra.S3All
import Lean.Util.CollectAxioms

/-!
概要：Sp-3 所有葉の私有宣言・推移的依存・宣言型の仮定を独立監査する。
方針：所有モジュールを漏れなく列挙し、標準三公理以外と ModelCategory を拒否する。
規約：三認証の存在は監査しない。条件付き API を無条件供給と数えない。
使われ方：専用集約の保存単位の s5 検証。共有集約を import しない。
-/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.KST.Spectra.S3ActualFaces,
    `SerrePositivity.KST.Spectra.S3MilnorConnection,
    `SerrePositivity.KST.Spectra.S3KappaConnection]
  for mod in #[
      `SerrePositivity.KST.Spectra.D3All,
      `SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.KanQuillen] do
    if env.header.modules.any (·.module == mod) then
      throwError "Sp-3 s3: forbidden import: {mod}"
  let mut roots : List Name := []
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "Sp-3 s3: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Sp-3 s3: unexpected axioms in {name}: {axioms}"
    roots := name :: roots
    unless modules.contains mod do modules := modules.push mod
  unless !roots.isEmpty do throwError "Sp-3 s3: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "Sp-3 s3: required module missing: {mod}"
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if name == `HomotopicalAlgebra.ModelCategory then
      throwError "Sp-3 s3: ModelCategory in proof/type closure"
    if let some info := env.find? name then
      pending := info.type.getUsedConstants.toList ++ pending
      if let .inductInfo value := info then
        pending := value.ctors ++ pending
      if let some value := info.value? (allowOpaque := true) then
        pending := value.getUsedConstants.toList ++ pending
  logInfo m!"Sp-3 s3: {roots.length} owned declarations in {modules.size} modules; standard three axioms only; {seen.size} transitive constants checked."

#check @SerrePositivity.KST.Spectra.S3.actualFaces_isPullback
#check @SerrePositivity.KST.Spectra.S3.actualSourceValueIso_triangle
#check @SerrePositivity.KST.Spectra.S3.rectangleOfSquare
#check @SerrePositivity.KST.Spectra.S3.rectangleOfStableSquare
#check @SerrePositivity.KST.Spectra.S3.milnorActualInput
#check @SerrePositivity.KST.Spectra.S3.milnorActual_isPullback
#check @SerrePositivity.KST.Spectra.S3.milnorSourceRoof
#check @SerrePositivity.KST.Spectra.S3.milnorSourceValueIso
#check @SerrePositivity.KST.Spectra.S3.kappaToStrict
#check @SerrePositivity.KST.Spectra.S3.kappaPerfect_isPullback
#check @SerrePositivity.KST.Spectra.S3.exists_kappaRelativeRoof
