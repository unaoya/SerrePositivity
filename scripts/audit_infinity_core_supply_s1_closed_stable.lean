import SerrePositivity.KST.Fibration.Relative.ClosedStableAll
import Lean.Util.CollectAxioms

/-!
概要：S-1 の無条件化を含む供給閉包の所有宣言を私有名も含めて公理監査する。
方針：環境の宣言を定義元モジュールで選び、推移的公理を列挙する。
規約：標準三公理のみ許可し、宣言型の ModelCategory 仮定を拒否する。
使われ方：Relative.ClosedStableAll の対象ビルド後の専用監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.KST.Fibration.Relative.ClosedStableFlags,
    `SerrePositivity.KST.Fibration.Relative.ClosedFlagFunctor,
    `SerrePositivity.KST.Fibration.Relative.ClosedCofiberProjection,
    `SerrePositivity.KST.Fibration.Relative.ClosedFlagConstants,
    `SerrePositivity.KST.Fibration.Relative.ClosedFlagFactor,
    `SerrePositivity.KST.Fibration.Relative.ClosedTailFlags,
    `SerrePositivity.KST.Fibration.Relative.ClosedTailPullback,
    `SerrePositivity.KST.Fibration.Relative.StableTrivialPullback,
    `SerrePositivity.KST.Fibration.Relative.ClosedTailAdditivity,
    `SerrePositivity.KST.Fibration.Relative.ClosedKernelFlags,
    `SerrePositivity.KST.Fibration.Relative.ClosedKernelContraction,
    `SerrePositivity.KST.Fibration.Relative.ClosedRealizationPullback,
    `SerrePositivity.KST.Fibration.Relative.ClosedZeroFlag,
    `SerrePositivity.KST.Fibration.Relative.ClosedStableFiber,
    `SerrePositivity.KST.Fibration.Relative.ClosedStableFiberUnconditional]
  for mod in env.header.modules do
    let parts := mod.module.components
    if (`SerrePositivity.KST).isPrefixOf mod.module &&
        (parts.contains `Cofinality || parts.contains `NonConnective) then
      throwError "S-1: forbidden transitive import: {mod.module}"
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Fibration.Relative).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "S-1 closed stable: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "S-1 closed stable: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "S-1 closed stable: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "S-1 closed stable: required module missing: {mod}"
  logInfo m!"S-1 closed stable: {count} declarations in {modules.size} modules audited; standard axioms only."
