import SerrePositivity.KST.Fibration
import Lean.Util.CollectAxioms

/-! K-F の私有宣言を含む全宣言と推移的公理依存を検査する。 -/

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.KST.Fibration.WeakEquivalences,
    `SerrePositivity.KST.Fibration.Extension,
    `SerrePositivity.KST.Fibration.RelativeDiagram,
    `SerrePositivity.KST.Fibration.RelativeDiagramMap,
    `SerrePositivity.KST.Fibration.RelativeDiagramCore,
    `SerrePositivity.KST.Fibration.RelativeSimplicialDiagram,
    `SerrePositivity.KST.Fibration.RelativeDiagramKernel,
    `SerrePositivity.KST.Fibration.FunctorCoreCriterion,
    `SerrePositivity.KST.Fibration.FullFunctorCore,
    `SerrePositivity.KST.Fibration.KernelWeakContractibility,
    `SerrePositivity.KST.Fibration.ConnectiveFiberObstruction,
    `SerrePositivity.KST.Fibration.RelativeSConstruction,
    `SerrePositivity.KST.Fibration.RelativeSQuotient,
    `SerrePositivity.KST.Fibration.RelativeSKernel,
    `SerrePositivity.KST.Fibration.RelativeSFunctor,
    `SerrePositivity.KST.Fibration.RelativeSKernelSquare,
    `SerrePositivity.KST.Fibration.KernelCofiberModel,
    `SerrePositivity.KST.Fibration.WeakCofiberVertices,
    `SerrePositivity.KST.Fibration.FullPredicateRestriction,
    `SerrePositivity.KST.Fibration.WeakArrowCategory,
    `SerrePositivity.KST.Fibration.WeakArrowEquivalence,
    `SerrePositivity.KST.Fibration.WeakArrowAdditivity,
    `SerrePositivity.KST.Fibration.WeakStrings,
    `SerrePositivity.KST.Fibration.WeakStringsSimplicial,
    `SerrePositivity.KST.Fibration.WeakArrowClosedPredicate,
    `SerrePositivity.KST.Fibration.WeakStringsStability,
    `SerrePositivity.KST.Fibration.WeakStringsExact]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Fibration).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-F: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-F: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-F: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-F: required module missing: {mod}"
  logInfo m!"K-F: {count} declarations in {modules.size} modules audited; standard axioms only."
