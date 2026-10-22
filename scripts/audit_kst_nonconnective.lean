import SerrePositivity.KST.NonConnective
import Lean.Util.CollectAxioms

/-! K-7 所有モジュールの全宣言（私有・自動生成を含む）と推移的公理依存を監査する。 -/

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.KST.NonConnective.SequentialSpectrum,
    `SerrePositivity.KST.NonConnective.SequentialPi,
    `SerrePositivity.KST.NonConnective.SequentialComparison,
    `SerrePositivity.KST.NonConnective.SequentialRawHomDiagram,
    `SerrePositivity.KST.NonConnective.SequentialCoherentLift,
    `SerrePositivity.KST.NonConnective.SequentialCoherentCocone,
    `SerrePositivity.KST.NonConnective.SequentialLevelColimit,
    `SerrePositivity.KST.NonConnective.SequentialLevelColimitUniversal,
    `SerrePositivity.KST.NonConnective.SequentialLevelHomLimit]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.NonConnective).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-7: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-7: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-7: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-7: required module missing: {mod}"
  logInfo m!"K-7: {count} declarations in {modules.size} modules audited; standard axioms only."

#check SerrePositivity.KST.NonConnective.sequentialPiCoconeIsColimit
#check SerrePositivity.KST.NonConnective.sequentialPiUnderlyingIsColimit
#check SerrePositivity.KST.NonConnective.sequentialPi_exists_late
#check SerrePositivity.KST.NonConnective.sequentialPi_eq_iff
#check SerrePositivity.KST.NonConnective.sequentialInjection_bijective_of_stable
#check SerrePositivity.KST.NonConnective.sequentialPi_subsingleton_iff
#check SerrePositivity.KST.NonConnective.sequentialPi_subsingleton_of_eventually
#check SerrePositivity.KST.NonConnective.sequentialInjection_bijective_on
#check SerrePositivity.KST.NonConnective.sequentialInjection_isInvertible_of_stable

#check SerrePositivity.KST.NonConnective.sequentialRawInjectionCone
#check SerrePositivity.KST.NonConnective.sequentialReflectedEndProjection_trivial
#check SerrePositivity.KST.NonConnective.sequentialReflectedBFInjectionPoint_projection
#check SerrePositivity.KST.NonConnective.sequentialCoherentCocone
#check SerrePositivity.KST.NonConnective.sequentialCoherentCocone_vertex

#check SerrePositivity.KST.NonConnective.sequentialKanSequence_sigma_mono
#check SerrePositivity.KST.NonConnective.sequentialLevelColimitIsColimit
#check SerrePositivity.KST.NonConnective.sequentialReplacementProjection_piIsomorphism

#check SerrePositivity.KST.NonConnective.sequentialLevelHomIsLimit
#check SerrePositivity.KST.NonConnective.sequentialHomLimitFamily_fac
