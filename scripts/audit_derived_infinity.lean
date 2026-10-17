import SerrePositivity.InfinityCategories.Derived
import Lean.Util.CollectAxioms

/-!
概要：D2 の公開宣言と実装モジュール内の全宣言の公理を監査する。
方針：公開名を表示し、生成補題も含め依存公理を機械的に検査する。
規約：許されるのは propext・Classical.choice・Quot.sound のみ。
使われ方：対象ビルド後に `lake env lean scripts/audit_derived_infinity.lean`。
-/

#print axioms SerrePositivity.InfinityCategories.complexSemifree
#print axioms SerrePositivity.InfinityCategories.complexSemifree_iff
#print axioms SerrePositivity.InfinityCategories.complexSemifree_evaluation
#print axioms SerrePositivity.InfinityCategories.complexSemifreeStage
#print axioms SerrePositivity.InfinityCategories.complexSemifreeQuotient
#print axioms SerrePositivity.InfinityCategories.freeSphereEvaluationIso
#print axioms SerrePositivity.InfinityCategories.spherePresentationEvaluationIso
#print axioms SerrePositivity.InfinityCategories.complexSemifreeStageZeroIso
#print axioms SerrePositivity.InfinityCategories.complexSemifreeQuotientIso

#print axioms SerrePositivity.InfinityCategories.complexSemifree_isKProjective

#print axioms SerrePositivity.InfinityCategories.exists_complexSemifree_resolution

#print axioms SerrePositivity.InfinityCategories.Semifree

#print axioms SerrePositivity.InfinityCategories.semifreeHomotopyComparison

#print axioms SerrePositivity.InfinityCategories.semifreeHomotopyComparisonFull

#print axioms SerrePositivity.InfinityCategories.semifreeHomotopyComparisonFaithful

#print axioms SerrePositivity.InfinityCategories.semifreeDerivedComparison

#print axioms SerrePositivity.InfinityCategories.semifreeDerivedComparison_map_bijective

#print axioms SerrePositivity.InfinityCategories.semifreeDerivedComparisonFull

#print axioms SerrePositivity.InfinityCategories.semifreeDerivedComparisonFaithful

#print axioms SerrePositivity.InfinityCategories.semifreeDerivedComparisonEssSurj

#print axioms SerrePositivity.InfinityCategories.semifreeDerivedComparisonIsEquivalence

#print axioms SerrePositivity.InfinityCategories.semifreeDerivedEquivalence

#print axioms SerrePositivity.InfinityCategories.derivedInfinityCategory
#print axioms SerrePositivity.InfinityCategories.derivedInfinityCategory_obj
#print axioms SerrePositivity.InfinityCategories.derivedInfinityCategoryVertexEquiv
#print axioms SerrePositivity.InfinityCategories.derivedInfinityCategoryEdgeEquiv
#print axioms SerrePositivity.InfinityCategories.derivedInfinityCategoryTriangleEquiv

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.InfinityCategories.Derived.Semifree,
    `SerrePositivity.InfinityCategories.Derived.SemifreeKProjective,
    `SerrePositivity.InfinityCategories.Derived.SemifreeResolution,
    `SerrePositivity.InfinityCategories.Derived.SemifreeSubcategory,
    `SerrePositivity.InfinityCategories.Derived.DerivedComparison,
    `SerrePositivity.InfinityCategories.Derived.InfinityCategory]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"D2 axiom audit passed: {count} declarations in {seen.size} modules."
