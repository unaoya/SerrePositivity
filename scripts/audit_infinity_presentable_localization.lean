import SerrePositivity.InfinityCategories.F2.Presentable.Localization.All
import Lean.Util.CollectAxioms

/-!
P-f の独立監査。新規所有モジュールの全宣言について標準三公理のみを許す。
局所化の存在の完成監査ではなく、現在検証済みの生成族・飽和射圏・小さい compact 候補の監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F2.Presentable.Localization |>.isPrefixOf mod do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Presentable localization: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count < 8 then throwError "Presentable localization: expected at least eight declarations"
  logInfo m!"Presentable localization audit passed: {count} declarations, standard axioms only."

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open F2.Presentable F2.Presentable.Localization HomotopyLimits

universe u v

-- 任意の生成添字・任意の元の対象・任意の単体集合パラメータを保持する独立例。
example {X : SSet.{v}} [Quasicategory X] {I : Type u}
    (edges : I → X _⦋1⦌) (z : X _⦋0⦌) (hz : IsLocalObject (Set.range edges) z)
    (i : I) (A : SSet.{v}) :
    Function.Bijective (fun α : ConstantFunctorHom A X (X.δ 0 (edges i)) z ↦
      constantFunctorHomMap A
        (Truncated.HomotopyCategory.homMk (edgeOfSimplex (edges i))) ≫ α) :=
  (isLocalObject_range_iff_constantHom_bijective edges z).mp hz i A

example {C : SSet.{u + 1}} [Quasicategory C] (hC : F2.Presentable.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∀ i, F2.Compact.IsKappaCompact.{u, u + 1} μ (C.δ 1 (edges i)) ∧
        F2.Compact.IsKappaCompact.{u, u + 1} μ (C.δ 0 (edges i)) :=
  exists_regular_compactEndpoints hC edges σ

#check @isLocalObject_range_iff
#check @isLocalObject_range_iff_constantHom_bijective
#check @localEquivalenceHom_range_iff_constantHom_bijective
#check @localObjects_antitone_of_generators_localEquivalences
#check @localEquivalences_subset_of_generators_localEquivalences
#check @localEquivalences_eq_iff_generators
#check @localEquivalences_eq_iff_localObjects
#check @exists_regular_compactEndpoints
#check @generatedEdges
#check @generatedArrowCategory
#check @generatedArrowInclusion_isFullyFaithful
#check @generatedEdges_smallGeneration
#check @generatedArrow_mem_iff_vertexIso
#check @generatedArrow_colimit_mem
#check @generatedArrow_hasSmallColimits
#check @generatedArrowInclusion_preservesSmallColimits
#check @generatedArrow_isKappaCompact_of_image
#check @compactGeneratedArrows
#check @compactGeneratedArrowVertex
#check @compactGeneratedArrowInclusion_isFullyFaithful
#check @exists_smallCompactGeneratedArrowModel
#check @compactGeneratedArrowInclusion_compact
#check @exists_smallCompactArrowCandidates
#check @generatorArrowVertex_edge
#check @arrow_isPresentable
#check @exists_regular_generatorArrowCardinal
#check @exists_generatorContainingCompactArrowCandidates
#check @exists_generatorContainingIndComparison
#check @generatedSourceCategory
#check @generatedSourceTarget
#check @generatedSourceInclusion_isFullyFaithful
#check @generatedSourceLeg
#check @generatedSourceLeg_mem
#check @sequentialPiece_exists_le
#check @sequentialPiece_isFiltered
#check @sequentialPieceSequence_final
#check @sequentialPiece_hasCardinalLT
#check @compactSource_coslice_factorization

#check @indArrowImageFactor_isQCatEquivalence
#check @indArrowImageVertex_mem
#check @indArrowImage_isKappaAccessible
#check @indArrowImage_colimit_mem
#check @indArrowImageInclusion_isFullyFaithful
#check @indArrowImageInclusion_isKappaAccessible
#check @exists_generatorContainingAccessibleIndImage
#check @exists_compactCoveringAccessibleIndImage
#check @sourceCoslice_hasColimit_iff
#check @sourceCoslice_hasSmallColimits

#check @smallDiagramCoslice_hasSmallColimits
