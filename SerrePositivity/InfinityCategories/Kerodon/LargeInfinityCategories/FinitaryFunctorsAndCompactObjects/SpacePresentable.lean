module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteSpaceGenerators
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：元の空間 ∞ 圏の小さい compact 全部分生成圏を構成し、presentable 性を証明する。
方針：共通の有限コード族の全部分模型へ、元の各空間の filtered 全表示を同型飽和の全同値で移す。
規約：生成圏・添字は u、元の標的は u+1。各指定頂点を厳密に保持し、生成性を instance 仮定にしない。
使われ方：HTT 5.5.1 の空間・前層の presentable 性。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects


/-- 元の空間内の共通の小さい compact 族の、宇宙 u の全部分模型。 -/
def spaceCompactGeneratorCategory : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.space_hasSmallFixedVertexMaps _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceGeneratorVertex

instance spaceCompactGeneratorCategory_quasicategory :
    Quasicategory spaceCompactGeneratorCategory.{u} :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.space_hasSmallFixedVertexMaps _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceGeneratorVertex))

/-- 元の空間 ∞ 圏への、同じ小さい compact 全部分模型の包含。 -/
def spaceCompactGeneratorInclusion :
    (SSet.uliftFunctor.{u + 1, u}).obj spaceCompactGeneratorCategory ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.space_hasSmallFixedVertexMaps _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceGeneratorVertex

/-- 同じ小さい全部分模型は、全 compact 性と元の各指定頂点の filtered 全表示を持つ。 -/
lemma spaceCompactGeneratorInclusion_isCompactGenerating :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating Cardinal.aleph0 spaceCompactGeneratorInclusion.{u} := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion_isKappaCompactGenerating
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.space_hasSmallFixedVertexMaps _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceGeneratorVertex
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceGeneratorVertex_isCompact
  intro x
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject x
  obtain ⟨d, hd, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSpacePresentation.exists_finiteSpacePresentation K
  refine ⟨nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSpacePresentation.FiniteSpacePieces K.obj), inferInstance,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSpacePresentation.finiteSpacePieces_nerve_isKappaFiltered K.obj,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSpacePresentation.finiteSpaceReplacementDiagram K.obj), ?_, d, hd, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finiteSpaceReplacementDiagram_in_family K.obj
  · exact hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x)

/-- 元の空間 ∞ 圏は、構成した小さい compact 全部分生成圏により ℵ₀-accessible。 -/
lemma space_isKappaAccessible_aleph0 : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible Cardinal.aleph0 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  ⟨Cardinal.isRegular_aleph0, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.space_hasSmallColimits.hasSmallKappaFilteredColimits _,
    spaceCompactGeneratorCategory, inferInstance, spaceCompactGeneratorInclusion,
    spaceCompactGeneratorInclusion_isCompactGenerating⟩

/-- 元の小さい空間の ∞ 圏は、同じ宇宙に関して presentable。 -/
lemma space_isPresentable : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  ⟨space_isKappaAccessible_aleph0.isAccessible, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.space_hasSmallColimits⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
