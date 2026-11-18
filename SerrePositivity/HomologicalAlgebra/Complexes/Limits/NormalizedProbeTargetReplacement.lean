module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeHomKan
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SemifreeResolutionValue
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.FixedQuillenTargetInvariance

/-!
# 同じ正規化 probe Hom の実半自由標的置換

概要：元の標的の半自由分解からの augmentation を、同じ正規化 Hom で後合成する。
方針：実 Reedy frame と元の擬同型へ固定 Quillen 類の標的比較を適用する。
規約：標的の元の cofibrancy を仮定しない。
使われ方：実正規化 Hom から既存 D(R) の同じ値への比較 span。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories


variable (A : Type u) [CommRing A]

def normalizedProbeTargetReplacementMap (X Y : Complex A) :
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (Opposite.op X)).obj
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y).val ⟶
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (Opposite.op X)).obj Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).obj X)).map
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A Y)

lemma normalizedProbeTargetReplacementMap_homotopyEquivalence (X Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.ComplexLimits.normalizedProbeTargetReplacementMap A X Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y).val
  have : WeakEquivalence (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A Y) :=
    ⟨_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation_quasiIso A Y⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameHom_target_homotopyEquivalence _ (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame_cofibrant A X)
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_homotopicallyConstant A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A Y)

end SerrePositivity.ComplexLimits
