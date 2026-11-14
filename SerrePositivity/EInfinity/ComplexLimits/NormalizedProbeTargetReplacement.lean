module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeHomKan
public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionValue
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories


variable (A : Type u) [CommRing A]

def normalizedProbeTargetReplacementMap (X Y : Complex A) :
    ((normalizedProbeTensorHom A).obj (Opposite.op X)).obj
      (complexSemifreeResolutionValue A Y).val ⟶
    ((normalizedProbeTensorHom A).obj (Opposite.op X)).obj Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((normalizedProbeTensorFrame A).obj X)).map
    (complexSemifreeResolutionValueAugmentation A Y)

lemma normalizedProbeTargetReplacementMap_homotopyEquivalence (X Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (normalizedProbeTargetReplacementMap A X Y) := by
  let := projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A
    (complexSemifreeResolutionValue A Y).val
  have : WeakEquivalence (complexSemifreeResolutionValueAugmentation A Y) :=
    ⟨complexSemifreeResolutionValueAugmentation_quasiIso A Y⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameHom_target_homotopyEquivalence _ (normalizedProbeTensorFrame_cofibrant A X)
    (normalizedSimplexTensor_homotopicallyConstant A ((framedLimitProbeFunctor A).obj X))
    (complexSemifreeResolutionValueAugmentation A Y)

end SerrePositivity.EInfinity.ComplexLimits
