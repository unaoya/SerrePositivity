module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementRoofMaps
public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementPinchedFamily

/-!
# 元の全複体の相対屋根と native な pinched 族の弱同値性

DAG XIII §2.2 の native な降下への前段。同じ正規化屋根の弱同値性を、
全要素圏の実同型と AsSmall の実同型を通して運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory _root_.HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma complexRelativeElementRoofMap_weak :
    IsWeakHomotopyEquivalence
      (complexRelativeElementRoofMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have hi := (isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso (weakEquivalences (Complex A))
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) Y).symm).isWeakHomotopyEquivalence
  apply hi.cancel_right
  have h := (isPrecompositionEquivalence_of_iso
    (complexRelativeElementIndexIso A X Y)).isWeakHomotopyEquivalence.comp
      (complexNormalizedTensorRoof_weak A X Y)
  exact (complexRelativeElementRoofMap_image A X Y).symm ▸ h

lemma complexRelativeElementHammockPinchedMap_weak :
    IsWeakHomotopyEquivalence
      (complexRelativeElementHammockPinchedMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) Y) := by
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
    (exInfinityUnit.app
      (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (complexRelativeCategory A).weakEquivalences
        ((complexRelativeUp A).obj ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))
        ((complexRelativeUp A).obj Y)))
    (SSet.anodyneExtensions.Q_inverts _ (exInfinityUnit_anodyne _))
  change IsWeakHomotopyEquivalence
    ((complexRelativeElementRoofMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) Y ≫
      exInfinityUnit.app _) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (complexRelativeCategory A)
        ((complexRelativeUp A).obj ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))
        ((complexRelativeUp A).obj Y))
  exact ((complexRelativeElementRoofMap_weak A X Y).comp hu).comp
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap_weak _ _ _)

end SerrePositivity.EInfinity.PowerOperation
