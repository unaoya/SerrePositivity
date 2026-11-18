module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProductRelative
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumnBackwardForwardCatIso
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardData
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardData

/-!
# 元の混合二方向の底と両係数の相対比較

概要：元の係数積と全相対作用素を保持する。
方針：両係数の元の写像と切断の全成分を組にする。
規約：同じ元の graph と augmentation を使う。
使われ方：DK10.3の混合二方向の自然な分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.Opposite
def backwardForwardData (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} where
  base := Cat.of (WideSubcategory C.weakEquivalences)
  left := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardLeftCoefficient C.weakEquivalences w X Y
  right := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.point
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def backwardForwardDataMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForwardData C w X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForwardData D w X' Y' where
  base := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F
  left := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).op
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardLeftMap (Y := Y) (Y' := Y') w F hX)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardLeftMap (X := X) (X' := X') w F hY)
  right := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
