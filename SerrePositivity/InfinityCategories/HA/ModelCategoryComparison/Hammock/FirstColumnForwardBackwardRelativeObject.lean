module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumnForwardBackwardData
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendParts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SingleZigzagRelativeValue
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramTotal

/-!
# 元の混合二方向の全対象の相対自然性

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
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def forwardBackwardRelativeFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardTarget C.weakEquivalences w X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardTarget D.weakEquivalences w X' Y' :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.totalFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardDataMap w F hX hY)).toFunctor
lemma forwardBackward_relative_head (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource C.weakEquivalences w X Y) :
    Discrete.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S))) =
    Discrete.mk (eqToHom hX.symm ≫ F.functor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S))) := by
  apply Discrete.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.left_relative_obj F hX hY S]
  simpa only [eqToHom_refl, Category.comp_id] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.value_relative F hX rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)
lemma forwardBackward_relative_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource C.weakEquivalences w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardObject D.weakEquivalences w X' Y'
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S) =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardRelativeFunctor w F hX hY).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardObject C.weakEquivalences w X Y S) := by
  apply congrArg₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.point
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRightCoefficient D.weakEquivalences w X' Y')
    (⟨F.functor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.obj S)⟩ :
      WideSubcategory D.weakEquivalences))
  · rfl
  · exact Prod.ext (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackward_relative_head w F hX hY S)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY S)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
