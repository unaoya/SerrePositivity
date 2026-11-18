module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardData
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendParts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SingleZigzagRelativeValue
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramTotal

/-!
# 元の前向き二列の切断対象の相対自然性

概要：元の切断対象を相対関手で送る二通りの像が厳密に一致する。
方針：元の底と両係数の比較関手で接合点・残り・先頭 Hom を照合する。
規約：元の固定端点の表示等式を含める。全射の自然性は後続。
使われ方：DK9.4・10.3の全相対作用素の正方形。
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
def forwardForwardRelativeFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget C.weakEquivalences w X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget D.weakEquivalences w X' Y' :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.totalFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardDataMap w F hX hY)).toFunctor

lemma forwardForward_relative_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource C.weakEquivalences w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject D.weakEquivalences w X' Y'
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S) =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardForwardRelativeFunctor w F hX hY).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject C.weakEquivalences w X Y S) := by
  apply congrArg₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardLeftCoefficient D.weakEquivalences w Y')
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardRightCoefficient D.weakEquivalences X')
    (⟨F.functor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.obj S)⟩ :
      WideSubcategory D.weakEquivalences))
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY S
  · apply Discrete.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S)) =
        eqToHom hX.symm ≫ F.functor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.left_relative_obj F hX hY S]
    simpa only [eqToHom_refl, Category.comp_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.value_relative F hX rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
