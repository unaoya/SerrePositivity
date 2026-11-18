module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardData
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendParts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagNativeRelative
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramTotal

/-!
# 元の後向き二列の切断対象の相対自然性

概要：元の底と両係数を送る相対関手と切断関手を厳密に照合する。
方針：指定 Hom の反変作用と残りの語の共変作用の全成分を回収する。
規約：元の両端の等式移送と全縦射を保持する。
使われ方：DK10.3の後向き二列の単体図式への分解。
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
def backwardBackwardRelativeFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget C.weakEquivalences w X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget D.weakEquivalences w X' Y' :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.totalFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardDataMap w F hX hY)).toFunctor
lemma backwardBackward_relative_head (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardSource C.weakEquivalences w X Y) :
    Discrete.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S)))) =
    Discrete.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S))) ≫
        eqToHom (congrArg (fun T => (⟨T⟩ : WideSubcategory D.weakEquivalences)) hX)) := by
  apply Discrete.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.left_relative_obj F hX hY S]
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nativeValue_relative F hX rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)
  simp only [eqToHom_refl, Category.id_comp] at he
  convert he using 1
lemma backwardBackward_relative_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardSource C.weakEquivalences w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardObject D.weakEquivalences w X' Y'
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S) =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackwardRelativeFunctor w F hX hY).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardObject C.weakEquivalences w X Y S) := by
  apply congrArg₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardLeftCoefficient D.weakEquivalences X')
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardRightCoefficient D.weakEquivalences w Y')
    (⟨F.functor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.obj S)⟩ : WideSubcategory D.weakEquivalences))
  · exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackward_relative_head w F hX hY S
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY S

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
