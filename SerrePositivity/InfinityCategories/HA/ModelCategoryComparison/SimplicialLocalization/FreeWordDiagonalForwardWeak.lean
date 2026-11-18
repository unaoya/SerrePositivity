module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.SingleZigzagDiagonalEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordDiagonalAugmentation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionHomRepresentation

/-!
# 元の自由解像の forward 一列の左比較の弱同値性

概要：元の自由解像の固定 Hom augmentation を一列の比較へ接続する。
方針：同じ対象の表示を移す同型と元の augmentation の可換式を使う。
規約：元の比較射自身の弱同値性を証明する。
使われ方：DK5.7の全語の帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram _root_.SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
def freeWordDiagonalAugmentation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalDiagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) C (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
      (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalAugmentation (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) C (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C) X Y

lemma freeWordDiagonalAugmentation_forward_square :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardZigzag.graphValue =
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleForwardDiagonalEvaluation (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
      (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) X Y ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomAugmentation C X Y := by
  ext n σ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.value_relative ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y) (σ.obj 0)

lemma freeWordDiagonalAugmentation_forward_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardZigzag.graphValue_weak.cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation_forward_square]
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleForwardDiagonalEvaluation_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) X Y).comp
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomAugmentation_isWeakHomotopyEquivalence C X Y)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
