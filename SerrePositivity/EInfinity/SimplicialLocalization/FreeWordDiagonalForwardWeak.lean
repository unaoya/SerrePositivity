module

public import SerrePositivity.EInfinity.Hammock.SingleZigzagDiagonalEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordDiagonalAugmentation
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionHomRepresentation

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock Hammock.FixedObjectDiagram SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
def freeWordDiagonalAugmentation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalDiagram (freeResolution C) C (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalAugmentation (freeResolution C) C (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) (freeResolutionAugmentationNatTrans C)
    (freeResolutionObject_augmentation C) X Y

lemma freeWordDiagonalAugmentation_forward_square :
    (freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) ≫
      ForwardZigzag.graphValue =
    singleForwardDiagonalEvaluation (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) X Y ≫
        freeResolutionHomAugmentation C X Y := by
  ext n σ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.value_relative ((freeResolutionAugmentationNatTrans C).app n)
    (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y) (σ.obj 0)

lemma freeWordDiagonalAugmentation_forward_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) := by
  apply ForwardZigzag.graphValue_weak.cancel_right
  rw [freeWordDiagonalAugmentation_forward_square]
  exact (singleForwardDiagonalEvaluation_weak (freeResolution C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) X Y).comp
      (freeResolutionHomAugmentation_isWeakHomotopyEquivalence C X Y)
end SerrePositivity.EInfinity.SimplicialLocalization
