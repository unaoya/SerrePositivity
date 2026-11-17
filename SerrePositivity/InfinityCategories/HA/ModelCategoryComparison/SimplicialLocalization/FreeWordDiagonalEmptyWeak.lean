module

public import SerrePositivity.EInfinity.Hammock.EmptyWordDiagonalWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjects
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalForwardWeak

/-!
# 元の自由解像の空語の左比較射の弱同値性

概要：元の固定端点と全単体作用素を保持する。
方針：一頂点の一意性と実際の相対関手・対角比較を使う。
規約：通常の hammock augmentation の弱同値性を仮定しない。
使われ方：DK5.7の全語の帰納基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.EInfinity.Hammock _root_.SerrePositivity.InfinityCategories
lemma freeWordDiagonalAugmentation_empty_weak (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty) :=
  FixedObjectDiagram.wordDiagonalAugmentation_empty_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) C
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C) (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C)
    (fun n => (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentation_obj_bijective C n).injective) X Y
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
