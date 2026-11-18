module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalForwardWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionCanonicalMarkedHom

/-!
# 元の自由解像の backward 一列の左比較の弱同値性

概要：元の backward 一列の augmentation 自身が弱同値である。
方針：実際の指定部分圏の Hom augmentation と端点表示の同型を使う。
規約：元の全列・全縦射と元の比較射を保持する。
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
lemma freeWordDiagonalAugmentation_backward_square :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BackwardZigzag.graphValue =
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleBackwardDiagonalEvaluation (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
      (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) X Y ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionCanonicalMarkedHomAugmentation C Y X := by
  ext n σ
  apply WideSubcategory.hom_ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n X)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y)).obj (σ.obj 0))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.value_relative]
  change (eqToHom _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n).functor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (σ.obj 0)).val ≫ eqToHom _) =
    (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)).map
      (eqToHom _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (σ.obj 0)) ≫
        eqToHom _) ≫ eqToHom _).hom
  simp only [Functor.map_comp, WideSubcategory.comp_def, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.marked_eqToHom_hom,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rfl
lemma freeWordDiagonalAugmentation_backward_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BackwardZigzag.graphValue_weak.cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation_backward_square]
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleBackwardDiagonalEvaluation_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) X Y).comp
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionCanonicalMarkedHomAugmentation_weak C Y X)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
