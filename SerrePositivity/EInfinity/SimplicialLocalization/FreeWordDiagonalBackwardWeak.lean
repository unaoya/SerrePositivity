module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeWordDiagonalForwardWeak
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionCanonicalMarkedHom

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock Hammock.FixedObjectDiagram SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
lemma freeWordDiagonalAugmentation_backward_square :
    (freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) ≫
      BackwardZigzag.graphValue =
    singleBackwardDiagonalEvaluation (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) X Y ≫
        freeResolutionCanonicalMarkedHomAugmentation C Y X := by
  ext n σ
  apply WideSubcategory.hom_ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
      (freeResolutionObject_augmentation C n X)
      (freeResolutionObject_augmentation C n Y)).obj (σ.obj 0))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.value_relative]
  change (eqToHom _ ≫ ((freeResolutionAugmentationNatTrans C).app n).functor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (σ.obj 0)).val ≫ eqToHom _) =
    (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((freeResolutionAugmentationNatTrans C).app n)).map
      (eqToHom _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (σ.obj 0)) ≫
        eqToHom _) ≫ eqToHom _).hom
  simp only [Functor.map_comp, WideSubcategory.comp_def, marked_eqToHom_hom,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rfl
lemma freeWordDiagonalAugmentation_backward_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) := by
  apply BackwardZigzag.graphValue_weak.cancel_right
  rw [freeWordDiagonalAugmentation_backward_square]
  exact (singleBackwardDiagonalEvaluation_weak (freeResolution C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) X Y).comp
      (freeResolutionCanonicalMarkedHomAugmentation_weak C Y X)
end SerrePositivity.EInfinity.SimplicialLocalization
