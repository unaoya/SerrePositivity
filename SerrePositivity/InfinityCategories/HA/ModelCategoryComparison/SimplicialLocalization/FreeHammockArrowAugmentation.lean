module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockArrowZero
public import SerrePositivity.EInfinity.Hammock.RelativeFixedArrow

/-!
# 共通始域の元の射の左比較による回収

概要：元の一文字の自由射は左比較で同じ hammock の一列へ戻る。
方針：元の余単位と固定端点の相対写像の一列への作用を使う。
規約：元の射と元の両端点を保持する。
使われ方：DK と hammock の比較の元の射への整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.Opposite _root_.SerrePositivity.EInfinity.Hammock
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

lemma freeResolutionArrowZero_augmentation (f : X ⟶ Y) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C (op ⦋0⦌) X).symm ≫
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app (op ⦋0⦌)).functor.map
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero C f) ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C (op ⦋0⦌) Y) = f := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  change eqToHom _ ≫ (pathComposition C.category).map ((Paths.of C.category).map f) ≫
    eqToHom _ = f
  simp only [pathComposition_map, Paths.of_map, composePath_toPath,
    eqToHom_refl, Category.id_comp, Category.comp_id]

lemma freeHammockArrowZero_augmentation (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowZero C f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint C.weakEquivalences f (op ⦋0⦌) := by
  change ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation C X Y).app (op ⦋0⦌)).app (op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero C f) (op ⦋0⦌)) = _
  have h := Relative.fixedColimitMap_arrowPoint
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app (op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C (op ⦋0⦌) X)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C (op ⦋0⦌) Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero C f) (op ⦋0⦌)
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero_augmentation] at h
  exact (congrArg (fun k => k.app (op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj (op ⦋0⦌)).weakEquivalences
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero C f) (op ⦋0⦌)))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation_fixedColimitMap C X Y (op ⦋0⦌))).trans h

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
