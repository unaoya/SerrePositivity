module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionFunctoriality
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockObjects

/-!
# 元の自由解像の選択対象の係数自然性

概要：元の自由解像の係数写像が同じ固定対象の表示を保つ。
方針：実際の augmentation の対象単射性と係数自然性を使う。
規約：元の対象表示の自然性を仮定せず証明する。
使われ方：自由 hammock の全係数写像と比較射の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory
lemma freeResolutionMap_object {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((freeResolutionMap F).app n).functor.obj (freeResolutionObject C n X) =
      freeResolutionObject D n (F.functor.obj X) := by
  apply (freeResolutionObjectEquiv D n).injective
  have he := NatTrans.congr_app (freeResolutionMap_augmentation F) n
  change (freeResolutionMap F).app n ≫ (freeResolutionAugmentationNatTrans D).app n =
    (freeResolutionAugmentationNatTrans C).app n ≫ F at he
  have hf := congrArg (fun K : (freeResolution C).obj n ⟶ D => K.functor) he
  change ((freeResolutionMap F).app n).functor ⋙
    ((freeResolutionAugmentationNatTrans D).app n).functor =
    ((freeResolutionAugmentationNatTrans C).app n).functor ⋙ F.functor at hf
  change ((freeResolutionAugmentationNatTrans D).app n).functor.obj
      (((freeResolutionMap F).app n).functor.obj (freeResolutionObject C n X)) =
    ((freeResolutionAugmentationNatTrans D).app n).functor.obj
      (freeResolutionObject D n (F.functor.obj X))
  rw [← Functor.comp_obj, hf, Functor.comp_obj,
    freeResolutionObject_augmentation, freeResolutionObject_augmentation]
end SerrePositivity.EInfinity.SimplicialLocalization
