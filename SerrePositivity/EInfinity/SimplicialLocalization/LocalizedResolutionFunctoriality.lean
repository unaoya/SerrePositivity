module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionFunctoriality
public import SerrePositivity.EInfinity.SimplicialLocalization.ResolutionObjects

/-!
# 局所化した自由解像の係数関手と対象表示

概要：Dwyer–Kan の全局所化解像へ相対関手を送り、同じ対象表示を保つ。
方針：全自由解像の係数射を厳密に局所化し、augmentation の自然性を使う。
規約：単体作用素と係数の両方に自然な元の対象表示を保持する。
使われ方：固定対象の Hom の間の単体写像の構成。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory

/-- 概要：相対関手が局所化した全自由解像に誘導する係数射（Dwyer–Kan）。
方針：同じ自由解像の係数射を厳密な局所化で送る。
規約：元の全単体作用素と両立する自然変換。
使われ方：固定対象の Hom の係数比較。 -/
def localizedFreeResolutionMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    localizedFreeResolution C ⟶ localizedFreeResolution D :=
  Functor.whiskerRight (freeResolutionMap F) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor

/-- 概要：全局所化解像は相対圏の係数関手をなす（Dwyer–Kan）。
方針：自由解像の係数関手と後合成関手を合成する。
規約：恒等と合成を厳密に保つ。
使われ方：係数関手の単体的局所化への延長。 -/
def localizedFreeResolutionFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} ⥤ SimplicialObject Cat.{u, u} :=
  freeResolutionFunctor ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory Cat).obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor

/-- 概要：局所化した係数射は元の augmentation に自然（Dwyer–Kan）。
方針：自由解像の augmentation の自然性を同じ厳密な局所化で送る。
規約：各次数の元の比較射を保持する。
使われ方：固定対象表示の係数自然性。 -/
lemma localizedFreeResolutionMap_augmentation {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) :
    (localizedFreeResolutionMap F).app n ≫ (localizedFreeResolutionAugmentation D).app n =
      (localizedFreeResolutionAugmentation C).app n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor.map F := by
  have h := NatTrans.congr_app (freeResolutionMap_augmentation F) n
  change (freeResolutionMap F).app n ≫ (freeResolutionAugmentationNatTrans D).app n =
    (freeResolutionAugmentationNatTrans C).app n ≫ F at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor.map ((freeResolutionMap F).app n) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor.map ((freeResolutionAugmentationNatTrans D).app n) ≫ 𝟙 _) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor.map ((freeResolutionAugmentationNatTrans C).app n) ≫ 𝟙 _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor.map F
  simp only [Category.comp_id]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor.map_comp _ _).symm.trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor.map h).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor.map_comp _ _))

/-- 概要：局所化した係数射は同じ対象の各次数の表示を保つ（Dwyer–Kan）。
方針：augmentation の対象単射性と係数自然性を使う。
規約：対象の選択の自然性を仮定せず証明する。
使われ方：元の対象を固定した Hom の間の単体写像。 -/
lemma localizedFreeResolutionMap_object {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((localizedFreeResolutionMap F).app n).toFunctor.obj
        (localizedFreeResolutionObject C n X) =
      localizedFreeResolutionObject D n (F.functor.obj X) := by
  apply (localizedFreeResolutionObjectEquiv D n).injective
  have h := congrArg Cat.Hom.toFunctor (localizedFreeResolutionMap_augmentation F n)
  change ((localizedFreeResolutionMap F).app n).toFunctor ⋙
      ((localizedFreeResolutionAugmentation D).app n).toFunctor =
    ((localizedFreeResolutionAugmentation C).app n).toFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap F at h
  change ((localizedFreeResolutionAugmentation D).app n).toFunctor.obj
      (((localizedFreeResolutionMap F).app n).toFunctor.obj
        (localizedFreeResolutionObject C n X)) =
    (localizedFreeResolutionObjectEquiv D n)
      (localizedFreeResolutionObject D n (F.functor.obj X))
  rw [← Functor.comp_obj, h, Functor.comp_obj]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap F).obj
      ((localizedFreeResolutionObjectEquiv C n) (localizedFreeResolutionObject C n X)) = _
  unfold localizedFreeResolutionObject
  rw [(localizedFreeResolutionObjectEquiv C n).apply_symm_apply,
    (localizedFreeResolutionObjectEquiv D n).apply_symm_apply]
  exact Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac F) X

end SerrePositivity.EInfinity.SimplicialLocalization
