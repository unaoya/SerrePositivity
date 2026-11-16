module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeUnderlyingCategory
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality

/-!
# 元の自由相対解像の底の固定 Hom と augmentation

概要：局所化前の元の自由解像の固定 Hom と元の圏の Hom への全次数の評価を作る。
方針：元の対象表示と元の augmentation を固定 Hom の係数自然変換へ代入する。
規約：元の全作用素と元の対象移送を保持する。
使われ方：DK ホモトピー補題2.4の底の圏の弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeResolutionUnderlyingDiagram : SimplicialObject Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.underlyingCategoryFunctor

def freeResolutionUnderlyingAugmentation : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionUnderlyingDiagram C ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj C.category :=
  Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.underlyingCategoryFunctor ≫
    (Functor.constComp SimplexCategoryᵒᵖ C _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.underlyingCategoryFunctor).hom

def freeResolutionHom (X Y : C.category) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionUnderlyingDiagram C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) X Y

def freeResolutionHomAugmentation (X Y : C.category) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHom C X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (X ⟶ Y) := by
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionUnderlyingDiagram C)
    ((Functor.const SimplexCategoryᵒᵖ).obj C.category) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
    (fun _ (X : C.category) => X)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) (fun _ _ => rfl)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionUnderlyingAugmentation C) id
    (fun n X => by exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n X) X Y
  refine { app := η.app, naturality := ?_ }
  intro n m θ
  apply ConcreteCategory.hom_ext
  intro f
  simpa [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map]
    using ConcreteCategory.congr_hom (η.naturality θ) f

lemma freeResolutionHomAugmentation_app (X Y : C.category) (n : SimplexCategoryᵒᵖ)
    (f : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHom C X Y).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomAugmentation C X Y).app n f =
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n X).symm ≫
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n).functor.map f ≫
          eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y) := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
