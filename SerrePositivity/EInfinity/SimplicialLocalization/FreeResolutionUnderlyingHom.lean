module

public import SerrePositivity.EInfinity.SimplicialLocalization.RelativeUnderlyingCategory
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockObjects
public import SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHomFunctoriality

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory

variable (C : RelativeCategory.{u})

def freeResolutionUnderlyingDiagram : SimplicialObject Cat.{u, u} :=
  freeResolution C ⋙ underlyingCategoryFunctor

def freeResolutionUnderlyingAugmentation : freeResolutionUnderlyingDiagram C ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj C.category :=
  Functor.whiskerRight (freeResolutionAugmentationNatTrans C) underlyingCategoryFunctor ≫
    (Functor.constComp SimplexCategoryᵒᵖ C underlyingCategoryFunctor).hom

def freeResolutionHom (X Y : C.category) : SSet.{u} :=
  FixedObjectHom.functor (freeResolutionUnderlyingDiagram C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) X Y

def freeResolutionHomAugmentation (X Y : C.category) : freeResolutionHom C X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (X ⟶ Y) := by
  let η := FixedObjectHom.coefficientNatTrans (freeResolutionUnderlyingDiagram C)
    ((Functor.const SimplexCategoryᵒᵖ).obj C.category) (freeResolutionObject C)
    (fun _ (X : C.category) => X)
    (fun θ X => freeResolutionObject_naturality C θ X) (fun _ _ => rfl)
    (freeResolutionUnderlyingAugmentation C) id
    (fun n X => by exact freeResolutionObject_augmentation C n X) X Y
  refine { app := η.app, naturality := ?_ }
  intro n m θ
  apply ConcreteCategory.hom_ext
  intro f
  simpa [freeResolutionHom, FixedObjectHom.functor, FixedObjectHom.map]
    using ConcreteCategory.congr_hom (η.naturality θ) f

lemma freeResolutionHomAugmentation_app (X Y : C.category) (n : SimplexCategoryᵒᵖ)
    (f : (freeResolutionHom C X Y).obj n) :
    (freeResolutionHomAugmentation C X Y).app n f =
      eqToHom (freeResolutionObject_augmentation C n X).symm ≫
        ((freeResolutionAugmentationNatTrans C).app n).functor.map f ≫
          eqToHom (freeResolutionObject_augmentation C n Y) := rfl

end SerrePositivity.EInfinity.SimplicialLocalization
