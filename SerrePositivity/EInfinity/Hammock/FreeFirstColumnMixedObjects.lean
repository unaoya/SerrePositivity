module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardDiagonalAugmentation
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnObjects

/-!
# 自由解像の混合二方向の係数図式

概要：元の全自由次数の混合二方向の図式と同じ augmentation を指定する。
方針：一般の図式構成へ元の自由解像と固定対象表示を代入する。
規約：底は同じ wide 指定部分圏、対象表示も既存の表示を共有する。
使われ方：混合二方向の左対角比較の帰納段階。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory SimplicialLocalization
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
def freeForwardBackwardDiagram (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) :
    SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} :=
  forwardBackwardDiagram (freeResolution C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) w X Y

def freeForwardBackwardAugmentation (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) :
    freeForwardBackwardDiagram C w X Y ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (forwardBackwardData C w X Y) :=
  forwardBackwardAugmentation (freeResolution C) C (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) (freeResolutionAugmentationNatTrans C)
    (freeResolutionObject_augmentation C) w X Y

lemma freeMixedFirstMarkedObjectEquiv_naturality (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (Z : C.category) :
    ((freeForwardBackwardDiagram C w X Y).map θ).base.obj
      (freeFirstMarkedObjectEquiv C n Z) = freeFirstMarkedObjectEquiv C m Z :=
  freeFirstMarkedObjectEquiv_naturality C w X Y θ Z

lemma freeMixedFirstMarkedObjectEquiv_augmentation (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) (Z : C.category) :
    ((freeForwardBackwardAugmentation C w X Y).app n).base.obj
      (freeFirstMarkedObjectEquiv C n Z) = markedObjectEquiv C Z :=
  freeFirstMarkedObjectEquiv_augmentation C w X Y n Z
end SerrePositivity.EInfinity.Hammock.FirstColumn
