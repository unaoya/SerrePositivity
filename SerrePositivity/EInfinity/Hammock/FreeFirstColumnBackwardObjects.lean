module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardDiagonalAugmentation
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnObjects

/-!
# 自由解像の後向き二列の係数図式

概要：元の全自由次数の後向き二列の図式と同じ augmentation を指定する。
方針：一般の図式構成へ元の自由解像と固定対象表示を代入する。
規約：底は同じ wide 指定部分圏、対象表示も既存の表示を共有する。
使われ方：後向き二列の左対角比較の帰納段階。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory SimplicialLocalization
variable (C : RelativeCategory.{u})
def freeBackwardBackwardDiagram (w : Word) (X Y : C.category) :
    SimplicialObject TwoSidedDiagram.Data.{u} :=
  backwardBackwardDiagram (freeResolution C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) w X Y

def freeBackwardBackwardAugmentation (w : Word) (X Y : C.category) :
    freeBackwardBackwardDiagram C w X Y ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (backwardBackwardData C w X Y) :=
  backwardBackwardAugmentation (freeResolution C) C (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) (freeResolutionAugmentationNatTrans C)
    (freeResolutionObject_augmentation C) w X Y

lemma freeBackwardFirstMarkedObjectEquiv_naturality (w : Word) (X Y : C.category)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (Z : C.category) :
    ((freeBackwardBackwardDiagram C w X Y).map θ).base.obj
      (freeFirstMarkedObjectEquiv C n Z) = freeFirstMarkedObjectEquiv C m Z :=
  freeFirstMarkedObjectEquiv_naturality C w X Y θ Z

lemma freeBackwardFirstMarkedObjectEquiv_augmentation (w : Word) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) (Z : C.category) :
    ((freeBackwardBackwardAugmentation C w X Y).app n).base.obj
      (freeFirstMarkedObjectEquiv C n Z) = markedObjectEquiv C Z :=
  freeFirstMarkedObjectEquiv_augmentation C w X Y n Z
end SerrePositivity.EInfinity.Hammock.FirstColumn
