module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnReversePointWeak
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardLeftWeak
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnLeftWeak
public import SerrePositivity.EInfinity.Hammock.CoefficientProductDiagonal

/-!
# 元の混合二方向の左係数積と元の二つの対角の同型

概要：元の左係数の対角比較をnative 指定 Hom と残りの語の対角比較の積へ戻す。
方針：同じ元の射を係数積の対角弱不変性へ代入する。
規約：残りの元の語の比較だけを帰納仮定にする。
使われ方：DK5.7の混合二方向の帰納段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory MonoidalCategory SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeReverseFirstLeftSpaceMap :=
  leftSpaceMap (freeFirstMarkedObjectEquiv C) (freeReverseFirstTargetObjectEquiv C w X Y)
    (freeReverseFirstMarkedObjectEquiv_naturality C w X Y)
    (freeReverseFirstTargetObjectEquiv_naturality C w X Y) (freeBackwardForwardAugmentation C w X Y)
    (freeReverseFirstMarkedObjectEquiv_augmentation C w X Y) Z
def freeReverseFirstLeftSpaceIso :
    leftSpace (freeBackwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeReverseFirstMarkedObjectEquiv_naturality C w X Y) Z ≅
    leftSpace (freeBackwardBackwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
        (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) Z ⊗
      leftSpace (freeForwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
        (freeFirstMarkedObjectEquiv_naturality C w X Y) Z where
  hom :=
    { app n := ↾fun σ => (σ ⋙ CategoryTheory.Prod.fst _ _, σ ⋙ CategoryTheory.Prod.snd _ _)
      naturality n m θ := by apply ConcreteCategory.hom_ext; intro σ; rfl }
  inv :=
    { app n := ↾fun p => p.1.prod' p.2
      naturality n m θ := by apply ConcreteCategory.hom_ext; intro p; rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    rfl
def freeReverseFirstTargetLeftSpaceIso :
    leftSpace ((Functor.const SimplexCategoryᵒᵖ).obj (backwardForwardData C w X Y))
      (freeReverseFirstTargetObjectEquiv C w X Y)
      (freeReverseFirstTargetObjectEquiv_naturality C w X Y) Z ≅
    leftSpace ((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y))
        (freeBackwardFirstTargetObjectEquiv C w X Y)
        (freeFirstTargetObjectEquiv_naturality C w X Y) Z ⊗
      leftSpace ((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y))
        (freeFirstTargetObjectEquiv C w X Y)
        (freeBackwardFirstTargetObjectEquiv_naturality C w X Y) Z where
  hom :=
    { app n := ↾fun σ => (σ ⋙ CategoryTheory.Prod.fst _ _, σ ⋙ CategoryTheory.Prod.snd _ _)
      naturality n m θ := by apply ConcreteCategory.hom_ext; intro σ; rfl }
  inv :=
    { app n := ↾fun p => p.1.prod' p.2
      naturality n m θ := by apply ConcreteCategory.hom_ext; intro p; rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    rfl
lemma freeReverseFirstLeftSpaceIso_augmentation :
    freeReverseFirstLeftSpaceMap C w X Y Z ≫ (freeReverseFirstTargetLeftSpaceIso C w X Y Z).hom =
    (freeReverseFirstLeftSpaceIso C w X Y Z).hom ≫
      (freeBackwardFirstLeftSpaceMap C w X Y Z ⊗ₘ freeFirstLeftSpaceMap C w X Y Z) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl
end SerrePositivity.EInfinity.Hammock.FirstColumn
