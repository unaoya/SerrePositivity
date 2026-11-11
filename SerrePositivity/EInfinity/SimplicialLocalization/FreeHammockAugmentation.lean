module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHammockAugmentation

/-!
# 元の自由解像の hammock 図式から元の hammock への augmentation

概要：同じ自由相対 augmentation は、全語の図式と元の余極限の比較を与える。
方針：元の対象表示の augmentation の等式を一般の固定対象の比較へ代入する。
規約：全単体作用素に自然な実際の射を構成する。弱同値性は後続。
使われ方：DK 命題2.2の左比較の元の対角前の射。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory CategoryTheory.Limits

def freeHammockGraphAugmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    (freeHammockWordDiagram C X Y).flip ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphAugmentation (freeResolution C) C (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) (freeResolutionAugmentationNatTrans C)
    (freeResolutionObject_augmentation C) X Y

def freeHammockAugmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockResolution C X Y ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.hammockAugmentation (freeResolution C) C (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) (freeResolutionAugmentationNatTrans C)
    (freeResolutionObject_augmentation C) X Y

lemma freeHammockAugmentation_fac (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockAugmentation C X Y =
      Functor.whiskerRight (freeHammockGraphAugmentation C X Y) colim ≫
        (Functor.constComp SimplexCategoryᵒᵖ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y)
          colim).hom := rfl

end SerrePositivity.EInfinity.SimplicialLocalization
