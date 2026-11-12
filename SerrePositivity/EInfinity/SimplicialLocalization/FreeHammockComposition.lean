module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockComparison
public import SerrePositivity.EInfinity.Hammock.FixedObjectComposition
public import SerrePositivity.EInfinity.Hammock.FixedObjectEvaluationComposition

/-!
# 元の自由 hammock の対角の合成

概要：元の全自由次数の合成を同じ対角の合成へ移す。
方針：固定対象の全図式の自然な合成と対角の積との同型を使う。
規約：元の各次数の合成を保持する。
使われ方：DK の左右比較の合成保存と両端点の高次自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory CategoryTheory.Limits Hammock MonoidalCategory
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y Z : C.category)

def freeHammockResolutionComposition :
    freeHammockResolution C X Y ⊗ freeHammockResolution C Y Z ⟶
      freeHammockResolution C X Z :=
  FixedObjectDiagram.hammockComposition (freeResolution C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) X Y Z

def freeHammockDiagonalTensorIso :
    freeHammockDiagonal C X Y ⊗ freeHammockDiagonal C Y Z ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (freeHammockResolution C X Y ⊗ freeHammockResolution C Y Z) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def freeHammockDiagonalComposition :
    freeHammockDiagonal C X Y ⊗ freeHammockDiagonal C Y Z ⟶ freeHammockDiagonal C X Z :=
  (freeHammockDiagonalTensorIso C X Y Z).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (freeHammockResolutionComposition C X Y Z)

lemma freeHammockDiagonalComposition_app (n : SimplexCategoryᵒᵖ)
    (p : (freeHammockDiagonal C X Y).obj n) (q : (freeHammockDiagonal C Y Z).obj n) :
    (freeHammockDiagonalComposition C X Y Z).app n (p, q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n X) (freeResolutionObject C n Y)
        (freeResolutionObject C n Z) p q := rfl

lemma freeHammockAugmentation_fixedColimitMap (n : SimplexCategoryᵒᵖ) :
    (freeHammockAugmentation C X Y).app n =
      Relative.fixedColimitMap ((freeResolutionAugmentationNatTrans C).app n)
        (freeResolutionObject_augmentation C n X)
        (freeResolutionObject_augmentation C n Y) := by
  change colim.map ((freeHammockGraphAugmentation C X Y).app n) =
    colim.map (Relative.fixedGraphDiagramMap ((freeResolutionAugmentationNatTrans C).app n)
      (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y))
  apply congrArg colim.map
  apply NatTrans.ext
  funext w
  exact (Relative.fixedGraphDiagramMap_app ((freeResolutionAugmentationNatTrans C).app n)
    (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y) w).symm

lemma freeHammockDiagonalAugmentation_composePoint (n : SimplexCategoryᵒᵖ)
    (p : (freeHammockDiagonal C X Y).obj n) (q : (freeHammockDiagonal C Y Z).obj n) :
    (freeHammockDiagonalAugmentation C X Z).app n
        ((freeHammockDiagonalComposition C X Y Z).app n (p, q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint C.weakEquivalences X Y Z
        ((freeHammockDiagonalAugmentation C X Y).app n p)
        ((freeHammockDiagonalAugmentation C Y Z).app n q) := by
  change ((freeHammockAugmentation C X Z).app n).app n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint _ _ _ _ p q) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint _ _ _ _
        (((freeHammockAugmentation C X Y).app n).app n p)
        (((freeHammockAugmentation C Y Z).app n).app n q)
  rw [freeHammockAugmentation_fixedColimitMap, freeHammockAugmentation_fixedColimitMap,
    freeHammockAugmentation_fixedColimitMap]
  exact Relative.fixedColimitMap_composePoint _ _ _ _ p q

lemma freeHammockDiagonalComparison_composePoint (n : SimplexCategoryᵒᵖ)
    (p : (freeHammockDiagonal C X Y).obj n) (q : (freeHammockDiagonal C Y Z).obj n) :
    (freeHammockDiagonalComparison C X Z).app n
        ((freeHammockDiagonalComposition C X Y Z).app n (p, q)) =
      (freeHammockDiagonalComparison C X Y).app n p ≫
        (freeHammockDiagonalComparison C Y Z).app n q :=
  (freeHammockLocalizationObjects C).colimitValue_composePoint n X Y Z n p q

lemma freeHammockDiagonalComposition_augmentation :
    freeHammockDiagonalComposition C X Y Z ≫ freeHammockDiagonalAugmentation C X Z =
      (freeHammockDiagonalAugmentation C X Y ⊗ₘ
        freeHammockDiagonalAugmentation C Y Z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences X Y Z := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact freeHammockDiagonalAugmentation_composePoint C X Y Z n z.1 z.2

lemma freeHammockDiagonalComposition_comparison :
    freeHammockDiagonalComposition C X Y Z ≫ freeHammockDiagonalComparison C X Z =
      (freeHammockDiagonalComparison C X Y ⊗ₘ
        freeHammockDiagonalComparison C Y Z) ≫ localizationComposition C X Y Z := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact freeHammockDiagonalComparison_composePoint C X Y Z n z.1 z.2

end SerrePositivity.EInfinity.SimplicialLocalization
