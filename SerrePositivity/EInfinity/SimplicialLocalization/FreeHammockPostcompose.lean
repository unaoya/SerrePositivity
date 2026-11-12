module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockArrowPoint
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions

/-!
# 元の射による自由 hammock の後合成と両比較の自然性

概要：元の射の同じ持ち上げ点を合成へ代入する。
方針：合成保存と元の点の回収の二つの厳密な等式を使う。
規約：元の射・全単体・元の両比較を保持する。
使われ方：DK と hammock の高次比較の終域変数の自然性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory MonoidalCategory Hammock
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category) {Y Z : C.category}

def freeHammockPostcompose (g : Y ⟶ Z) :
    freeHammockDiagonal C X Y ⟶ freeHammockDiagonal C X Z :=
  (ρ_ (freeHammockDiagonal C X Y)).inv ≫
    (𝟙 _ ⊗ₘ freeHammockArrowPoint C g) ≫ freeHammockDiagonalComposition C X Y Z

def localizationPostcompose (g : Y ⟶ Z) : localizationHom C X Y ⟶ localizationHom C X Z :=
  (ρ_ (localizationHom C X Y)).inv ≫
    (𝟙 _ ⊗ₘ localizationArrowPoint C g) ≫ localizationComposition C X Y Z

lemma freeHammockPostcompose_comparison (g : Y ⟶ Z) :
    freeHammockPostcompose C X g ≫ freeHammockDiagonalComparison C X Z =
      freeHammockDiagonalComparison C X Y ≫ localizationPostcompose C X g := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change (freeHammockDiagonalComparison C X Z).app n
      ((freeHammockDiagonalComposition C X Y Z).app n
        (z, (freeHammockArrowPoint C g).app n PUnit.unit)) =
    (freeHammockDiagonalComparison C X Y).app n z ≫
      (localizationArrowPoint C g).app n PUnit.unit
  rw [freeHammockDiagonalComparison_composePoint]
  exact congrArg (fun h => (freeHammockDiagonalComparison C X Y).app n z ≫ h)
    (congrArg (fun k => k.app n PUnit.unit) (freeHammockArrowPoint_comparison C g))

lemma freeHammockPostcompose_augmentation (g : Y ⟶ Z) :
    freeHammockPostcompose C X g ≫ freeHammockDiagonalAugmentation C X Z =
      freeHammockDiagonalAugmentation C X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences g) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change (freeHammockDiagonalAugmentation C X Z).app n
      ((freeHammockDiagonalComposition C X Y Z).app n
        (z, (freeHammockArrowPoint C g).app n PUnit.unit)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint C.weakEquivalences X Y Z
      ((freeHammockDiagonalAugmentation C X Y).app n z)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences g).app n PUnit.unit)
  rw [freeHammockDiagonalAugmentation_composePoint]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint C.weakEquivalences X Y Z
    ((freeHammockDiagonalAugmentation C X Y).app n z))
      (congrArg (fun k => k.app n PUnit.unit) (freeHammockArrowPoint_augmentation C g))

end SerrePositivity.EInfinity.SimplicialLocalization
