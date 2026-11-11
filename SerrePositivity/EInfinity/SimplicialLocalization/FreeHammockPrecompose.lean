module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockPostcompose

/-!
# 元の射による自由 hammock の前合成と両比較の自然性

概要：元の射の同じ持ち上げ点を合成の左へ代入する。
方針：合成保存と元の点の回収の二つの厳密な等式を使う。
規約：元の射・全単体・元の両比較を保持する。
使われ方：DK と hammock の高次比較の始域変数の自然性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory MonoidalCategory Hammock
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category} (Z : C.category)

def freeHammockPrecompose (f : X ⟶ Y) :
    freeHammockDiagonal C Y Z ⟶ freeHammockDiagonal C X Z :=
  (λ_ (freeHammockDiagonal C Y Z)).inv ≫
    (freeHammockArrowPoint C f ⊗ₘ 𝟙 _) ≫ freeHammockDiagonalComposition C X Y Z

def localizationPrecompose (f : X ⟶ Y) : localizationHom C Y Z ⟶ localizationHom C X Z :=
  (λ_ (localizationHom C Y Z)).inv ≫
    (localizationArrowPoint C f ⊗ₘ 𝟙 _) ≫ localizationComposition C X Y Z

lemma freeHammockPrecompose_comparison (f : X ⟶ Y) :
    freeHammockPrecompose C Z f ≫ freeHammockDiagonalComparison C X Z =
      freeHammockDiagonalComparison C Y Z ≫ localizationPrecompose C Z f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change (freeHammockDiagonalComparison C X Z).app n
      ((freeHammockDiagonalComposition C X Y Z).app n
        ((freeHammockArrowPoint C f).app n PUnit.unit, z)) =
    (localizationArrowPoint C f).app n PUnit.unit ≫
      (freeHammockDiagonalComparison C Y Z).app n z
  rw [freeHammockDiagonalComparison_composePoint]
  exact congrArg (fun h => h ≫ (freeHammockDiagonalComparison C Y Z).app n z)
    (congrArg (fun k => k.app n PUnit.unit) (freeHammockArrowPoint_comparison C f))

lemma freeHammockPrecompose_augmentation (f : X ⟶ Y) :
    freeHammockPrecompose C Z f ≫ freeHammockDiagonalAugmentation C X Z =
      freeHammockDiagonalAugmentation C Y Z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f) Z := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change (freeHammockDiagonalAugmentation C X Z).app n
      ((freeHammockDiagonalComposition C X Y Z).app n
        ((freeHammockArrowPoint C f).app n PUnit.unit, z)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint C.weakEquivalences X Y Z
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f).app n PUnit.unit)
      ((freeHammockDiagonalAugmentation C Y Z).app n z)
  rw [freeHammockDiagonalAugmentation_composePoint]
  exact congrArg (fun h => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint C.weakEquivalences X Y Z h
    ((freeHammockDiagonalAugmentation C Y Z).app n z))
      (congrArg (fun k => k.app n PUnit.unit) (freeHammockArrowPoint_augmentation C f))

end SerrePositivity.EInfinity.SimplicialLocalization
