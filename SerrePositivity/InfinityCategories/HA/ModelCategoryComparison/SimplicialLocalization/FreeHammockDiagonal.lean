module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DoubleSimplicialDiagonal
public import SerrePositivity.EInfinity.Hammock.ReducedColimit

/-!
# 元の自由相対解像の hammock の対角と左比較

概要：DK 命題2.2の元の対角 hammock と、元の hammock 余極限への射を構成する。
方針：元の二重単体的図式と augmentation に同じ対角関手を適用する。
規約：元の全次数・全作用素・元の左射を保持する。弱同値性は後続。
使われ方：元の DK Hom と hammock の高次比較の共通始域。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory

def freeHammockDiagonal (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution C X Y)

def freeHammockDiagonalAugmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonal C X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation C X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalConstantIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y)).hom

lemma freeHammockDiagonal_obj (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonal C X Y).obj n = ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution C X Y).obj n).obj n := rfl

lemma freeHammockDiagonalAugmentation_app (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y).app n = ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation C X Y).app n).app n :=
  rfl

def freeHammockDiagonalReduction (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonal C X Y ⟶ _root_.SerrePositivity.EInfinity.Hammock.reducedSimplicialSet C.weakEquivalences X Y :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y ≫ (_root_.SerrePositivity.EInfinity.Hammock.reducedColimitIso C.weakEquivalences X Y).hom

lemma freeHammockDiagonalReduction_fac (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y ≫ (_root_.SerrePositivity.EInfinity.Hammock.reducedColimitIso C.weakEquivalences X Y).inv =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
