module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockAugmentation
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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory

def freeHammockDiagonal (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (freeHammockResolution C X Y)

def freeHammockDiagonalAugmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockDiagonal C X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (freeHammockAugmentation C X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalConstantIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y)).hom

lemma freeHammockDiagonal_obj (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) :
    (freeHammockDiagonal C X Y).obj n = ((freeHammockResolution C X Y).obj n).obj n := rfl

lemma freeHammockDiagonalAugmentation_app (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) :
    (freeHammockDiagonalAugmentation C X Y).app n = ((freeHammockAugmentation C X Y).app n).app n :=
  rfl

def freeHammockDiagonalReduction (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockDiagonal C X Y ⟶ Hammock.reducedSimplicialSet C.weakEquivalences X Y :=
  freeHammockDiagonalAugmentation C X Y ≫ (Hammock.reducedColimitIso C.weakEquivalences X Y).hom

lemma freeHammockDiagonalReduction_fac (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockDiagonalReduction C X Y ≫ (Hammock.reducedColimitIso C.weakEquivalences X Y).inv =
      freeHammockDiagonalAugmentation C X Y := by
  simp only [freeHammockDiagonalReduction, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.EInfinity.SimplicialLocalization
