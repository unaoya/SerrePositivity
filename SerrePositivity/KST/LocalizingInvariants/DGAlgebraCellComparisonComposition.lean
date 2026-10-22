module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellAugmentation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathLift

/-!
概要：cell 比較射の合成を、同じ元の augmentation 上の実相対経路で比較する。
方針：合成と選択済み比較の augmentation が一致し、全射準同型上の cell 経路を使う。
規約：二重 cell augmentation を前合成する。使われ方：引き戻した class の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : B ⟶ C)

lemma cellResolutionMap_comp_augmentation : (cellResolutionMap R f ≫ cellResolutionMap R g) ≫
    cellAugmentation R C = cellResolutionMap R (f ≫ g) ≫ cellAugmentation R C := by
  rw [Category.assoc, cellResolutionMap_augmentation, ← Category.assoc,
    cellResolutionMap_augmentation, cellResolutionMap_augmentation, Category.assoc]

def cellResolutionMapCompositionWitness : Path.Witness R
    (cellAugmentation R (cellResolution R A) ≫ (cellResolutionMap R f ≫ cellResolutionMap R g))
    (cellAugmentation R (cellResolution R A) ≫ cellResolutionMap R (f ≫ g)) :=
  RelativePath.cellPathWitness R (cellAugmentation R C) (cellAugmentation_surjective R C)
    (cellAugmentation_quasiIso R C) (cellResolutionMap R f ≫ cellResolutionMap R g)
    (cellResolutionMap R (f ≫ g)) (cellResolutionMap_comp_augmentation R f g)

lemma cellResolutionMapCompositionWitness_relative :
    (cellResolutionMapCompositionWitness R f g).hom ≫ Path.map R (cellAugmentation R C) =
      (cellAugmentation R (cellResolution R A) ≫ (cellResolutionMap R f ≫ cellResolutionMap R g) ≫
        cellAugmentation R C) ≫ Path.diagonal R C :=
  RelativePath.cellPathWitness_relative _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
