module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathReflection

/-!
概要：元の二つの底射を結ぶ実経路を、それらの cell 比較射の間の実経路へ移す。
方針：augmentation 上の元の経路を四重 cell 細分へ反映する。
規約：元の経路を入力に使い、追加の経路の存在を仮定しない。使われ方：class の底経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} {f g : A ⟶ B}
  (w : Path.Witness R f g)

def cellResolutionMapAugmentationWitness : Path.Witness R
    (cellResolutionMap R f ≫ cellAugmentation R B)
    (cellResolutionMap R g ≫ cellAugmentation R B) where
  hom := cellAugmentation R A ≫ w.hom
  source_eq := by
    rw [Category.assoc, w.source_eq]
    exact (cellResolutionMap_augmentation R f).symm
  target_eq := by
    rw [Category.assoc, w.target_eq]
    exact (cellResolutionMap_augmentation R g).symm

def cellResolutionMapPathWitness : Path.Witness R
    (iteratedCellAugmentation R (cellResolution R A) 4 ≫ cellResolutionMap R f)
    (iteratedCellAugmentation R (cellResolution R A) 4 ≫ cellResolutionMap R g) :=
  Path.Witness.cellReflectSurjective R (cellAugmentation R B) (cellAugmentation_surjective R B)
    (cellAugmentation_quasiIso R B) (cellResolutionMapAugmentationWitness R w)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
