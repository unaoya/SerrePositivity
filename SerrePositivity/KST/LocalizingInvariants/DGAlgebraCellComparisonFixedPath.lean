module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellComparisonPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathFixedBase

/-!
概要：元の二つの cell 比較射の間の経路を、底の元の全経路を固定して持ち上げる。
方針：augmentation 上の元の経路を、両端を固定する境界持ち上げへ渡す。
規約：二重 cell 源上で底への全射影を保持。使われ方：元の右経路と class の比較。
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

def cellResolutionMapFixedPathWitness : Path.Witness R
    (cellAugmentation R (cellResolution R A) ≫ cellResolutionMap R f)
    (cellAugmentation R (cellResolution R A) ≫ cellResolutionMap R g) :=
  Path.Witness.cellLiftFixedBase R (cellAugmentation R B) (cellAugmentation_surjective R B)
    (cellAugmentation_quasiIso R B) (cellResolutionMapAugmentationWitness R w)

lemma cellResolutionMapFixedPathWitness_map : (cellResolutionMapFixedPathWitness R w).hom ≫
    Path.map R (cellAugmentation R B) =
    (cellAugmentation R (cellResolution R A) ≫ cellAugmentation R A) ≫ w.hom := by
  rw [cellResolutionMapFixedPathWitness, Path.Witness.cellLiftFixedBase_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
