module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeWitness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassNaturality

/-!
概要：元の Postnikov cell class の相対経路を、源の切断代数という共通底へ移す。
方針：元の二重 cell augmentation と係数制限を使い、実相対経路の厳密な底変更を適用。
規約：元の底と係数比較を固定。使われ方：係数 cokernel の実乗法的零経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

abbrev classCommonBase := cellAugmentation R (cellResolution R (postnikov R B n)) ≫
  cellAugmentation R (postnikov R B n)

abbrev classCommonSource := cellAugmentation R (cellResolution R (postnikov R B n)) ≫
  postnikovCellClass R B n hn ≫ postnikovDerivationTargetMap R f n hn

abbrev classCommonTarget := cellAugmentation R (cellResolution R (postnikov R B n)) ≫
  cellResolutionMap R (postnikovMap R f n) ≫ postnikovCellClass R C n hn

lemma classCommonSource_projection : classCommonSource R f n hn ≫
    SquareZero.projection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1) =
      classCommonBase R (B := B) n ≫ postnikovMap R f n := by
  rw [classCommonSource, Category.assoc, Category.assoc, postnikovDerivationTargetMap_projection,
    ← Category.assoc (postnikovCellClass R B n hn), postnikovCellClass_projection]
  rfl

lemma classCommonTarget_projection : classCommonTarget R f n hn ≫
    SquareZero.projection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1) =
      classCommonBase R (B := B) n ≫ postnikovMap R f n := by
  rw [classCommonTarget, Category.assoc, Category.assoc, postnikovCellClass_projection,
    cellResolutionMap_augmentation]
  rfl

def postnikovClassCommonBaseSource := SquareZero.baseChangeLift (postnikovMap R f n)
  (postnikovShiftedLayerBimodule R C n hn 1) (classCommonBase R (B := B) n)
  (classCommonSource R f n hn) (classCommonSource_projection R f n hn)

def postnikovClassCommonBaseTarget := SquareZero.baseChangeLift (postnikovMap R f n)
  (postnikovShiftedLayerBimodule R C n hn 1) (classCommonBase R (B := B) n)
  (classCommonTarget R f n hn) (classCommonTarget_projection R f n hn)

def postnikovClassCommonBaseWitness : Path.Witness R (postnikovClassCommonBaseSource R f n hn)
    (postnikovClassCommonBaseTarget R f n hn) :=
  SquareZero.baseChangeWitness (postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1)
    (classCommonBase R (B := B) n) (classCommonSource R f n hn) (classCommonTarget R f n hn)
    (classCommonSource_projection R f n hn) (classCommonTarget_projection R f n hn)
    (postnikovCellClassNaturalityWitness R f n hn)
    (postnikovCellClassNaturalityWitness_relative R f n hn)

lemma postnikovClassCommonBaseWitness_relative :
    (postnikovClassCommonBaseWitness R f n hn).hom ≫ Path.map R
      (SquareZero.projection (postnikov R B n)
        (bimoduleRestrict (postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1))) =
          classCommonBase R (B := B) n ≫ Path.diagonal R (postnikov R B n) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
