module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellLiftComposition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeCellCompositionHomotopy

/-!
概要：直接の Postnikov 自然性と二段の自然性合成が誘導する実 class 輸送を比較する。
方針：元の二段の経路を底を固定して合成し、直接経路との cell 二重充填を使う。
規約：並行経路の存在を追加入力しない。使われ方：Γ の自然性合成の実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C) (g : C ⟶ D)

def postnikovCellLiftComposedWitness : Path.Witness R
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionSource R B C D P n hn b f g)
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionTarget R B C D P n hn b f g) :=
  RelativePath.cellComp R (postnikovPerturbedProjection R D n hn)
    (postnikovPerturbedProjection_surjective R D n hn)
    (postnikovCellLiftCompositionFirst R B C D P n hn b f g)
    (postnikovCellLiftCompositionSecond R B C D P n hn b f g)
    (postnikovCellLiftCompositionFirst_relative R B C D P n hn b f g)
    (postnikovCellLiftCompositionSecond_relative R B C D P n hn b f g)

lemma postnikovCellLiftComposedWitness_relative :
    (postnikovCellLiftComposedWitness R B C D P n hn b f g).hom ≫
      Path.map R (postnikovPerturbedProjection R D n hn) =
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫
      postnikovPerturbedProjection R D n hn) ≫ Path.diagonal R (postnikov R D n) :=
  RelativePath.cellComp_relative R _ _ _ _ _ _

lemma postnikovCellLiftDirectRefined_relative :
    ((postnikovCellLiftCompositionDirect R B C D P n hn b f g).precomp
      (cellAugmentation R (cellResolution R (cellResolution R P)))).hom ≫
      Path.map R (postnikovPerturbedProjection R D n hn) =
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫
      postnikovPerturbedProjection R D n hn) ≫ Path.diagonal R (postnikov R D n) :=
  SquareZeroExtension.relativeCellComposition_direct_relative R _ _
    (postnikovCellLiftCompositionDirect_relative R B C D P n hn b f g)

def postnikovCellCompositionClassDirect : SquareZero.RelativeWitness
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫
      postnikovPerturbedProjection R D n hn)
    (postnikovShiftedLayerBimodule R D n hn 1)
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫ postnikovPerturbedClass R D n hn)
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionTarget R B C D P n hn b f g) ≫
      postnikovPerturbedClass R D n hn) :=
  SquareZero.cellClassWitness R (postnikovPerturbedProjection R D n hn)
    ((postnikovCellLiftCompositionDirect R B C D P n hn b f g).precomp
      (cellAugmentation R (cellResolution R (cellResolution R P))))
    (postnikovCellLiftDirectRefined_relative R B C D P n hn b f g)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)

def postnikovCellCompositionClassComposed : SquareZero.RelativeWitness
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫
      postnikovPerturbedProjection R D n hn)
    (postnikovShiftedLayerBimodule R D n hn 1)
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫ postnikovPerturbedClass R D n hn)
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionTarget R B C D P n hn b f g) ≫
      postnikovPerturbedClass R D n hn) :=
  SquareZero.cellClassWitness R (postnikovPerturbedProjection R D n hn)
    (postnikovCellLiftComposedWitness R B C D P n hn b f g)
    (postnikovCellLiftComposedWitness_relative R B C D P n hn b f g)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)

def postnikovCellCompositionClassSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellCompositionClassDirect R B C D P n hn b f g)
    (postnikovCellCompositionClassComposed R B C D P n hn b f g) :=
  SquareZero.cellClassWitnessSquare R (postnikovPerturbedProjection R D n hn)
    (postnikovPerturbedProjection_surjective R D n hn)
    (postnikovPerturbedProjection_quasiIso R D n hn)
    ((postnikovCellLiftCompositionDirect R B C D P n hn b f g).precomp
      (cellAugmentation R (cellResolution R (cellResolution R P))))
    (postnikovCellLiftComposedWitness R B C D P n hn b f g)
    (postnikovCellLiftDirectRefined_relative R B C D P n hn b f g)
    (postnikovCellLiftComposedWitness_relative R B C D P n hn b f g)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)

def postnikovCellClassCompositionTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovShiftedLayerBimodule R D n hn 1)
      (postnikovCellCompositionClassDirect R B C D P n hn b f g))
    (SquareZeroExtension.transport (postnikovShiftedLayerBimodule R D n hn 1)
      (postnikovCellCompositionClassComposed R B C D P n hn b f g)) :=
  SquareZeroExtension.relativeCellCompositionTransportHomotopy R
    (postnikovPerturbedProjection R D n hn) (postnikovPerturbedProjection_surjective R D n hn)
    (postnikovPerturbedProjection_quasiIso R D n hn)
    (postnikovCellLiftCompositionDirect R B C D P n hn b f g)
    (postnikovCellLiftCompositionFirst R B C D P n hn b f g)
    (postnikovCellLiftCompositionSecond R B C D P n hn b f g)
    (postnikovCellLiftCompositionDirect_relative R B C D P n hn b f g)
    (postnikovCellLiftCompositionFirst_relative R B C D P n hn b f g)
    (postnikovCellLiftCompositionSecond_relative R B C D P n hn b f g)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
