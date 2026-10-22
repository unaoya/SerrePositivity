module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellNaturalityComposition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCellClassCompositionSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrecomp

/-!
概要：Postnikov の元の二段自然性の cell 合成を、元の二 class 経路の affine 合成と比較する。
方針：指定 cellCompLift の普遍 class 合成を使う比較を、元の摂動射と二経路へ適用する。
規約：同じ係数・底・両端を保持。使われ方：三経路貼合せと二因子分解比較の照合。
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

def postnikovCellClassAffineComposite : SquareZero.RelativeWitness
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫
        postnikovPerturbedProjection R D n hn)
    (postnikovShiftedLayerBimodule R D n hn 1)
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫ postnikovPerturbedClass R D n hn)
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionTarget R B C D P n hn b f g) ≫
      postnikovPerturbedClass R D n hn) :=
  SquareZero.relativeClassAffineRefined R (postnikovPerturbedProjection R D n hn)
    (postnikovCellLiftCompositionFirst R B C D P n hn b f g)
      (postnikovCellLiftCompositionFirst_relative R B C D P n hn b f g)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)
      (postnikovCellLiftCompositionSecond R B C D P n hn b f g)
    (postnikovCellLiftCompositionSecond_relative R B C D P n hn b f g)

def postnikovCellClassCellComposite : SquareZero.RelativeWitness
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫
        postnikovPerturbedProjection R D n hn)
    (postnikovShiftedLayerBimodule R D n hn 1)
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫ postnikovPerturbedClass R D n hn)
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      postnikovCellLiftCompositionTarget R B C D P n hn b f g) ≫
      postnikovPerturbedClass R D n hn) :=
  SquareZero.relativeClassCellComposite R (postnikovPerturbedProjection R D n hn)
    (postnikovCellLiftCompositionFirst R B C D P n hn b f g)
      (postnikovCellLiftCompositionFirst_relative R B C D P n hn b f g)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)
      (postnikovCellLiftCompositionSecond R B C D P n hn b f g)
    (postnikovCellLiftCompositionSecond_relative R B C D P n hn b f g)
    (postnikovPerturbedProjection_surjective R D n hn)

def postnikovCellClassCellAffineSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellClassCellComposite R B C D P n hn b f g)
    (postnikovCellClassAffineComposite R B C D P n hn b f g) :=
  SquareZero.cellClassCompositionSquare R (postnikovPerturbedProjection R D n hn)
    (postnikovPerturbedProjection_surjective R D n hn)
    (postnikovCellLiftCompositionFirst R B C D P n hn b f g)
      (postnikovCellLiftCompositionSecond R B C D P n hn b f g)
    (postnikovCellLiftCompositionFirst_relative R B C D P n hn b f g)
    (postnikovCellLiftCompositionSecond_relative R B C D P n hn b f g)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)

def postnikovCellCompositionClassAffine : SquareZero.RelativeWitness
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
  (postnikovCellClassAffineComposite R B C D P n hn b f g).precomp
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))))

/-- 既存の四重 cell 源上の cell 合成を、その元の二 class 経路の affine 合成へ結ぶ。 -/
def postnikovCellCompositionAffineSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellCompositionClassComposed R B C D P n hn b f g)
    (postnikovCellCompositionClassAffine R B C D P n hn b f g) := by
  let z := (postnikovCellClassCellAffineSquare R B C D P n hn b f g).precomp
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))))
  exact SquareZero.RelativeWitnessSquare.replacePaths z rfl rfl

def postnikovCellCompositionAffineTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovShiftedLayerBimodule R D n hn 1)
      (postnikovCellCompositionClassComposed R B C D P n hn b f g))
    (SquareZeroExtension.transport (postnikovShiftedLayerBimodule R D n hn 1)
      (postnikovCellCompositionClassAffine R B C D P n hn b f g)) :=
  SquareZeroExtension.transportHomotopy _
    (postnikovCellCompositionAffineSquare R B C D P n hn b f g)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
