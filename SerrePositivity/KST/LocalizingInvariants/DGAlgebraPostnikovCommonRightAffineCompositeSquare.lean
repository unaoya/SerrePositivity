module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellAffineFactorizationSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCompositeSquare

/-!
概要：A 遷移と fⱼ、fᵢ と B 遷移の実 affine class 合成を同じ底上で比較する。
方針：元の二因子分解の cell 比較に、cell–affine の実二重経路を縦合成する。
規約：比較二重経路を追加入力しない。使われ方：Γ の右像貼合せへの実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightAffineNaturalityViaA : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d))
    (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
    (postnikovCommonRightNaturalityCompositeSource R f c d hj)
    (postnikovCommonRightNaturalityCompositeTarget R f c d hj) :=
  postnikovCellFactorizationAffineCommonWitness R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj) (A.obj j).obj
    (A.transition hj).hom (f.app j).hom rfl

def postnikovCommonRightAffineNaturalityViaB : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d))
    (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
    (postnikovCommonRightNaturalityCompositeSource R f c d hj)
    (postnikovCommonRightNaturalityCompositeTarget R f c d hj) :=
  postnikovCellFactorizationAffineCommonWitness R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj) (B.obj i).obj
    (f.app i).hom (B.transition hj).hom (congrArg (fun t => t.hom) (f.naturality hj)).symm

def postnikovCommonRightAffineCompositeSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightAffineNaturalityViaA R f c d hj)
    (postnikovCommonRightAffineNaturalityViaB R f c d hj) :=
  postnikovCellAffineFactorizationCommonSquare R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj) (A.obj j).obj (B.obj i).obj
    (A.transition hj).hom (f.app j).hom rfl
    (f.app i).hom (B.transition hj).hom (congrArg (fun t => t.hom) (f.naturality hj)).symm

def postnikovCommonRightAffineCompositeTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightAffineNaturalityViaA R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightAffineNaturalityViaB R f c d hj)) :=
  SquareZeroExtension.transportHomotopy _ (postnikovCommonRightAffineCompositeSquare R f c d hj)

lemma postnikovCommonRightAffineCompositeTransportHomotopy_left :
    (postnikovCommonRightAffineCompositeTransportHomotopy R f c d hj).hom ≫
      Path.map R (SquareZeroExtension.relativeLeft
        (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
        (postnikovCommonRightNaturalityCompositeTarget R f c d hj)) =
    SquareZeroExtension.relativeLeft (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightNaturalityCompositeSource R f c d hj) ≫
      Path.diagonal R (cellResolution R (cellResolution R (cellResolution R
        (cellResolution R (postnikovCommonClassBase R f c d))))) :=
  SquareZeroExtension.transportHomotopy_left _
    (postnikovCommonRightAffineCompositeSquare R f c d hj)

lemma postnikovCommonRightAffineCompositeTransportHomotopy_right :
    (postnikovCommonRightAffineCompositeTransportHomotopy R f c d hj).hom ≫
      Path.map R (SquareZeroExtension.relativeRight
        (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
        (postnikovCommonRightNaturalityCompositeTarget R f c d hj)) =
    SquareZeroExtension.relativeRight (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightNaturalityCompositeSource R f c d hj) ≫
      Path.diagonal R (postnikovCommonClassBase R f c d) :=
  SquareZeroExtension.transportHomotopy_right _
    (postnikovCommonRightAffineCompositeSquare R f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
