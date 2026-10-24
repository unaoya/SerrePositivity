module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellAffineFactorizationSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCompositeSquare

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightAffineCompositeSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

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
  PostnikovCommonCore.postnikovCommonRightAffineNaturalityViaA
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightAffineNaturalityViaB : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d))
    (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
    (postnikovCommonRightNaturalityCompositeSource R f c d hj)
    (postnikovCommonRightNaturalityCompositeTarget R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightAffineNaturalityViaB
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightAffineCompositeSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightAffineNaturalityViaA R f c d hj)
    (postnikovCommonRightAffineNaturalityViaB R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightAffineCompositeSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightAffineCompositeTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightAffineNaturalityViaA R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightAffineNaturalityViaB R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightAffineCompositeTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightAffineCompositeTransportHomotopy_left :
    (postnikovCommonRightAffineCompositeTransportHomotopy R f c d hj).hom ≫
      Path.map R (SquareZeroExtension.relativeLeft
        (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
        (postnikovCommonRightNaturalityCompositeTarget R f c d hj)) =
    SquareZeroExtension.relativeLeft (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightNaturalityCompositeSource R f c d hj) ≫
      Path.diagonal R (cellResolution R (cellResolution R (cellResolution R
        (cellResolution R (postnikovCommonClassBase R f c d))))) :=
  PostnikovCommonCore.postnikovCommonRightAffineCompositeTransportHomotopy_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightAffineCompositeTransportHomotopy_right :
    (postnikovCommonRightAffineCompositeTransportHomotopy R f c d hj).hom ≫
      Path.map R (SquareZeroExtension.relativeRight
        (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
        (postnikovCommonRightNaturalityCompositeTarget R f c d hj)) =
    SquareZeroExtension.relativeRight (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightNaturalityCompositeSource R f c d hj) ≫
      Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightAffineCompositeTransportHomotopy_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
