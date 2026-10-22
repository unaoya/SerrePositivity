module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightZeroRebase
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareBaseChange

/-!
概要：元の native 右 class 比較を、元の P と classifying 係数上の実二重経路へ戻す。
方針：底表示を揃えた元の二重経路に、既存の実底変更 pullback lift を適用する。
規約：元の Γ 射影・両端と全二重経路の零 class 像を保持。使われ方：右模型三角形。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassFixedRightDenominatorLift :=
  SquareZero.baseChangeRelativeWitness (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassFixedRightDenominatorZero R f c d hj e)

def postnikovCommonClassFixedRightCompletedLift :=
  SquareZero.baseChangeRelativeWitness (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassFixedRightCompletedZero R f c d hj e)

def postnikovCommonClassFixedRightRelativeSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassFixedRightDenominatorLift R f c d hj e)
    (postnikovCommonClassFixedRightCompletedLift R f c d hj e) :=
  SquareZero.baseChangeRelativeWitnessSquare
    (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassFixedRightRebasedZeroSquare R f c d hj e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
