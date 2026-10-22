module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareSolveLeft
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareMapOver

/-!
概要：元の G を実二重経路で相殺し、分母自然性を G⁻¹⋅分子自然性⋅W と比較する。
方針：元の指定自然性四角形に反転を前置し、零底への二重経路も保持する。
規約：元の Γ・G・W と両端を保持。使われ方：fixed class 互換性の右三角形。
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

def postnikovCommonRightGlueSolvedPath :=
  (postnikovCommonRightGlueRefinedPath R f c d hj).reverse.comp
    (postnikovCommonRightViaBThenBottom R f c d hj)

def postnikovCommonRightGlueSolvedSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenContourPath R f c d hj)
    (postnikovCommonRightGlueSolvedPath R f c d hj) :=
  SquareZero.RelativeWitnessSquare.solveLeft
    (postnikovCommonRightGlueRefinedPath R f c d hj)
    (postnikovCommonRightDenContourPath R f c d hj)
    (postnikovCommonRightViaBThenBottom R f c d hj)
    (postnikovCommonRightGlueNaturalitySquare R f c d hj)

def postnikovCommonRightGlueSolvedZeroSquare :=
  (postnikovCommonRightGlueSolvedSquare R f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
    (SquareZero.baseChangeMap_projection _ _)

def postnikovCommonRightGlueSolvedTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightDenContourPath R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueSolvedPath R f c d hj)) :=
  SquareZeroExtension.transportHomotopy _ (postnikovCommonRightGlueSolvedSquare R f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
