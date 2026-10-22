module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardContour
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareAppend
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrepend

/-!
概要：native 標準像の実比較に、元の G の反転と指定 W を接続する。
方針：同じ端点表示の二重経路へ W を後置し、G の反転を前置する。
規約：元の Γ・G・W と全二重経路を保持。使われ方：分母側との右 class 比較。
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

def postnikovCommonClassContourBottomZero :=
  (postnikovCommonRightContourBottomRefinedPath R f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
    (SquareZero.baseChangeMap_projection _ _)

def postnikovCommonClassStandardThenBottom :=
  (postnikovCommonClassStandardContourPath R f c d hj).comp
    (postnikovCommonClassContourBottomZero R f c d hj)

def postnikovCommonClassViaBThenBottomZero :=
  (postnikovCommonClassViaBContourZero R f c d hj).comp
    (postnikovCommonClassContourBottomZero R f c d hj)

def postnikovCommonClassGlueStandardBottom :=
  (postnikovCommonRightGlueZeroRelative R f c d hj).reverse.comp
    (postnikovCommonClassStandardThenBottom R f c d hj)

def postnikovCommonClassGlueViaBBottom :=
  (postnikovCommonRightGlueZeroRelative R f c d hj).reverse.comp
    (postnikovCommonClassViaBThenBottomZero R f c d hj)

def postnikovCommonClassGlueStandardBottomSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassGlueStandardBottom R f c d hj)
    (postnikovCommonClassGlueViaBBottom R f c d hj) :=
  ((postnikovCommonClassStandardContourSquare R f c d hj).append
    (postnikovCommonClassContourBottomZero R f c d hj)).prepend
    (postnikovCommonRightGlueZeroRelative R f c d hj).reverse

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
