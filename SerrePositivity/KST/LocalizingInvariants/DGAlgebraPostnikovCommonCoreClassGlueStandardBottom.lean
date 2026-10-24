module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardContour
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassContourBottomZero :=
  (postnikovCommonRightContourBottomRefinedPath R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)

def postnikovCommonClassStandardThenBottom :=
  (postnikovCommonClassStandardContourPath R hn f c d hj).comp
    (postnikovCommonClassContourBottomZero R hn f c d hj)

def postnikovCommonClassViaBThenBottomZero :=
  (postnikovCommonClassViaBContourZero R hn f c d hj).comp
    (postnikovCommonClassContourBottomZero R hn f c d hj)

def postnikovCommonClassGlueStandardBottom :=
  (postnikovCommonRightGlueZeroRelative R hn f c d hj).reverse.comp
    (postnikovCommonClassStandardThenBottom R hn f c d hj)

def postnikovCommonClassGlueViaBBottom :=
  (postnikovCommonRightGlueZeroRelative R hn f c d hj).reverse.comp
    (postnikovCommonClassViaBThenBottomZero R hn f c d hj)

def postnikovCommonClassGlueStandardBottomSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassGlueStandardBottom R hn f c d hj)
    (postnikovCommonClassGlueViaBBottom R hn f c d hj) :=
  ((postnikovCommonClassStandardContourSquare R hn f c d hj).append
    (postnikovCommonClassContourBottomZero R hn f c d hj)).prepend
    (postnikovCommonRightGlueZeroRelative R hn f c d hj).reverse

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
