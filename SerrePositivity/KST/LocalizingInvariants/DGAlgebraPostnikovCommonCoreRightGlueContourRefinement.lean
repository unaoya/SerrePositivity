module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueContour
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightComparisonRefinement
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCompositeZeroCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareBoundary
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrecomp

/-!
概要：元の G を含む貼合せ輪郭比較を、元の Γ 源・射影上へ移す。
方針：準同型な指定細分射を全二重経路へ前合成し、同じ P 射影に移す。
規約：G,S′,R,T′,L,W の全経路を保持。使われ方：零底の二因子分解比較との照合。
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

def postnikovCommonRightGlueContourRefinedLeft :=
  ((postnikovCommonRightGlueContourSquare R hn f c d hj).leftPath.precomp
    (postnikovCommonRightToClassifying R hn f c d)).rebase
    (postnikovCommonRightToClassifying_projection R hn f c d)

def postnikovCommonRightGlueContourRefinedRight :=
  ((postnikovCommonRightGlueContourSquare R hn f c d hj).rightPath.precomp
    (postnikovCommonRightToClassifying R hn f c d)).rebase
    (postnikovCommonRightToClassifying_projection R hn f c d)

def postnikovCommonRightGlueContourRefinedSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightGlueContourRefinedLeft R hn f c d hj)
    (postnikovCommonRightGlueContourRefinedRight R hn f c d hj) :=
  ((postnikovCommonRightGlueContourSquare R hn f c d hj).precomp
    (postnikovCommonRightToClassifying R hn f c d)).rebase
    (postnikovCommonRightToClassifying_projection R hn f c d)

lemma postnikovCommonRightGlueContourRefinedSquare_hom :
    (postnikovCommonRightGlueContourRefinedSquare R hn f c d hj).hom =
      postnikovCommonRightToClassifying R hn f c d ≫
        (postnikovCommonRightGlueContourSquare R hn f c d hj).hom := rfl

def postnikovCommonRightGlueContourRefinedTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R hn f c d hj)
      (postnikovCommonRightGlueContourRefinedLeft R hn f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R hn f c d hj)
      (postnikovCommonRightGlueContourRefinedRight R hn f c d hj)) :=
  SquareZeroExtension.transportHomotopy _
    (postnikovCommonRightGlueContourRefinedSquare R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
