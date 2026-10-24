module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenAffineContour
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightRestored

/-!
概要：元の直接 B 遷移の自然性と、復元した native fixed 右 class 合成を実比較する。
方針：二段分母の全射同定で両端を揃え、既存の二重経路を縦合成する。
規約：元の Γ・P・直接遷移・native 合成を保持。使われ方：実右逆三角形の模型照合。
-/

@[expose] public section
noncomputable section
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

def postnikovCommonRightDenDirectContourPath :=
  SquareZero.RelativeWitness.transferEndpoints (postnikovCommonRightDenAffinePath R hn f c d hj)
    (postnikovCommonRightDenContourPath R hn f c d hj)
    (postnikovCommonRightDenAffinePath_contour_hom R hn f c d hj)
    (postnikovCommonRightDenDirectPath R hn f c d hj)

lemma postnikovCommonRightDenDirectContourPath_hom :
    (postnikovCommonRightDenDirectContourPath R hn f c d hj).hom =
      (postnikovCommonRightDenDirectPath R hn f c d hj).hom := by
  let h := SquareZero.RelativeWitness.transferEndpoints_hom
    (postnikovCommonRightDenAffinePath R hn f c d hj) (postnikovCommonRightDenContourPath R hn f c d hj)
    (postnikovCommonRightDenAffinePath_contour_hom R hn f c d hj)
    (postnikovCommonRightDenDirectPath R hn f c d hj)
  exact h

def postnikovCommonRightDenDirectContourSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenDirectContourPath R hn f c d hj)
    (postnikovCommonRightDenContourPath R hn f c d hj) :=
  (postnikovCommonRightDenDirectAffineSquare R hn f c d hj).reindex _ _
    (postnikovCommonRightDenDirectContourPath_hom R hn f c d hj).symm
    (postnikovCommonRightDenAffinePath_contour_hom R hn f c d hj)

variable (e : PostnikovZeroLayerInverse R n f j i hj)

def postnikovCommonRightDenDirectRestoredSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenDirectContourPath R hn f c d hj)
    (postnikovCommonClassFixedRightRestoredPath R hn f c d hj e) :=
  (postnikovCommonRightDenDirectContourSquare R hn f c d hj).trans
    (postnikovCommonClassFixedRightRestoredSquare R hn f c d hj e)

def postnikovCommonRightDenDirectRestoredTransportHomotopy :=
  SquareZeroExtension.transportHomotopy (postnikovCommonRightClassifyingLayer R hn f c d hj)
    (postnikovCommonRightDenDirectRestoredSquare R hn f c d hj e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
