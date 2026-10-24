module

public import
SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightDenLiftComparison

/-!
概要：元の P 上で、元の分母自然性と復元した native 右 class 合成を実比較する。
方針：分母経路の全射の同定で端点を揃え、持ち上げた全二重経路を保持する。
規約：Γ 射影と native 零 class 像も厳密に保持。使われ方：元の右模型三角形の復元。
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
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassFixedRightRestoredPath :=
  SquareZero.RelativeWitness.transferEndpoints
    (postnikovCommonClassFixedRightDenominatorLift R hn f c d hj e)
    (postnikovCommonRightDenContourPath R hn f c d hj)
    (postnikovCommonClassFixedRightDenominatorLift_hom R hn f c d hj e)
    (postnikovCommonClassFixedRightCompletedLift R hn f c d hj e)

lemma postnikovCommonClassFixedRightRestoredPath_hom :
    (postnikovCommonClassFixedRightRestoredPath R hn f c d hj e).hom =
      (postnikovCommonClassFixedRightCompletedLift R hn f c d hj e).hom := by
  let h := SquareZero.RelativeWitness.transferEndpoints_hom
    (postnikovCommonClassFixedRightDenominatorLift R hn f c d hj e)
    (postnikovCommonRightDenContourPath R hn f c d hj)
    (postnikovCommonClassFixedRightDenominatorLift_hom R hn f c d hj e)
    (postnikovCommonClassFixedRightCompletedLift R hn f c d hj e)
  exact h

def postnikovCommonClassFixedRightRestoredSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenContourPath R hn f c d hj)
    (postnikovCommonClassFixedRightRestoredPath R hn f c d hj e) :=
  (postnikovCommonClassFixedRightRelativeSquare R hn f c d hj e).reindex _ _
    (postnikovCommonClassFixedRightDenominatorLift_hom R hn f c d hj e)
    (postnikovCommonClassFixedRightRestoredPath_hom R hn f c d hj e).symm

lemma postnikovCommonClassFixedRightRestoredPath_map :
    (postnikovCommonClassFixedRightRestoredPath R hn f c d hj e).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (postnikovCommonClassFixedRightCompletedPath R hn f c d hj e).hom := by
  let h := congrArg (fun k => k ≫ Path.map R
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)))
    (postnikovCommonClassFixedRightRestoredPath_hom R hn f c d hj e)
  exact h.trans (postnikovCommonClassFixedRightCompletedLift_map R hn f c d hj e)

def postnikovCommonClassFixedRightRestoredTransportHomotopy :=
  SquareZeroExtension.transportHomotopy (postnikovCommonRightClassifyingLayer R hn f c d hj)
    (postnikovCommonClassFixedRightRestoredSquare R hn f c d hj e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
