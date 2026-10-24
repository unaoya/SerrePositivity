module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightLift

/-!
概要：元の P へ戻した native 右 class 経路と二重経路の二射影を保持する。
方針：底変更 lift の厳密な射影式を、元の Γ と classifying 底射へ適用する。
規約：存在だけでなく全経路の零 class 像を保存。使われ方：元の分母経路との実同定。
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

lemma postnikovCommonClassFixedRightCompletedLift_map :
    (postnikovCommonClassFixedRightCompletedLift R hn f c d hj e).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (postnikovCommonClassFixedRightCompletedPath R hn f c d hj e).hom := by
  let h := SquareZero.baseChangeRelativeWitness_map
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    (postnikovCommonClassStandardGlueProjection R hn f c d)
    (postnikovCommonClassFixedRightCompletedZero R hn f c d hj e)
  exact h.trans (SquareZero.RelativeWitness.rebase_hom _ _)

lemma postnikovCommonClassFixedRightDenominatorLift_map :
    (postnikovCommonClassFixedRightDenominatorLift R hn f c d hj e).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (postnikovCommonClassFixedRightDenominatorPath R hn f c d hj e).hom := by
  let h := SquareZero.baseChangeRelativeWitness_map
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    (postnikovCommonClassStandardGlueProjection R hn f c d)
    (postnikovCommonClassFixedRightDenominatorZero R hn f c d hj e)
  exact h.trans (SquareZero.RelativeWitness.rebase_hom _ _)

lemma postnikovCommonClassFixedRightRelativeSquare_map :
    (postnikovCommonClassFixedRightRelativeSquare R hn f c d hj e).hom ≫ Path.map R
      (Path.map R (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))) =
    (postnikovCommonClassFixedRightRebasedZeroSquare R hn f c d hj e).hom := by
  let h := SquareZero.baseChangeSquareHom_map
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    (postnikovCommonClassStandardGlueProjection R hn f c d)
    (postnikovCommonClassFixedRightRebasedZeroSquare R hn f c d hj e)
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
