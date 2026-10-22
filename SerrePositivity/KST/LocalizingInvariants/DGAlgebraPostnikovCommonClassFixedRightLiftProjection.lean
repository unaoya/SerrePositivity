module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightLift

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassFixedRightCompletedLift_map :
    (postnikovCommonClassFixedRightCompletedLift R f c d hj e).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonClassFixedRightCompletedPath R f c d hj e).hom := by
  let h := SquareZero.baseChangeRelativeWitness_map
    (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassFixedRightCompletedZero R f c d hj e)
  exact h.trans (SquareZero.RelativeWitness.rebase_hom _ _)

lemma postnikovCommonClassFixedRightDenominatorLift_map :
    (postnikovCommonClassFixedRightDenominatorLift R f c d hj e).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonClassFixedRightDenominatorPath R f c d hj e).hom := by
  let h := SquareZero.baseChangeRelativeWitness_map
    (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassFixedRightDenominatorZero R f c d hj e)
  exact h.trans (SquareZero.RelativeWitness.rebase_hom _ _)

lemma postnikovCommonClassFixedRightRelativeSquare_map :
    (postnikovCommonClassFixedRightRelativeSquare R f c d hj e).hom ≫ Path.map R
      (Path.map R (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (postnikovCommonClassFixedRightRebasedZeroSquare R f c d hj e).hom := by
  let h := SquareZero.baseChangeSquareHom_map
    (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassFixedRightRebasedZeroSquare R f c d hj e)
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
