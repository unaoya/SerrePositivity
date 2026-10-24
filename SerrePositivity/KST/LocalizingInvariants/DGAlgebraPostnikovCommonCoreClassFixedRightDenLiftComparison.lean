module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightLiftProjection
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeHomProjections

/-!
概要：P 上へ戻した native 分母経路を、元の分母自然性の全経路そのものへ同定する。
方針：元の P 射影と零 class 像の両一致から、経路 pullback の一意性を使う。
規約：端点・低次射影の一致で代用しない。使われ方：元の分母と native 右模型の比較。
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

lemma postnikovCommonClassFixedRightDenominator_zero_hom :
    (postnikovCommonClassFixedRightDenominatorPath R hn f c d hj e).hom =
    (postnikovCommonRightDenContourPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) := by
  let h := SquareZero.RelativeWitness.transferEndpoints_hom
    (postnikovCommonClassGlueStandardBottom R hn f c d hj)
    (postnikovCommonClassFixedRightCompletedPath R hn f c d hj e)
    (postnikovCommonClassFixedRightCompletedPath_hom R hn f c d hj e).symm
    (postnikovCommonClassDenContourZero R hn f c d hj)
  let k := SquareZero.RelativeWitness.mapOver_hom
    (postnikovCommonRightDenContourPath R hn f c d hj)
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)
  exact h.trans k

lemma postnikovCommonClassFixedRightDenominatorLift_hom :
    (postnikovCommonClassFixedRightDenominatorLift R hn f c d hj e).hom =
      (postnikovCommonRightDenContourPath R hn f c d hj).hom := by
  apply SquareZero.baseChangePath_hom_ext (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
  · exact (postnikovCommonClassFixedRightDenominatorLift R hn f c d hj e).projection_eq.trans
      (postnikovCommonRightDenContourPath R hn f c d hj).projection_eq.symm
  · exact (postnikovCommonClassFixedRightDenominatorLift_map R hn f c d hj e).trans
      (postnikovCommonClassFixedRightDenominator_zero_hom R hn f c d hj e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
