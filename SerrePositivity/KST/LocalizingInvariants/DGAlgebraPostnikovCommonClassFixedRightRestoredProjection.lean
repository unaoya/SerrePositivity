module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightRestored

/-!
概要：元の P 上へ復元した右 class 二重経路の native 零 class 像と全底射影を同定する。
方針：表示移送の全射保存と、底変更二重経路の厳密な二射影式を合成する。
規約：元の全二重経路を回収する。使われ方：右模型三角形の coherence の比較。
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

lemma postnikovCommonClassFixedRightRestoredSquare_hom :
    (postnikovCommonClassFixedRightRestoredSquare R f c d hj e).hom =
      (postnikovCommonClassFixedRightRelativeSquare R f c d hj e).hom := by
  let h := SquareZero.RelativeWitnessSquare.reindex_hom
    (postnikovCommonClassFixedRightRelativeSquare R f c d hj e)
    (postnikovCommonRightDenContourPath R f c d hj)
    (postnikovCommonClassFixedRightRestoredPath R f c d hj e)
    (postnikovCommonClassFixedRightDenominatorLift_hom R f c d hj e)
    (postnikovCommonClassFixedRightRestoredPath_hom R f c d hj e).symm
  exact h

lemma postnikovCommonClassFixedRightRestoredSquare_map :
    (postnikovCommonClassFixedRightRestoredSquare R f c d hj e).hom ≫ Path.map R
      (Path.map R (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (postnikovCommonClassFixedRightZeroSquare R f c d hj e).hom := by
  let h := congrArg (fun k => k ≫ Path.map R (Path.map R
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))))
    (postnikovCommonClassFixedRightRestoredSquare_hom R f c d hj e)
  let k := SquareZero.RelativeWitnessSquare.rebase_hom
    (postnikovCommonClassFixedRightZeroSquare R f c d hj e)
    (postnikovCommonClassFixedZeroBase_projection R f c d hj)
  exact h.trans ((postnikovCommonClassFixedRightRelativeSquare_map R f c d hj e).trans k)

lemma postnikovCommonClassFixedRightRestoredSquare_projection :
    (postnikovCommonClassFixedRightRestoredSquare R f c d hj e).hom ≫ Path.map R
      (Path.map R (SquareZero.projection (postnikovCommonClassBase R f c d)
        (postnikovCommonRightClassifyingLayer R f c d hj))) =
    (postnikovCommonClassStandardGlueProjection R f c d ≫
      Path.diagonal R (postnikovCommonClassBase R f c d)) ≫
        Path.diagonal R (Path.algebra R (postnikovCommonClassBase R f c d)) :=
  (postnikovCommonClassFixedRightRestoredSquare R f c d hj e).projection_eq

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
