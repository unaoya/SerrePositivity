module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedTransitionRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver

/-!
概要：fixed Γ の遷移の右像を、零底に相対的な元の G として保持する。
方針：底変更射による相対経路の移送と、全経路の厳密同定を使う。
規約：Γ の元の射影と指定端点を保持。使われ方：右 class 互換性の実比較。
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

def postnikovCommonRightGlueZeroRelative :=
  (postnikovCommonRightGlueRefinedPath R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)

variable (e : PostnikovZeroLayerInverse R n f j i hj)

lemma postnikovCommonClassFixedTransitionZeroRight_projection :
    (postnikovCommonClassFixedTransitionZeroRightPath R hn f c d hj e).hom ≫
      Path.map R (SquareZero.projection _ _) =
    (postnikovCommonClassStandardGlueProjection R hn f c d ≫
      postnikovCommonRightClassifyingBase R hn f c d hj) ≫
      Path.diagonal R (postnikov R (B.obj j).obj 0) := by
  rw [postnikovCommonClassFixedTransitionZeroRight_hom R hn f c d hj e]
  exact (postnikovCommonRightGlueZeroRelative R hn f c d hj).projection_eq

/-- 同じ G の端点表示で、全射は fixed 遷移の元の右像そのもの。 -/
def postnikovCommonRightFixedTransitionZeroRelative :=
  (postnikovCommonRightGlueZeroRelative R hn f c d hj).replaceHom
    (postnikovCommonClassFixedTransitionZeroRightPath R hn f c d hj e).hom
    (postnikovCommonClassFixedTransitionZeroRight_hom R hn f c d hj e).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
