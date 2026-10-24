module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightComposite

/-!
概要：元の fixed class 互換性・fⱼ の自然性・指定 W を実相対経路として合成する。
方針：全経路の同定から W の接合端点だけを移し、同じ affine 結合則を使う。
規約：fixed 互換性と元の W の全射を保持。使われ方：元の native 右 class 比較。
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
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassFixedRightBottom :=
  SquareZero.RelativeWitness.followWithEndpoints
    (postnikovCommonClassGlueStandardPath R hn f c d hj)
    (postnikovCommonClassFixedCompatibilityNaturality R hn f c d hj e)
    (postnikovCommonClassFixedCompatibilityNaturality_hom R hn f c d hj e).symm
    (postnikovCommonClassContourBottomZero R hn f c d hj)

def postnikovCommonClassFixedRightCompletedPath :=
  (postnikovCommonClassFixedCompatibilityNaturality R hn f c d hj e).comp
    (postnikovCommonClassFixedRightBottom R hn f c d hj e)

lemma postnikovCommonClassFixedRightCompletedPath_hom :
    (postnikovCommonClassFixedRightCompletedPath R hn f c d hj e).hom =
      (postnikovCommonClassGlueStandardBottom R hn f c d hj).hom := by
  have hc := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := postnikovCommonClassFixedCompatibilityNaturality R hn f c d hj e)
    (w := postnikovCommonClassFixedRightBottom R hn f c d hj e)
    (v' := postnikovCommonClassGlueStandardPath R hn f c d hj)
    (w' := postnikovCommonClassContourBottomZero R hn f c d hj)
    (postnikovCommonClassFixedCompatibilityNaturality_hom R hn f c d hj e) rfl
  have ha := SquareZero.RelativeWitness.comp_assoc_hom
    (postnikovCommonRightGlueZeroRelative R hn f c d hj).reverse
    (postnikovCommonClassStandardContourPath R hn f c d hj)
    (postnikovCommonClassContourBottomZero R hn f c d hj)
  exact hc.trans ha

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
