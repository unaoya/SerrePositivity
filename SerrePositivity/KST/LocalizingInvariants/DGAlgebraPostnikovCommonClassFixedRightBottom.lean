module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightComposite

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassFixedRightBottom :=
  SquareZero.RelativeWitness.followWithEndpoints
    (postnikovCommonClassGlueStandardPath R f c d hj)
    (postnikovCommonClassFixedCompatibilityNaturality R f c d hj e)
    (postnikovCommonClassFixedCompatibilityNaturality_hom R f c d hj e).symm
    (postnikovCommonClassContourBottomZero R f c d hj)

def postnikovCommonClassFixedRightCompletedPath :=
  (postnikovCommonClassFixedCompatibilityNaturality R f c d hj e).comp
    (postnikovCommonClassFixedRightBottom R f c d hj e)

lemma postnikovCommonClassFixedRightCompletedPath_hom :
    (postnikovCommonClassFixedRightCompletedPath R f c d hj e).hom =
      (postnikovCommonClassGlueStandardBottom R f c d hj).hom := by
  have hc := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := postnikovCommonClassFixedCompatibilityNaturality R f c d hj e)
    (w := postnikovCommonClassFixedRightBottom R f c d hj e)
    (v' := postnikovCommonClassGlueStandardPath R f c d hj)
    (w' := postnikovCommonClassContourBottomZero R f c d hj)
    (postnikovCommonClassFixedCompatibilityNaturality_hom R f c d hj e) rfl
  have ha := SquareZero.RelativeWitness.comp_assoc_hom
    (postnikovCommonRightGlueZeroRelative R f c d hj).reverse
    (postnikovCommonClassStandardContourPath R f c d hj)
    (postnikovCommonClassContourBottomZero R f c d hj)
  exact hc.trans ha

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
