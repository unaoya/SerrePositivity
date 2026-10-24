module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroAffineRefinement

/-!
概要：零底へ移した affine 経路と二重経路の、元の class 標的への全射を計算する。
方針：平方零同型の厳密な射影式を経路関手で二度まで写す。
規約：端点の一致だけで代用しない。使われ方：元の classifying 輪郭経路との照合。
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

def postnikovCommonRightCompositeToZeroClass :=
  SquareZero.baseChangeMap
    ((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) n)
    (postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1) ≫
      postnikovClassToZeroBase R (B.obj j).obj n hn 1

lemma postnikovCommonRightZeroAffineViaA_map :
    (postnikovCommonRightZeroAffineViaA R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (postnikovCommonRightAffineRefinedViaA R hn f c d hj).hom ≫
      Path.map R (postnikovCommonRightCompositeToZeroClass R hn f c d hj) := by
  change ((postnikovCommonRightAffineRefinedViaA R hn f c d hj).hom ≫
    Path.map R (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightCompositeZeroIso_map]
  rfl

lemma postnikovCommonRightZeroAffineViaB_map :
    (postnikovCommonRightZeroAffineViaB R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (postnikovCommonRightAffineRefinedViaB R hn f c d hj).hom ≫
      Path.map R (postnikovCommonRightCompositeToZeroClass R hn f c d hj) := by
  change ((postnikovCommonRightAffineRefinedViaB R hn f c d hj).hom ≫
    Path.map R (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightCompositeZeroIso_map]
  rfl

lemma postnikovCommonRightZeroAffineSquare_map :
    (postnikovCommonRightZeroAffineSquare R hn f c d hj).hom ≫ Path.map R (Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))) =
    (postnikovCommonRightAffineRefinedSquare R hn f c d hj).hom ≫
      Path.map R (Path.map R (postnikovCommonRightCompositeToZeroClass R hn f c d hj)) := by
  change ((postnikovCommonRightAffineRefinedSquare R hn f c d hj).hom ≫
    Path.map R (Path.map R (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, ← Path.map_comp, postnikovCommonRightCompositeZeroIso_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
