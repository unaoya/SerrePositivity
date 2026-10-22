module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroAffineRefinement

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightCompositeToZeroClass :=
  SquareZero.baseChangeMap
    ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) 1)
    (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
      postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1

lemma postnikovCommonRightZeroAffineViaA_map :
    (postnikovCommonRightZeroAffineViaA R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonRightAffineRefinedViaA R f c d hj).hom ≫
      Path.map R (postnikovCommonRightCompositeToZeroClass R f c d hj) := by
  change ((postnikovCommonRightAffineRefinedViaA R f c d hj).hom ≫
    Path.map R (postnikovCommonRightCompositeZeroIso R f c d hj).hom) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightCompositeZeroIso_map]
  rfl

lemma postnikovCommonRightZeroAffineViaB_map :
    (postnikovCommonRightZeroAffineViaB R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonRightAffineRefinedViaB R f c d hj).hom ≫
      Path.map R (postnikovCommonRightCompositeToZeroClass R f c d hj) := by
  change ((postnikovCommonRightAffineRefinedViaB R f c d hj).hom ≫
    Path.map R (postnikovCommonRightCompositeZeroIso R f c d hj).hom) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightCompositeZeroIso_map]
  rfl

lemma postnikovCommonRightZeroAffineSquare_map :
    (postnikovCommonRightZeroAffineSquare R f c d hj).hom ≫ Path.map R (Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (postnikovCommonRightAffineRefinedSquare R f c d hj).hom ≫
      Path.map R (Path.map R (postnikovCommonRightCompositeToZeroClass R f c d hj)) := by
  change ((postnikovCommonRightAffineRefinedSquare R f c d hj).hom ≫
    Path.map R (Path.map R (postnikovCommonRightCompositeZeroIso R f c d hj).hom)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, ← Path.map_comp, postnikovCommonRightCompositeZeroIso_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
