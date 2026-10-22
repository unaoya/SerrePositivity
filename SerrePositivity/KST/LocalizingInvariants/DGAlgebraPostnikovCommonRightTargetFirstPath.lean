module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaBImageMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightTargetOriginalPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageForwardZero

/-!
概要：元の Γ 源上で、T の B 遷移後の持ち上げと零底 affine 第一辺を取り出す。
方針：元の指定細分・実係数射を使い、同じ Γ 射影上の相対経路を保つ。
規約：全経路を変更しない。使われ方：二射影の一意性による第一辺の実同定。
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

lemma postnikovCommonRightImageToSecond_projection :
    postnikovCommonRightImageToSecond R f c d ≫
      (cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫
        cellAugmentation R (postnikovCommonClassBase R f c d)) =
      postnikovCommonClassStandardGlueProjection R f c d := by
  rw [postnikovCommonRightImageToSecond, Category.assoc,
    postnikovCellImageToSecond_projection, postnikovCommonRightToFactorization_projection]

def postnikovCommonRightTargetRefinedPath :=
  ((postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedTargetRelative R f c d)).precomp
      (postnikovCommonRightToClassifying R f c d)).rebase
      (postnikovCommonRightToClassifying_projection R f c d)

def postnikovCommonRightViaBFirstZeroPath :=
  (((postnikovCellImageForwardRelative R (A.obj i).obj (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (f.app i).hom (B.transition hj).hom).mapOver (𝟙 _)
    (postnikovCommonRightViaBImageToZero R f c d hj)
    ((postnikovCommonRightViaBImageToZero_projection R f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightImageToSecond R f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightImageToSecond_projection R f c d)

lemma postnikovCommonRightViaBFirstZeroPath_map :
    (postnikovCommonRightViaBFirstZeroPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCellImageForwardRelative R (A.obj i).obj (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
        (f.app i).hom (B.transition hj).hom).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
          postnikovMap R (f.app i).hom 1) ≫ postnikovMap R (B.transition hj).hom 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
          postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) := by
  change (postnikovCommonRightImageToSecond R f c d ≫
    ((postnikovCellImageForwardRelative R (A.obj i).obj (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
      (f.app i).hom (B.transition hj).hom).hom ≫
        Path.map R (postnikovCommonRightViaBImageToZero R f c d hj))) ≫ _ = _
  simp only [Category.assoc, ← Path.map_comp, postnikovCommonRightViaBImageToZero_map]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
