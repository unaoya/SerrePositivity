module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightViaBImageMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightTargetOriginalPath
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

lemma postnikovCommonRightImageToSecond_projection :
    postnikovCommonRightImageToSecond R hn f c d ≫
      (cellAugmentation R (cellResolution R (postnikovCommonClassBase R hn f c d)) ≫
        cellAugmentation R (postnikovCommonClassBase R hn f c d)) =
      postnikovCommonClassStandardGlueProjection R hn f c d := by
  rw [postnikovCommonRightImageToSecond, Category.assoc,
    postnikovCellImageToSecond_projection, postnikovCommonRightToFactorization_projection]

def postnikovCommonRightTargetRefinedPath :=
  ((postnikovCommonRightTransitionLift R hn f c d hj
    (postnikovCommonRightFixedTargetRelative R hn f c d)).precomp
      (postnikovCommonRightToClassifying R hn f c d)).rebase
      (postnikovCommonRightToClassifying_projection R hn f c d)

def postnikovCommonRightViaBFirstZeroPath :=
  (((postnikovCellImageForwardRelative R (A.obj i).obj (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (f.app i).hom (B.transition hj).hom).mapOver (𝟙 _)
    (postnikovCommonRightViaBImageToZero R hn f c d hj)
    ((postnikovCommonRightViaBImageToZero_projection R hn f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightImageToSecond R hn f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R hn f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightImageToSecond_projection R hn f c d)

lemma postnikovCommonRightViaBFirstZeroPath_map :
    (postnikovCommonRightViaBFirstZeroPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCellImageForwardRelative R (A.obj i).obj (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        (roofRefine R hn f c d.zero.source_le).roof.numerator
        (f.app i).hom (B.transition hj).hom).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
          postnikovMap R (f.app i).hom n) ≫ postnikovMap R (B.transition hj).hom n)
        (postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1) ≫
          postnikovClassToZeroBase R (B.obj j).obj n hn 1) := by
  change (postnikovCommonRightImageToSecond R hn f c d ≫
    ((postnikovCellImageForwardRelative R (A.obj i).obj (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      (roofRefine R hn f c d.zero.source_le).roof.numerator
      (f.app i).hom (B.transition hj).hom).hom ≫
        Path.map R (postnikovCommonRightViaBImageToZero R hn f c d hj))) ≫ _ = _
  simp only [Category.assoc, ← Path.map_comp, postnikovCommonRightViaBImageToZero_map]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
