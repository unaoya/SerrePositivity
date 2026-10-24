module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourLeftPath

/-!
概要：元の L を、同じ Γ 源上の零底 affine 第二経路へ全射で同定する。
方針：source trace の全零 class 像と第二 ImageWitness の底変更式を照合する。
規約：経路の一致は二射影の一意性から証明。使われ方：T′L の affine 合成への接続。
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

lemma postnikovCommonRightViaBSecondZeroPath_map :
    (postnikovCommonRightViaBSecondZeroPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        (postnikovCommonRightBase R hn f c d) (B.transition hj).hom).hom ≫
      Path.map R (postnikovClassToZeroBase R (B.obj j).obj n hn 1) := by
  change (postnikovCommonRightImageToSecond R hn f c d ≫
    ((postnikovCellImageRelative R (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      ((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (f.app i).hom n) (B.transition hj).hom).hom ≫
      Path.map R (postnikovCommonRightViaBImageToZero R hn f c d hj))) ≫ _ = _
  simp only [Category.assoc, ← Path.map_comp, postnikovCommonRightViaBImageToZero_map]
  rw [postnikovCellImageRelative_zero_map]
  rfl

lemma postnikovCommonRightContourLeftSecond_map :
    (postnikovCommonRightContourLeftRefinedPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (postnikovCommonRightViaBSecondZeroPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) := by
  have hl := congrArg (fun t => postnikovCommonRightToClassifying R hn f c d ≫ t)
    (postnikovCommonRightContourLeftPath_map R hn f c d hj)
  have hr := postnikovCommonRightViaBSecondZeroPath_map R hn f c d hj
  simp only [postnikovCommonRightImageToSecond_eq, Category.assoc] at hr
  simpa only [postnikovCommonRightContourLeftRefinedPath, SquareZero.RelativeWitness.rebase_hom,
    SquareZero.RelativeWitness.precomp_hom, Category.assoc] using hl.trans hr.symm

lemma postnikovCommonRightContourLeftSecond_hom :
    (postnikovCommonRightContourLeftRefinedPath R hn f c d hj).hom =
      (postnikovCommonRightViaBSecondZeroPath R hn f c d hj).hom := by
  apply SquareZero.baseChangePath_hom_ext (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
  · exact (postnikovCommonRightContourLeftRefinedPath R hn f c d hj).projection_eq.trans
      (postnikovCommonRightViaBSecondZeroPath R hn f c d hj).projection_eq.symm
  · exact postnikovCommonRightContourLeftSecond_map R hn f c d hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
