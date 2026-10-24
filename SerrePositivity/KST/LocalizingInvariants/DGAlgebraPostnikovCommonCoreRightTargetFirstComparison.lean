module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightTargetFirstPath

/-!
概要：元の T の B 遷移後の持ち上げを、Γ 源上の零底 affine 第一経路そのものに同定する。
方針：元の全零 class 像を第一 ImageWitness の式で照合し、同じ P 射影の一意性を使う。
規約：経路の一致は証明の結論。使われ方：T′・L・W の境界の実比較。
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

lemma postnikovCommonRightTargetFirst_map :
    (postnikovCommonRightTargetRefinedPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (postnikovCommonRightViaBFirstZeroPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) := by
  have ht := congrArg (fun t => postnikovCommonRightToClassifying R hn f c d ≫ t)
    (postnikovCommonRightTargetTransition_original_map R hn f c d hj)
  have hm := congrArg (fun t => postnikovCommonRightImageToSecond R hn f c d ≫ t)
    (postnikovCellImageForwardRelative_zero_map R (A.obj i).obj (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      (roofRefine R hn f c d.zero.source_le).roof.numerator
      (f.app i).hom (B.transition hj).hom)
  have hf := postnikovCommonRightViaBFirstZeroPath_map R hn f c d hj
  simp only [postnikovCommonRightImageToSecond_eq, postnikovCommonRightBase,
    Category.assoc] at ht hm hf
  simpa only [postnikovCommonRightTargetRefinedPath, SquareZero.RelativeWitness.rebase_hom,
    SquareZero.RelativeWitness.precomp_hom, Category.assoc] using
    ht.trans (hm.symm.trans hf.symm)

/-- 元の T と affine 第一辺は、同じ Γ 源の全乗法的経路として厳密に一致する。 -/
lemma postnikovCommonRightTargetFirst_hom :
    (postnikovCommonRightTargetRefinedPath R hn f c d hj).hom =
      (postnikovCommonRightViaBFirstZeroPath R hn f c d hj).hom := by
  apply SquareZero.baseChangePath_hom_ext (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
  · exact (postnikovCommonRightTargetRefinedPath R hn f c d hj).projection_eq.trans
      (postnikovCommonRightViaBFirstZeroPath R hn f c d hj).projection_eq.symm
  · exact postnikovCommonRightTargetFirst_map R hn f c d hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
