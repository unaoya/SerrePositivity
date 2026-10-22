module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenFirstPath

/-!
概要：元の S の B 遷移後の持ち上げを、Γ 源上の零底 affine 第一経路そのものに同定する。
方針：元の全零 class 像を第一 ImageWitness の式で照合し、同じ P 射影の一意性を使う。
規約：経路の一致は証明の結論。使われ方：S′・L・W の境界の実比較。
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

lemma postnikovCommonRightSourceFirst_map :
    (postnikovCommonRightSourceRefinedPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonRightDenFirstZeroPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) := by
  have ht := congrArg (fun t => postnikovCommonRightToClassifying R f c d ≫ t)
    (postnikovCommonRightSourceTransition_original_map R f c d hj)
  have hm := congrArg (fun t => postnikovCommonRightImageToSecond R f c d ≫ t)
    (postnikovCellImageForwardRelative_zero_map R (B.obj d.zero.stage).obj
      (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom)
  have hf := postnikovCommonRightDenFirstZeroPath_map R f c d hj
  simp only [postnikovCommonRightImageToSecond_eq, postnikovCommonRightDenBase,
    Category.assoc] at ht hm hf
  simpa only [postnikovCommonRightSourceRefinedPath, SquareZero.RelativeWitness.rebase_hom,
    SquareZero.RelativeWitness.precomp_hom, Category.assoc] using
    ht.trans (hm.symm.trans hf.symm)

/-- 元の S と affine 第一辺は、同じ Γ 源の全乗法的経路として厳密に一致する。 -/
lemma postnikovCommonRightSourceFirst_hom :
    (postnikovCommonRightSourceRefinedPath R f c d hj).hom =
      (postnikovCommonRightDenFirstZeroPath R f c d hj).hom := by
  apply SquareZero.baseChangePath_hom_ext (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  · exact (postnikovCommonRightSourceRefinedPath R f c d hj).projection_eq.trans
      (postnikovCommonRightDenFirstZeroPath R f c d hj).projection_eq.symm
  · exact postnikovCommonRightSourceFirst_map R f c d hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
