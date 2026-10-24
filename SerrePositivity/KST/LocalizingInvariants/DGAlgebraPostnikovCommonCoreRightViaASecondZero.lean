module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightViaAImageMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightTargetFirstPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageZeroMap

/-!
概要：元の Γ 源上で、A 遷移と fⱼ の零底 affine 第二辺を取り出す。
方針：元の指定細分・ViaA の実係数射を使い、同じ Γ 射影上の相対経路を保つ。
規約：全経路を変更しない。使われ方：fⱼ の元の class 自然性との同定。
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

def postnikovCommonRightViaASecondZeroPath :=
  (((postnikovCellImageRelative R (A.obj j).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    ((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (A.transition hj).hom n) (f.app j).hom).mapOver (𝟙 _)
    (postnikovCommonRightViaAImageToZero R hn f c d hj)
    ((postnikovCommonRightViaAImageToZero_projection R hn f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightImageToSecond R hn f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R hn f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightImageToSecond_projection R hn f c d)

lemma postnikovCommonRightViaASecondZeroPath_map :
    (postnikovCommonRightViaASecondZeroPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCellClassOverNaturalityWitness R (A.obj j).obj (B.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        ((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
          postnikovMap R (A.transition hj).hom n) (f.app j).hom).hom ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj n hn 1) := by
  change (postnikovCommonRightImageToSecond R hn f c d ≫
    ((postnikovCellImageRelative R (A.obj j).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      ((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (A.transition hj).hom n) (f.app j).hom).hom ≫
      Path.map R (postnikovCommonRightViaAImageToZero R hn f c d hj))) ≫ _ = _
  simp only [Category.assoc, ← Path.map_comp, postnikovCommonRightViaAImageToZero_map]
  exact congrArg (fun k => postnikovCommonRightImageToSecond R hn f c d ≫ k)
    (postnikovCellImageRelative_zero_map R (A.obj j).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      ((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (A.transition hj).hom n) (f.app j).hom)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
