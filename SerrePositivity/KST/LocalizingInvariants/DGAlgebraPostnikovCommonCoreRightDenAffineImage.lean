module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenDirectSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathImageWhisker

/-!
概要：分母の正規化 affine 経路を、元の二 ImageWitness の同じ Γ 上の合成へ同定する。
方針：元の係数表示同型の全経路式を、元の Γ と分母零底同型で写す。
規約：二段自然性の選択を変えない。使われ方：元の分母輪郭との厳密照合。
-/

@[expose] public section
noncomputable section
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

def postnikovCommonRightDenImageComposite :=
  postnikovCellImageComposite R (B.obj d.zero.stage).obj (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom

lemma postnikovCommonRightDenAffineCommon_image_hom :
    (postnikovCommonRightDenAffineCommonPath R hn f c d hj).hom ≫
      Path.map R (postnikovCommonRightDenDirectImageIso R hn f c d hj).hom =
    postnikovCellImageToSecond R (postnikovCommonClassBase R hn f c d) ≫
      (postnikovCommonRightDenImageComposite R hn f c d hj).hom := by
  let h := postnikovCellFactorizationImagePath_hom R (B.obj d.zero.stage).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R hn f c d hj) (B.obj i).obj
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
    (postnikovCommonRightDenDirect_factorization R hn f c d hj)
  exact h

lemma postnikovCommonRightDenAffinePath_image_hom :
    (postnikovCommonRightDenAffinePath R hn f c d hj).hom =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCommonRightDenImageComposite R hn f c d hj).hom ≫
        Path.map R (postnikovCommonRightDenCompositeZeroIso R hn f c d hj).hom := by
  change (postnikovCommonRightToFactorization R hn f c d ≫
    ((postnikovCommonRightDenAffineCommonPath R hn f c d hj).hom ≫
      Path.map R (postnikovCommonRightDenDirectToZero R hn f c d hj))) = _
  let h := Path.map_image_whisker R (postnikovCommonRightToFactorization R hn f c d)
    (postnikovCommonRightDenAffineCommonPath R hn f c d hj).hom
    (postnikovCellImageToSecond R (postnikovCommonClassBase R hn f c d))
    (postnikovCommonRightDenImageComposite R hn f c d hj).hom
    (postnikovCommonRightDenDirectImageIso R hn f c d hj).hom
    (postnikovCommonRightDenCompositeZeroIso R hn f c d hj).hom
    (postnikovCommonRightDenAffineCommon_image_hom R hn f c d hj)
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
