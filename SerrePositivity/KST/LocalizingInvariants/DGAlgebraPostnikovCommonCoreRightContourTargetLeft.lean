module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightViaBZeroComposition
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourFirstComparison

/-!
概要：元の輪郭の T′L の合成を、同じ Γ 源上の既存 affineViaB 経路そのものへ同定する。
方針：二つの全経路同定と、前合成・affine 合成の厳密な保存を使う。
規約：元の T′・L・Γ 射影を保持。使われ方：貼合せの右三角形の境界の接続。
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

def postnikovCommonRightContourTargetPath :=
  let N := postnikovCommonRightClassifyingLayer R hn f c d hj
  let H := postnikovCommonRightClassifyingBaseChangeHom R hn f c d hj
  let p := postnikovCommonRightClassifyingProjection R hn f c d
  let V := postnikovCommonRightTransitionLift R hn f c d hj
    (postnikovCommonRightFixedCentralRelative R hn f c d)
  let T := postnikovCommonRightTransitionLift R hn f c d hj
    (postnikovCommonRightFixedTargetRelative R hn f c d)
  let hTop := postnikovCommonRightClassifyingBaseChangeHom_central R hn f c d hj
  SquareZero.RectangleOfHom.towardTopSource N H p V hTop T

def postnikovCommonRightContourTargetLeft :=
  (postnikovCommonRightContourTargetPath R hn f c d hj).comp
    (postnikovCommonRightContourLeftPath R hn f c d hj)

def postnikovCommonRightContourTargetLeftRefined :=
  ((postnikovCommonRightContourTargetLeft R hn f c d hj).precomp
    (postnikovCommonRightToClassifying R hn f c d)).rebase
    (postnikovCommonRightToClassifying_projection R hn f c d)

/-- 元の輪郭の T′L は元の Γ 源上の affineViaB と全乗法的経路として厳密に一致。 -/
lemma postnikovCommonRightContourTargetLeft_hom :
    (postnikovCommonRightContourTargetLeftRefined R hn f c d hj).hom =
      (postnikovCommonRightZeroAffineViaB R hn f c d hj).hom := by
  let t := postnikovCommonRightContourTargetPath R hn f c d hj
  let l := postnikovCommonRightContourLeftPath R hn f c d hj
  let e := postnikovCommonRightToClassifying R hn f c d
  have ht : (t.precomp e).hom = (postnikovCommonRightViaBFirstZeroPath R hn f c d hj).hom :=
    postnikovCommonRightContourFirst_hom R hn f c d hj
  have hl : (l.precomp e).hom = (postnikovCommonRightViaBSecondZeroPath R hn f c d hj).hom :=
    postnikovCommonRightContourLeftSecond_hom R hn f c d hj
  exact (SquareZero.RelativeWitness.precomp_comp_hom t l e).trans
    ((SquareZero.RelativeWitness.comp_congr_hom_of_paths ht hl).trans
      (postnikovCommonRightZeroAffineViaB_pair_hom R hn f c d hj).symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
