module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaBZeroComposition
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourFirstComparison

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightContourTargetPath :=
  let N := postnikovCommonRightClassifyingLayer R f c d hj
  let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
  let p := postnikovCommonRightClassifyingProjection R f c d
  let V := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedCentralRelative R f c d)
  let T := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedTargetRelative R f c d)
  let hTop := postnikovCommonRightClassifyingBaseChangeHom_central R f c d hj
  SquareZero.RectangleOfHom.towardTopSource N H p V hTop T

def postnikovCommonRightContourTargetLeft :=
  (postnikovCommonRightContourTargetPath R f c d hj).comp
    (postnikovCommonRightContourLeftPath R f c d hj)

def postnikovCommonRightContourTargetLeftRefined :=
  ((postnikovCommonRightContourTargetLeft R f c d hj).precomp
    (postnikovCommonRightToClassifying R f c d)).rebase
    (postnikovCommonRightToClassifying_projection R f c d)

/-- 元の輪郭の T′L は元の Γ 源上の affineViaB と全乗法的経路として厳密に一致。 -/
lemma postnikovCommonRightContourTargetLeft_hom :
    (postnikovCommonRightContourTargetLeftRefined R f c d hj).hom =
      (postnikovCommonRightZeroAffineViaB R f c d hj).hom := by
  let t := postnikovCommonRightContourTargetPath R f c d hj
  let l := postnikovCommonRightContourLeftPath R f c d hj
  let e := postnikovCommonRightToClassifying R f c d
  have ht : (t.precomp e).hom = (postnikovCommonRightViaBFirstZeroPath R f c d hj).hom :=
    postnikovCommonRightContourFirst_hom R f c d hj
  have hl : (l.precomp e).hom = (postnikovCommonRightViaBSecondZeroPath R f c d hj).hom :=
    postnikovCommonRightContourLeftSecond_hom R f c d hj
  exact (SquareZero.RelativeWitness.precomp_comp_hom t l e).trans
    ((SquareZero.RelativeWitness.comp_congr_hom_of_paths ht hl).trans
      (postnikovCommonRightZeroAffineViaB_pair_hom R f c d hj).symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
