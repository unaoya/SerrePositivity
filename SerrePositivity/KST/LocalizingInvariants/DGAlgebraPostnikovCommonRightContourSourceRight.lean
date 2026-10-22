module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourRightComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativePathCompositionCongr
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRectangleTopGlue

/-!
概要：元の輪郭の S′R を、分母の二つの指定 ImageWitness の零底 affine 合成へ同定する。
方針：S′ は元の S と同じ射、R は target trace からの同定を使い、合成の全射を保つ。
規約：同じ Γ 源・射影・係数。使われ方：元の G の分母側の境界を接続する。
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

def postnikovCommonRightContourSourcePath :=
  let N := postnikovCommonRightClassifyingLayer R f c d hj
  let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
  let p := postnikovCommonRightClassifyingProjection R f c d
  let V := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedCentralRelative R f c d)
  let S := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedSourceRelative R f c d)
  let hTop := postnikovCommonRightClassifyingBaseChangeHom_central R f c d hj
  SquareZero.RectangleOfHom.towardTopTarget N H p V hTop S

def postnikovCommonRightContourSourceRight :=
  (postnikovCommonRightContourSourcePath R f c d hj).comp
    (postnikovCommonRightContourRightPath R f c d hj)

def postnikovCommonRightContourSourceRightRefined :=
  ((postnikovCommonRightContourSourceRight R f c d hj).precomp
    (postnikovCommonRightToClassifying R f c d)).rebase
    (postnikovCommonRightToClassifying_projection R f c d)

def postnikovCommonRightDenZeroComposite :=
  (postnikovCommonRightDenFirstZeroPath R f c d hj).comp
    (postnikovCommonRightDenSecondZeroPath R f c d hj)

/-- 元の分母境界 S′R は指定した二自然性の零底 affine 合成と全経路で厳密に一致。 -/
lemma postnikovCommonRightContourSourceRight_hom :
    (postnikovCommonRightContourSourceRightRefined R f c d hj).hom =
      (postnikovCommonRightDenZeroComposite R f c d hj).hom := by
  let s := postnikovCommonRightContourSourcePath R f c d hj
  let r := postnikovCommonRightContourRightPath R f c d hj
  let e := postnikovCommonRightToClassifying R f c d
  have hs : (s.precomp e).hom = (postnikovCommonRightDenFirstZeroPath R f c d hj).hom :=
    postnikovCommonRightSourceFirst_hom R f c d hj
  have hr : (r.precomp e).hom = (postnikovCommonRightDenSecondZeroPath R f c d hj).hom :=
    postnikovCommonRightContourRightSecond_hom R f c d hj
  exact (SquareZero.RelativeWitness.precomp_comp_hom s r e).trans
    (SquareZero.RelativeWitness.comp_congr_hom_of_paths hs hr)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
