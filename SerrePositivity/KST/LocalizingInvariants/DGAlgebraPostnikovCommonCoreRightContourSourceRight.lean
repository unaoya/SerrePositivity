module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourRightComparison
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightContourSourcePath :=
  let N := postnikovCommonRightClassifyingLayer R hn f c d hj
  let H := postnikovCommonRightClassifyingBaseChangeHom R hn f c d hj
  let p := postnikovCommonRightClassifyingProjection R hn f c d
  let V := postnikovCommonRightTransitionLift R hn f c d hj
    (postnikovCommonRightFixedCentralRelative R hn f c d)
  let S := postnikovCommonRightTransitionLift R hn f c d hj
    (postnikovCommonRightFixedSourceRelative R hn f c d)
  let hTop := postnikovCommonRightClassifyingBaseChangeHom_central R hn f c d hj
  SquareZero.RectangleOfHom.towardTopTarget N H p V hTop S

def postnikovCommonRightContourSourceRight :=
  (postnikovCommonRightContourSourcePath R hn f c d hj).comp
    (postnikovCommonRightContourRightPath R hn f c d hj)

def postnikovCommonRightContourSourceRightRefined :=
  ((postnikovCommonRightContourSourceRight R hn f c d hj).precomp
    (postnikovCommonRightToClassifying R hn f c d)).rebase
    (postnikovCommonRightToClassifying_projection R hn f c d)

def postnikovCommonRightDenZeroComposite :=
  (postnikovCommonRightDenFirstZeroPath R hn f c d hj).comp
    (postnikovCommonRightDenSecondZeroPath R hn f c d hj)

/-- 元の分母境界 S′R は指定した二自然性の零底 affine 合成と全経路で厳密に一致。 -/
lemma postnikovCommonRightContourSourceRight_hom :
    (postnikovCommonRightContourSourceRightRefined R hn f c d hj).hom =
      (postnikovCommonRightDenZeroComposite R hn f c d hj).hom := by
  let s := postnikovCommonRightContourSourcePath R hn f c d hj
  let r := postnikovCommonRightContourRightPath R hn f c d hj
  let e := postnikovCommonRightToClassifying R hn f c d
  have hs : (s.precomp e).hom = (postnikovCommonRightDenFirstZeroPath R hn f c d hj).hom :=
    postnikovCommonRightSourceFirst_hom R hn f c d hj
  have hr : (r.precomp e).hom = (postnikovCommonRightDenSecondZeroPath R hn f c d hj).hom :=
    postnikovCommonRightContourRightSecond_hom R hn f c d hj
  exact (SquareZero.RelativeWitness.precomp_comp_hom s r e).trans
    (SquareZero.RelativeWitness.comp_congr_hom_of_paths hs hr)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
