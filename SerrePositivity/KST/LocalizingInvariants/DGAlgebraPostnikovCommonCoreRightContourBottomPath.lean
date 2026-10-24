module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourTargetLeft

/-!
概要：元の W と、元の T′L の端点表示にそろえた既存 affineViaB を取り出す。
方針：証明済みの全経路同定で端点の表示だけを移し、Γ 射影を保持する。
規約：W と affineViaB の全射は不変。使われ方：元の貼合せ比較への実代入。
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

def postnikovCommonRightContourBottomPath := SquareZero.RectangleOfHom.outerTarget
  (postnikovCommonRightClassifyingLayer R hn f c d hj)
  (postnikovCommonRightClassifyingBaseChangeHom R hn f c d hj)
  (postnikovCommonRightClassifyingProjection R hn f c d)
  (postnikovCommonRightClassifyingBaseChangeHom_projection R hn f c d hj)

def postnikovCommonRightContourBottomRefinedPath :=
  ((postnikovCommonRightContourBottomPath R hn f c d hj).precomp
    (postnikovCommonRightToClassifying R hn f c d)).rebase
    (postnikovCommonRightToClassifying_projection R hn f c d)

def postnikovCommonRightViaBContourPath :=
  (postnikovCommonRightContourTargetLeftRefined R hn f c d hj).replaceHom
    (postnikovCommonRightZeroAffineViaB R hn f c d hj).hom
    (postnikovCommonRightContourTargetLeft_hom R hn f c d hj)

def postnikovCommonRightViaBThenBottom :=
  (postnikovCommonRightViaBContourPath R hn f c d hj).comp
    (postnikovCommonRightContourBottomRefinedPath R hn f c d hj)

lemma postnikovCommonRightViaBContourPath_hom :
    (postnikovCommonRightViaBContourPath R hn f c d hj).hom =
      (postnikovCommonRightZeroAffineViaB R hn f c d hj).hom := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
