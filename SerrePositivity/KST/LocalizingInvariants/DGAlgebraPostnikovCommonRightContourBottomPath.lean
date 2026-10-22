module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourTargetLeft

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightContourBottomPath := SquareZero.RectangleOfHom.outerTarget
  (postnikovCommonRightClassifyingLayer R f c d hj)
  (postnikovCommonRightClassifyingBaseChangeHom R f c d hj)
  (postnikovCommonRightClassifyingProjection R f c d)
  (postnikovCommonRightClassifyingBaseChangeHom_projection R f c d hj)

def postnikovCommonRightContourBottomRefinedPath :=
  ((postnikovCommonRightContourBottomPath R f c d hj).precomp
    (postnikovCommonRightToClassifying R f c d)).rebase
    (postnikovCommonRightToClassifying_projection R f c d)

def postnikovCommonRightViaBContourPath :=
  (postnikovCommonRightContourTargetLeftRefined R f c d hj).replaceHom
    (postnikovCommonRightZeroAffineViaB R f c d hj).hom
    (postnikovCommonRightContourTargetLeft_hom R f c d hj)

def postnikovCommonRightViaBThenBottom :=
  (postnikovCommonRightViaBContourPath R f c d hj).comp
    (postnikovCommonRightContourBottomRefinedPath R f c d hj)

lemma postnikovCommonRightViaBContourPath_hom :
    (postnikovCommonRightViaBContourPath R f c d hj).hom =
      (postnikovCommonRightZeroAffineViaB R f c d hj).hom := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
