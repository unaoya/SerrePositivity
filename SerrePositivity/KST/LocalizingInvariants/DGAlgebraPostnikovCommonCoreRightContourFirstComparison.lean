module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightTargetFirstComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueContour

/-!
概要：貼合せ輪郭の元の T′ を、同じ Γ 源上の零底 affine 第一経路へ同定する。
方針：T′ の端点移送が全射を変更しないことと、元の T の全経路同定を使う。
規約：元の classifying 正方形と全 Γ 射影を保持。使われ方：残る L・W の境界の同定。
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

/-- 元の T′ の全経路の射そのものを、指定した affine 第一辺へ同定する。 -/
lemma postnikovCommonRightContourFirst_hom :
    let N := postnikovCommonRightClassifyingLayer R hn f c d hj
    let H := postnikovCommonRightClassifyingBaseChangeHom R hn f c d hj
    let p := postnikovCommonRightClassifyingProjection R hn f c d
    let V := postnikovCommonRightTransitionLift R hn f c d hj
      (postnikovCommonRightFixedCentralRelative R hn f c d)
    let T := postnikovCommonRightTransitionLift R hn f c d hj
      (postnikovCommonRightFixedTargetRelative R hn f c d)
    let hTop := postnikovCommonRightClassifyingBaseChangeHom_central R hn f c d hj
    let T' := SquareZero.RectangleOfHom.towardTopSource N H p V hTop T
    postnikovCommonRightToClassifying R hn f c d ≫ T'.hom =
      (postnikovCommonRightViaBFirstZeroPath R hn f c d hj).hom := by
  exact postnikovCommonRightTargetFirst_hom R hn f c d hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
