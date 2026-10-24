module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightTargetFirstComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueContour

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourFirstComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

/-- 元の T′ の全経路の射そのものを、指定した affine 第一辺へ同定する。 -/
lemma postnikovCommonRightContourFirst_hom :
    let N := postnikovCommonRightClassifyingLayer R f c d hj
    let H := postnikovCommonRightClassifyingBaseChangeHom R f c d hj
    let p := postnikovCommonRightClassifyingProjection R f c d
    let V := postnikovCommonRightTransitionLift R f c d hj
      (postnikovCommonRightFixedCentralRelative R f c d)
    let T := postnikovCommonRightTransitionLift R f c d hj
      (postnikovCommonRightFixedTargetRelative R f c d)
    let hTop := postnikovCommonRightClassifyingBaseChangeHom_central R f c d hj
    let T' := SquareZero.RectangleOfHom.towardTopSource N H p V hTop T
    postnikovCommonRightToClassifying R f c d ≫ T'.hom =
      (postnikovCommonRightViaBFirstZeroPath R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightContourFirst_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
