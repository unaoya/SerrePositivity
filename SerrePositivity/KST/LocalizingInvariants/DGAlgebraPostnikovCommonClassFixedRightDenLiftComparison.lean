module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightLiftProjection
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeHomProjections

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightDenLiftComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：P 上へ戻した native 分母経路を、元の分母自然性の全経路そのものへ同定する。
方針：元の P 射影と零 class 像の両一致から、経路 pullback の一意性を使う。
規約：端点・低次射影の一致で代用しない。使われ方：元の分母と native 右模型の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassFixedRightDenominator_zero_hom :
    (postnikovCommonClassFixedRightDenominatorPath R f c d hj e).hom =
    (postnikovCommonRightDenContourPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) :=
  PostnikovCommonCore.postnikovCommonClassFixedRightDenominator_zero_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedRightDenominatorLift_hom :
    (postnikovCommonClassFixedRightDenominatorLift R f c d hj e).hom =
      (postnikovCommonRightDenContourPath R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedRightDenominatorLift_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
