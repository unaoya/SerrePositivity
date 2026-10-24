module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenAffineImage
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeFollowingTransfer
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueNaturality

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenAffineContour
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：二段分母 affine 経路を、元の分母輪郭の全経路そのものへ同定する。
方針：同じ二 ImageWitness の底付き移送・前合成の合成保存を使う。
規約：元の第一辺・第二辺・輪郭の全射を保持。使われ方：直接遷移の比較との接続。
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

lemma postnikovCommonRightDenAffinePath_pair_hom :
    (postnikovCommonRightDenAffinePath R f c d hj).hom =
      (postnikovCommonRightDenZeroComposite R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightDenAffinePath_pair_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightDenAffinePath_contour_hom :
    (postnikovCommonRightDenAffinePath R f c d hj).hom =
      (postnikovCommonRightDenContourPath R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightDenAffinePath_contour_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
