module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaBZeroComposition
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourFirstComparison

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourTargetLeft
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

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
  PostnikovCommonCore.postnikovCommonRightContourTargetPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightContourTargetLeft :=
  PostnikovCommonCore.postnikovCommonRightContourTargetLeft
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightContourTargetLeftRefined :=
  PostnikovCommonCore.postnikovCommonRightContourTargetLeftRefined
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 元の輪郭の T′L は元の Γ 源上の affineViaB と全乗法的経路として厳密に一致。 -/
lemma postnikovCommonRightContourTargetLeft_hom :
    (postnikovCommonRightContourTargetLeftRefined R f c d hj).hom =
      (postnikovCommonRightZeroAffineViaB R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightContourTargetLeft_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
