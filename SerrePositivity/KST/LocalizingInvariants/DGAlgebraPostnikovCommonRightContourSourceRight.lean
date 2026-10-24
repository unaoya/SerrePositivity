module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourRightComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativePathCompositionCongr
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRectangleTopGlue

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourSourceRight
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

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
  PostnikovCommonCore.postnikovCommonRightContourSourcePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightContourSourceRight :=
  PostnikovCommonCore.postnikovCommonRightContourSourceRight
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightContourSourceRightRefined :=
  PostnikovCommonCore.postnikovCommonRightContourSourceRightRefined
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightDenZeroComposite :=
  PostnikovCommonCore.postnikovCommonRightDenZeroComposite
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 元の分母境界 S′R は指定した二自然性の零底 affine 合成と全経路で厳密に一致。 -/
lemma postnikovCommonRightContourSourceRight_hom :
    (postnikovCommonRightContourSourceRightRefined R f c d hj).hom =
      (postnikovCommonRightDenZeroComposite R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightContourSourceRight_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
