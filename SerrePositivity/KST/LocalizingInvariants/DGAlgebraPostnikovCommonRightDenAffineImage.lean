module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenDirectSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathImageWhisker

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenAffineImage
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：分母の正規化 affine 経路を、元の二 ImageWitness の同じ Γ 上の合成へ同定する。
方針：元の係数表示同型の全経路式を、元の Γ と分母零底同型で写す。
規約：二段自然性の選択を変えない。使われ方：元の分母輪郭との厳密照合。
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

def postnikovCommonRightDenImageComposite :=
  PostnikovCommonCore.postnikovCommonRightDenImageComposite
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightDenAffineCommon_image_hom :
    (postnikovCommonRightDenAffineCommonPath R f c d hj).hom ≫
      Path.map R (postnikovCommonRightDenDirectImageIso R f c d hj).hom =
    postnikovCellImageToSecond R (postnikovCommonClassBase R f c d) ≫
      (postnikovCommonRightDenImageComposite R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightDenAffineCommon_image_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightDenAffinePath_image_hom :
    (postnikovCommonRightDenAffinePath R f c d hj).hom =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCommonRightDenImageComposite R f c d hj).hom ≫
        Path.map R (postnikovCommonRightDenCompositeZeroIso R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightDenAffinePath_image_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
