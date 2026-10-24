module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedBaseNormalization
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenDirectData

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRightCoefficientBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fⱼ と直接 B 遷移の係数射を、元の P 上の classifying 係数へ移す底射を固定する。
方針：切断の自然性と塔の厳密合成式で、両射の零底を同じ元の底射へ同定する。
規約：P 全体上の等式を保持。使われ方：fixed 模型射の右係数三角形。
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

def postnikovCommonClassRightImageBase :=
  PostnikovCommonCore.postnikovCommonClassRightImageBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassRightImageBase_zero :
    postnikovCommonClassRightImageBase R f c d hj ≫
      postnikovTransition R (B.obj j).obj 1 0 (by omega) =
    postnikovCommonRightClassifyingBase R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassRightImageBase_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassRightDenominatorBase :=
  PostnikovCommonCore.postnikovCommonClassRightDenominatorBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassRightDenominatorBase_zero :
    postnikovCommonClassRightDenominatorBase R f c d hj ≫
      postnikovTransition R (B.obj j).obj 1 0 (by omega) =
    postnikovCommonRightClassifyingBase R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassRightDenominatorBase_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
