module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassRightCoefficientBase

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRightCoefficients
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fⱼ と直接 B 遷移の実係数射を、元の P 上の同じ classifying 双加群へ構成する。
方針：元の層射を零底係数へ移し、底射の厳密な等式で係数表示を揃える。
規約：実双加群射と元の underlying 層射を保持。使われ方：fixed 模型射の右係数三角形。
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

def postnikovCommonClassRightTargetCoefficient :
    postnikovCommonClassTransitionLayer R f c d hj ⟶
      postnikovCommonRightClassifyingLayer R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassRightTargetCoefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassRightDenominatorCoefficient :
    postnikovOneRoofShiftedDenominatorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1 ⟶
      postnikovCommonRightClassifyingLayer R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassRightDenominatorCoefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassRightTargetCoefficient_hom :
    (postnikovCommonClassRightTargetCoefficient R f c d hj).hom =
      (postnikovLayerMap R (f.app j).hom 1)⟦(1 : ℤ)⟧' :=
  PostnikovCommonCore.postnikovCommonClassRightTargetCoefficient_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassRightDenominatorCoefficient_hom :
    (postnikovCommonClassRightDenominatorCoefficient R f c d hj).hom =
      (postnikovLayerMap R (postnikovCommonRightDenDirectMap R f c d hj) 1)⟦(1 : ℤ)⟧' :=
  PostnikovCommonCore.postnikovCommonClassRightDenominatorCoefficient_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
