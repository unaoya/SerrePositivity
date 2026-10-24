module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonShiftedCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftFromRestriction

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightShiftedCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の細分 roof 底上の右係数比較を、class の shift 係数へ移す。
方針：元の分子・分母の shift 制限から、同じ右標的の shift へ実射を作る。
規約：元の右 cochain 三角形を保持。使われ方：実平方零 class 標的の可換式。
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
  (d : PostnikovCommonLayerInverse R f c) (s : ℤ)

def postnikovCommonRightShiftedNumeratorMap :
    postnikovOneRoofShiftedNumeratorLayer R f (postnikovOneRoofRefine R f c d.zero.source_le) s ⟶
      DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) s :=
  PostnikovCommonCore.postnikovCommonRightShiftedNumeratorMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

lemma postnikovCommonRightShiftedNumeratorMap_hom :
    (postnikovCommonRightShiftedNumeratorMap R f c d s).hom =
      (postnikovLayerMap R (f.app i).hom 1)⟦s⟧' :=
  PostnikovCommonCore.postnikovCommonRightShiftedNumeratorMap_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

def postnikovCommonRightShiftedDenominatorMap :
    postnikovOneRoofShiftedDenominatorLayer R f (postnikovOneRoofRefine R f c d.zero.source_le) s ⟶
      DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) s :=
  PostnikovCommonCore.postnikovCommonRightShiftedDenominatorMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

lemma postnikovCommonRightShiftedDenominatorMap_hom :
    (postnikovCommonRightShiftedDenominatorMap R f c d s).hom =
      (postnikovLayerMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 1)⟦s⟧' :=
  PostnikovCommonCore.postnikovCommonRightShiftedDenominatorMap_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

lemma postnikovCommonRightShifted_coefficient : postnikovCommonShiftedCoefficientMap R f c d s ≫
    postnikovCommonRightShiftedNumeratorMap R f c d s =
      postnikovCommonRightShiftedDenominatorMap R f c d s :=
  PostnikovCommonCore.postnikovCommonRightShifted_coefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
