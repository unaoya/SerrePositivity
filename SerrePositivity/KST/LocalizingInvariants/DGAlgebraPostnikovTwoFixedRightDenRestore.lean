module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightOriginalRoof

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDenRestore

/-!
概要：直接分母遷移の元の係数表示を classifying 表示へ同型化し、元の標的へ戻す。
方針：元の二段分母の表示同型を双加群上で合成し、同じ平方零同型を回収する。
規約：直接分母経路の元の係数射を保持。使われ方：輸送後の模型の標的復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def rightDenominatorCoefficientIso : bimoduleRestrict
    (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le)
    (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≅
      d.rightClassifyingLayer R :=
  PostnikovSuccessorClassInverseData.rightDenominatorCoefficientIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightDenominatorCoefficientIso_map :
    (SquareZero.coefficientIso (d.classBase R) (d.rightDenominatorCoefficientIso R)).hom =
      postnikovCommonRightDenDirectToZero R f d.baseInverse d.layerInverse d.target_le :=
  PostnikovSuccessorClassInverseData.rightDenominatorCoefficientIso_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightDenominatorClassRestore :=
  PostnikovSuccessorClassInverseData.rightDenominatorClassRestore
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightDenominatorClassRestore_triangle :
    postnikovCommonRightDenDirectToZero R f d.baseInverse d.layerInverse d.target_le ≫
      d.rightDenominatorClassRestore R = SquareZero.baseChangeMap
        (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) :=
  PostnikovSuccessorClassInverseData.rightDenominatorClassRestore_triangle
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
