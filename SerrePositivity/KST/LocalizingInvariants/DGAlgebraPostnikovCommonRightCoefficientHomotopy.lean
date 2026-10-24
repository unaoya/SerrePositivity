module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassGlue
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientHomotopy

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCoefficientHomotopy
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：貼り合わせた元の右 class 経路から、係数逆候補の右像の鎖ホモトピーを回収する。
方針：元の二 class と cell 比較射を保持し、実係数射への一般回収補題を適用する。
規約：元の class 整合を追加入力しない。使われ方：後続段での係数障害消去。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

abbrev postnikovCommonGlueClassTarget :=
  PostnikovCommonCore.postnikovCommonGlueClassTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

abbrev postnikovCommonGlueClassSource :=
  PostnikovCommonCore.postnikovCommonGlueClassSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

/-- 元の層の係数射の右像は、追加の経路仮定なしに実際に鎖ホモトピック。 -/
def postnikovCommonRightCoefficientHomotopy : Homotopy
    (((postnikovCommonGlueClassTarget R f c d).hom ≫ biprod.snd) ≫
      (postnikovCommonRightShiftedNumeratorMap R f c d 1).hom)
    (((postnikovCommonGlueClassSource R f c d).hom ≫ biprod.snd) ≫
      (postnikovCommonRightShiftedNumeratorMap R f c d 1).hom) :=
  PostnikovCommonCore.postnikovCommonRightCoefficientHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
