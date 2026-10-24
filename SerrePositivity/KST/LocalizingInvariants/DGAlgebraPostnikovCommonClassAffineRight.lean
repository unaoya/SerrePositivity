module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassAffine

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassAffineRight
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：native class 遷移経路を零底へ戻し、fⱼ で後合成した実経路を計算する。
方針：底変更経路の元の射影と、同じ零層逆の厳密な右三角形を使う。
規約：ホモロジーの式でなく Path への元の代数射の一致。使われ方：Γ の右三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassTransitionIso_inv_zero :
    (postnikovCommonClassTransitionIso R f c d hj).inv ≫
      postnikovCommonClassTransitionToZero R f c d hj =
    SquareZero.baseChangeMap (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
      postnikovTransition R (A.obj j).obj 1 0 (by omega))
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj 1) 1) :=
  PostnikovCommonCore.postnikovCommonClassTransitionIso_inv_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassTransitionWitness_zero :
    (postnikovCommonClassTransitionWitness R f c d e).hom ≫
      Path.map R (postnikovCommonClassTransitionToZero R f c d hj) =
        (postnikovCommonClassRetractWitness R f c d e).hom :=
  PostnikovCommonCore.postnikovCommonClassTransitionWitness_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonRightRetract_right : postnikovCommonRightRetract R f c d e ≫
    postnikovZeroClassMap R 1 1 (f.app j).hom = postnikovCommonRightClassToZero R f c d ≫
      postnikovZeroClassMap R 1 1 (B.transition hj).hom :=
  PostnikovCommonCore.postnikovCommonRightRetract_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassTransitionWitness_zero_right :
    (postnikovCommonClassTransitionWitness R f c d e).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom) =
    (postnikovCommonRightClassGlueWitness R f c d).hom ≫ Path.map R
      (postnikovCommonRightClassToZero R f c d ≫
        postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonClassTransitionWitness_zero_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassAffineRelative_zero_right_hom :
    ((postnikovCommonClassAffineRelative R f c d e).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom)).hom =
    (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom) ≫
      Path.diagonal R (postnikovZeroClassTarget R (B.obj j).obj 1 1)).hom -
    ((postnikovCommonRightClassGlueWitness R f c d).hom ≫ Path.map R
      (postnikovCommonRightClassToZero R f c d ≫
        postnikovZeroClassMap R 1 1 (B.transition hj).hom)).hom +
    ((postnikovCommonClassStandardWitness R f c d hj).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom)).hom :=
  PostnikovCommonCore.postnikovCommonClassAffineRelative_zero_right_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
