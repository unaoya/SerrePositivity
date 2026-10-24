module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassAffineRight

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRight
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：新しい class 互換性を fⱼ で移した経路を、元の B 遷移と指定右貼合せで計算する。
方針：同じ係数逆の厳密な右三角形と底変更射影を使う。
規約：全経路の実射の式を保つ。使われ方：組み直した Γ の右三角形。
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

lemma postnikovCommonClassFixedTransition_zero :
    (postnikovCommonClassFixedTransitionWitness R f c d e).hom ≫
      Path.map R (postnikovCommonClassTransitionToZero R f c d hj) =
    (postnikovCommonClassFixedRetractWitness R f c d e).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedTransition_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedTransition_zero_right :
    (postnikovCommonClassFixedTransitionWitness R f c d e).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom) =
    (postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫ Path.map R
      (postnikovCommonRightClassToZero R f c d ≫
        postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonClassFixedTransition_zero_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedCompatibility_linear :
    (postnikovCommonClassFixedCompatibility R f c d e).hom.hom =
    (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫ Path.diagonal R _).hom -
      (postnikovCommonClassFixedTransitionWitness R f c d e).hom.hom +
      (postnikovCommonClassStandardWitness R f c d hj).hom.hom :=
  PostnikovCommonCore.postnikovCommonClassFixedCompatibility_linear
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedCompatibility_zero_right :
    ((postnikovCommonClassFixedCompatibility R f c d e).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom)).hom =
    (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom) ≫
      Path.diagonal R (postnikovZeroClassTarget R (B.obj j).obj 1 1)).hom -
    ((postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫ Path.map R
      (postnikovCommonRightClassToZero R f c d ≫
        postnikovZeroClassMap R 1 1 (B.transition hj).hom)).hom +
    ((postnikovCommonClassStandardWitness R f c d hj).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom)).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedCompatibility_zero_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
