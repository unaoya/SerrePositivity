module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedClassGlue

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedGlueZeroMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fixed native 貼合せの全経路を、元の零底 affine 貼合せへ厳密に戻す。
方針：元の底変更同型の逆の射影式と、底変更経路の全射影を使う。
規約：native class 経路の全射を保持。使われ方：fixed Γ の右 class 像との接続。
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
  (d : PostnikovCommonLayerInverse R f c)

lemma postnikovCommonRightZeroBaseIso_inv_map :
    (postnikovCommonRightZeroBaseIso R f c d).inv ≫
      postnikovCommonRightClassToZero R f c d =
    SquareZero.baseChangeMap (postnikovCommonRightZeroBase R f c d)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1) :=
  PostnikovCommonCore.postnikovCommonRightZeroBaseIso_inv_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightFixedClassGlueWitness_zero :
    (postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫
      Path.map R (postnikovCommonRightClassToZero R f c d) =
    (postnikovCommonRightFixedZeroGlueWitness R f c d).hom :=
  PostnikovCommonCore.postnikovCommonRightFixedClassGlueWitness_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
