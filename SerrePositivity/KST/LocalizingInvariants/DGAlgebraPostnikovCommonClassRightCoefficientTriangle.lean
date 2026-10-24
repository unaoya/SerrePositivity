module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassRightCoefficients
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassCompatibilityTriangles

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRightCoefficientTriangle
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fixed class 係数射の後に fⱼ を作用させると、元の直接 B 遷移の係数射になる。
方針：元の複体の射の厳密な三角形を、同じ P 上の双加群射の等式へ移す。
規約：ホモロジーだけの三角形で代用しない。使われ方：元の fixed 模型射の右合成。
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

lemma postnikovCommonClassRightCoefficient_triangle :
    postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj) ≫
      postnikovCommonClassRightTargetCoefficient R f c d hj =
    postnikovCommonClassRightDenominatorCoefficient R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassRightCoefficient_triangle
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
