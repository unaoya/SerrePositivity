module

public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModel
public import SerrePositivity.AlgebraicGeometry.DegreeOnePolynomialAction

/-!
概要：実際の次数一表示の証人から、射影 Čech の係数構造と被覆条件を同時に得る。
方針：同じ全射評価に係数移送の一般の法則を適用する。
規約：元の R 作用を保ち、有限性を追加仮定にしない。
使われ方：有限ファイバー冪の同じ表示を 2f の四角形の入力へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- 表示の同じ評価から、2f の係数構造・有限性・被覆条件を供給する。 -/
theorem DegreeOneProjectiveModel.projectiveCechData {R : Type u} [CommRing R]
    {Y : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of R)} (m : DegreeOneProjectiveModel f) :
    letI := degreeOnePolynomialAlgebra (R := R) m.generator
    IsScalarTower R (MvPolynomial m.index R) m.ring ∧
      SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule m.index R) m.grade ∧
      Module.Finite (MvPolynomial m.index R) m.ring ∧
      (HomogeneousIdeal.irrelevant m.grade).toIdeal ≤ Ideal.span
        (Set.range (fun i : m.index ↦
          algebraMap (MvPolynomial m.index R) m.ring (MvPolynomial.X i))) :=
  degreeOne_projective_cech_data m.grade m.generator m.homogeneous m.surjective

end SerrePositivity.AlgebraicGeometry
