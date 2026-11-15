module

public import SerrePositivity.AlgebraicGeometry.PolynomialGradeZeroEquiv
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.FiniteType

/-!
概要：有限変数の多項式環の Proj の固有な構造射を、元の係数環の Spec 上へ移す。
方針：次数零成分上の有限型性を合成から得て、係数の環同型で標的を戻す。
規約：Proj の既存の固有性を用い、係数環の Noether 性は要求しない。
使われ方：C05 の有限型 affine の固有な周辺スキーム。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) (ι : Type u) [CommRing R]

/-- 有限変数の多項式環は、その次数零成分上でも有限型。 -/
theorem polynomial_finiteType_gradeZero [Finite ι] :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι R 0) (MvPolynomial ι R) := by
  have hc : (algebraMap (MvPolynomial.homogeneousSubmodule ι R 0) (MvPolynomial ι R)).comp
      (polynomialGradeZeroMap R ι) = algebraMap R (MvPolynomial ι R) := by
    ext r
    rfl
  have hf : ((algebraMap (MvPolynomial.homogeneousSubmodule ι R 0) (MvPolynomial ι R)).comp
      (polynomialGradeZeroMap R ι)).FiniteType := by
    rw [hc]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType hf)

/-- 次数零成分の係数の同型を使って元の Spec R へ戻した Proj の構造射。 -/
def polynomialProjToSpec : Proj (MvPolynomial.homogeneousSubmodule ι R) ⟶
    Spec (CommRingCat.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (polynomialGradeZeroMap R ι))

/-- 有限変数の多項式環の Proj は、元の係数環の Spec 上で固有。 -/
theorem isProper_polynomialProjToSpec [Finite ι] : IsProper (polynomialProjToSpec R ι) := by
  letI : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι R 0) (MvPolynomial ι R) :=
    polynomial_finiteType_gradeZero R ι
  haveI : IsIso (CommRingCat.ofHom (polynomialGradeZeroMap R ι)) :=
    inferInstanceAs (IsIso (polynomialGradeZeroEquiv R ι).toCommRingCatIso.hom)
  dsimp [polynomialProjToSpec]
  infer_instance

end SerrePositivity.AlgebraicGeometry
