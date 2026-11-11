module

public import SerrePositivity.AlgebraicGeometry.ReesPolynomialBaseChange

/-!
概要：元の多項式環と、基底 Rees 環上の多項式環との係数変更の両立性。
方針：定数多項式の像を比較し、二つの scalar tower を合成する。
規約：Rees 加群の加群作用は既存の reesPolynomialBaseChange で制限する。
使われ方：P 上の斉次局所化を B[X] 上の斉次局所化と比較するための入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

variable {R ι : Type*} [CommRing R] (I : Ideal R)

/-- P→B[X] の係数変更は、基底環 R からの代数構造と両立する。 -/
theorem reesPolynomialCoefficientAlgebra_scalarTower :
    letI := reesPolynomialCoefficientAlgebra (ι := ι) I
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) := by
  letI := reesPolynomialCoefficientAlgebra (ι := ι) I
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R (reesAlgebra I) r) =
    MvPolynomial.map (algebraMap R (reesAlgebra I)) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]

/-- 制限した B[X] 作用は、P を経由する基底環上の作用と両立する。 -/
theorem reesPolynomialBaseChange_base_scalarTower
    (N : Type*) [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    [Module (reesAlgebra (I.map (algebraMap R (MvPolynomial ι R)))) N]
    [IsScalarTower (MvPolynomial ι R)
      (reesAlgebra (I.map (algebraMap R (MvPolynomial ι R)))) N] :
    letI := reesPolynomialCoefficientAlgebra (ι := ι) I
    letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
    IsScalarTower R (MvPolynomial ι (reesAlgebra I)) N := by
  let P := MvPolynomial ι R
  let Q := MvPolynomial ι (reesAlgebra I)
  letI := reesPolynomialCoefficientAlgebra (ι := ι) I
  letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
  letI : IsScalarTower R P Q := reesPolynomialCoefficientAlgebra_scalarTower I
  letI : IsScalarTower P Q N := reesPolynomialBaseChange_source_scalarTower I N
  apply IsScalarTower.of_algebraMap_smul
  intro r n
  rw [IsScalarTower.algebraMap_apply R P Q r, algebraMap_smul Q, algebraMap_smul P]

end SerrePositivity.AlgebraicGeometry
