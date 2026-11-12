module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientModule

/-!
概要：閉厚化の四つの係数環の作用の両立性をそろえる。
方針：商環の代表と、多項式係数変更の作用の計算式を使う。
規約：多項式間の代数構造は係数の商写像から定める。
使われ方：商環上の標準開図式を R へ係数制限する比較への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (J : Ideal R)

local instance : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) J 1
local instance : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) J 1
local instance : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J
local instance : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J
local instance : Algebra (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J)) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).toAlgebra

/-- 多項式環の係数変更に関する作用の塔。 -/
theorem reesClosedPolynomialCoefficient_scalarTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J))
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  IsScalarTower.of_algebraMap_smul (reesClosedPolynomialCoefficient_map_smul (ι := ι) J)

/-- 元の基底から商係数の多項式環への作用の塔。 -/
theorem reesClosedPolynomialCoefficient_base_scalarTower :
    IsScalarTower R (MvPolynomial ι (R ⧸ J))
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change MvPolynomial.C (Ideal.Quotient.mk J r) • x = r • x
  rw [← MvPolynomial.map_C (Ideal.Quotient.mk J),
    reesClosedPolynomialCoefficient_map_smul]
  exact algebraMap_smul (MvPolynomial ι R) r x

/-- 商基底から商係数の多項式環への作用の塔。 -/
theorem reesClosedPolynomialCoefficient_quotient_scalarTower :
    IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) := by
  apply IsScalarTower.of_algebraMap_smul
  intro b x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  change MvPolynomial.C (Ideal.Quotient.mk J r) • x = Ideal.Quotient.mk J r • x
  rw [reesClosedCoefficient_mk_smul, ← MvPolynomial.map_C (Ideal.Quotient.mk J),
    reesClosedPolynomialCoefficient_map_smul]
  exact algebraMap_smul (MvPolynomial ι R) r x

end SerrePositivity.AlgebraicGeometry
