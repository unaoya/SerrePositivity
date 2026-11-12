module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
概要：閉厚化 M/JM を、商環 R/J とその多項式環の加群として扱う。
方針：J と拡大イデアルの消滅を使い、商多項式環の既存の同型で作用を移す。
規約：加群の型と元の R 作用は変えず、追加の作用だけを局所的に設定する。
使われ方：閉厚化の標準開 Čech 比較を、商環上の係数表示へ接続する。
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

/-- J は実際の閉厚化 M/JM を消す。 -/
theorem reesClosedCoefficient_torsion : Module.IsTorsionBySet R
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) J := by
  apply (Module.isTorsionBySet_quotient_iff _ _).mpr
  intro m r hr
  change r • m ∈ (((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
    (⊤ : Submodule (MvPolynomial ι R) M)).restrictScalars R)
  rw [reesExtendedAdic_restrictScalars, pow_one]
  exact Submodule.smul_mem_smul hr (Submodule.mem_top)

/-- 閉厚化の商環 R/J 上の係数加群構造。 -/
@[instance_reducible]
def reesClosedCoefficientModule :
    Module (R ⧸ J) (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  (reesClosedCoefficient_torsion (ι := ι) (M := M) J).module

local instance : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J

/-- 商環の代表による作用は元の R 作用に一致する。 -/
theorem reesClosedCoefficient_mk_smul (r : R)
    (x : reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :
    Ideal.Quotient.mk J r • x = r • x := rfl

/-- 係数制限は元の R 加群構造を回復する。 -/
theorem reesClosedCoefficient_scalarTower : IsScalarTower R (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  IsScalarTower.of_algebraMap_smul (reesClosedCoefficient_mk_smul (ι := ι) J)

/-- 拡大イデアルも、閉厚化の元の多項式加群構造を消す。 -/
theorem reesClosedPolynomialCoefficient_torsion : Module.IsTorsionBySet (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1)
    (J.map (algebraMap R (MvPolynomial ι R))) := by
  change Module.IsTorsionBySet (MvPolynomial ι R)
    (M ⧸ ((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
      (⊤ : Submodule (MvPolynomial ι R) M))) _
  apply (Module.isTorsionBySet_quotient_iff
    ((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
      (⊤ : Submodule (MvPolynomial ι R) M)) _).mpr
  intro m p hp
  rw [pow_one]
  exact Submodule.smul_mem_smul hp (Submodule.mem_top)

/-- 閉厚化の (R/J)[X] 上の係数加群構造。 -/
@[instance_reducible]
def reesClosedPolynomialCoefficientModule : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) := by
  letI : Module (MvPolynomial ι R ⧸ J.map (MvPolynomial.C : R →+* MvPolynomial ι R))
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
    (reesClosedPolynomialCoefficient_torsion (ι := ι) (M := M) J).module
  exact Module.compHom _ (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) J).toRingHom

local instance : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J

/-- 多項式の係数を商へ写してから作用させても、元の作用と同じ。 -/
theorem reesClosedPolynomialCoefficient_map_smul (p : MvPolynomial ι R)
    (x : reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :
    MvPolynomial.map (Ideal.Quotient.mk J) p • x = p • x := by
  have he : (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) J)
      (MvPolynomial.map (Ideal.Quotient.mk J) p) =
      Ideal.Quotient.mk (J.map (MvPolynomial.C : R →+* MvPolynomial ι R)) p := by
    induction p using MvPolynomial.induction_on with
    | C r =>
      simp [MvPolynomial.quotientEquivQuotientMvPolynomial]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.map_X, hp]
      congr 1
      simp [MvPolynomial.quotientEquivQuotientMvPolynomial]
  letI : Module (MvPolynomial ι R ⧸ J.map (MvPolynomial.C : R →+* MvPolynomial ι R))
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
    (reesClosedPolynomialCoefficient_torsion (ι := ι) (M := M) J).module
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) J)
    (MvPolynomial.map (Ideal.Quotient.mk J) p) • x = p • x
  rw [he]
  rfl

end SerrePositivity.AlgebraicGeometry
