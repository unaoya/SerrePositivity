module

public import SerrePositivity.AlgebraicGeometry.SurjectiveCoefficientQuotient
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotientTransition
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
概要：全射な係数変更の下で、実際の I 進閉厚化に変更後の係数作用を入れる。
方針：拡大イデアルの冪の部分加群を変更後の多項式環へ降ろし、同じ商を使う。
規約：I は元の基底環のイデアルのままとし、商の型も変えない。
使われ方：R/J を固定した閉厚化の係数比較と I 進遷移。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type}
local instance reesCoefficientAdicPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance reesCoefficientAdicPolynomialTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R B r) =
    MvPolynomial.map (algebraMap R B) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]

variable {M : Type u} [AddCommGroup M] [Module R M] [Module B M]
variable [Module (MvPolynomial ι R) M] [Module (MvPolynomial ι B) M]
variable [IsScalarTower R B M] [IsScalarTower R (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι B) M] [IsScalarTower B (MvPolynomial ι B) M]
variable [IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) M]
variable [Fact (Function.Surjective (algebraMap R B))]
variable (I : Ideal R)

/-- 全射な基底係数変更は、多項式環の係数変更も全射にする。 -/
theorem reesCoefficientAdicPolynomial_surjective :
    Function.Surjective (algebraMap (MvPolynomial ι R) (MvPolynomial ι B)) :=
  MvPolynomial.map_surjective (algebraMap R B) Fact.out

/-- 実際の IⁿM を、変更後の多項式環上の部分加群として表す。 -/
def reesCoefficientAdicSubmodule (n : ℕ) : Submodule (MvPolynomial ι B) M :=
  surjectiveCoefficientSubmodule (reesCoefficientAdicPolynomial_surjective (R := R) (B := B) (ι := ι))
    ((I.map (algebraMap R (MvPolynomial ι R))) ^ n • ⊤)

/-- 変更後の係数環で表した IⁿM は、I の拡大冪の作用そのものである。 -/
theorem reesCoefficientAdicSubmodule_eq (n : ℕ) :
    reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n =
      (I.map (algebraMap R (MvPolynomial ι B))) ^ n •
        (⊤ : Submodule (MvPolynomial ι B) M) := by
  apply Submodule.restrictScalars_injective R
  change (((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
    (⊤ : Submodule (MvPolynomial ι R) M)).restrictScalars R) = _
  rw [reesExtendedAdic_restrictScalars, reesExtendedAdic_restrictScalars]

/-- 同じ部分加群は、変更後の基底のイデアル I B の冪による作用でもある。 -/
theorem reesCoefficientAdicSubmodule_eq_mappedIdeal (n : ℕ) :
    reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n =
      ((I.map (algebraMap R B)).map (algebraMap B (MvPolynomial ι B))) ^ n •
        (⊤ : Submodule (MvPolynomial ι B) M) := by
  rw [reesCoefficientAdicSubmodule_eq, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq R B (MvPolynomial ι B)]

/-- 同じ I 進商の、変更後の多項式環上の加群構造。 -/
@[instance_reducible]
def reesCoefficientAdicQuotientPolynomialModule (n : ℕ) :
    Module (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  inferInstanceAs (Module (MvPolynomial ι B) (M ⧸ reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n))

/-- 同じ I 進商の、変更後の基底環上の加群構造。 -/
@[instance_reducible]
def reesCoefficientAdicQuotientModule (n : ℕ) :
    Module B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  inferInstanceAs (Module B (M ⧸ reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n))

local instance (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := M) I n
local instance (n : ℕ) : Module B
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientModule (B := B) (ι := ι) (M := M) I n

/-- 元の基底と変更後の基底の作用の塔。 -/
theorem reesCoefficientAdicQuotient_base_scalarTower (n : ℕ) :
    IsScalarTower R B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  inferInstanceAs (IsScalarTower R B (M ⧸ reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n))

/-- 元の基底と変更後の多項式環の作用の塔。 -/
theorem reesCoefficientAdicQuotient_base_polynomial_scalarTower (n : ℕ) :
    IsScalarTower R (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  inferInstanceAs (IsScalarTower R (MvPolynomial ι B)
    (M ⧸ reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n))

/-- 変更後の基底と変更後の多項式環の作用の塔。 -/
theorem reesCoefficientAdicQuotient_polynomial_scalarTower (n : ℕ) :
    IsScalarTower B (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  inferInstanceAs (IsScalarTower B (MvPolynomial ι B)
    (M ⧸ reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n))

/-- 二つの多項式環の作用の塔。 -/
theorem reesCoefficientAdicQuotient_coefficient_scalarTower (n : ℕ) :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
      (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  inferInstanceAs (IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (M ⧸ reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n))

local instance (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := M) I n

/-- 変更後の多項式環上で見た、実際の I 進遷移。 -/
def reesCoefficientAdicQuotientTransition (i j : ℕ) (h : j ≤ i) :
    reesAdicProjectiveQuotient (ι := ι) (M := M) I i →ₗ[MvPolynomial ι B]
      reesAdicProjectiveQuotient (ι := ι) (M := M) I j :=
  (reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I i).mapQ
    (reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I j) LinearMap.id
    (reesAdicProjectiveSubmodule_antitone (ι := ι) (M := M) I h)

/-- I 進遷移の係数制限は、以前の実際の遷移そのものである。 -/
theorem reesCoefficientAdicQuotientTransition_restrictScalars
    (i j : ℕ) (h : j ≤ i) :
    (reesCoefficientAdicQuotientTransition (B := B) (ι := ι) (M := M) I i j h).restrictScalars (MvPolynomial ι R) =
      reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j h := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) I i x
  rfl

end SerrePositivity.AlgebraicGeometry
