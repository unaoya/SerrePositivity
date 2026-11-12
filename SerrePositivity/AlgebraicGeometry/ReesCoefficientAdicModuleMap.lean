module

public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicCech
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveModuleMap

/-!
概要：商係数の I 進商の写像を、実際の加群写像から構成する。
方針：I 進部分加群の保存で商へ降ろし、代表上で射影と遷移の可換性を示す。
規約：変更後の多項式環上で線形とし、元の係数への制限も照合する。
使われ方：I 進系全体の Čech 係数比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type}
local instance reesCoefficientAdicModuleMapPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance reesCoefficientAdicModuleMapPolynomialTower :
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
variable {N : Type u} [AddCommGroup N] [Module R N] [Module B N]
variable [Module (MvPolynomial ι R) N] [Module (MvPolynomial ι B) N]
variable [IsScalarTower R B N] [IsScalarTower R (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι B) N] [IsScalarTower B (MvPolynomial ι B) N]
variable [IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) N]
variable [Fact (Function.Surjective (algebraMap R B))]
variable (I : Ideal R)

local instance coefficientAdicModuleMapLocal0 (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance coefficientAdicModuleMapLocal1 (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicModuleMapLocal2 (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicModuleMapLocal3 (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) I n
local instance coefficientAdicModuleMapLocal4 (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicModuleMapLocal5 (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := N) I n

variable (f : M →ₗ[MvPolynomial ι B] N)

/-- 変更後の多項式環上で見た、実際の加群写像の I 進商への降下。 -/
def reesCoefficientAdicQuotientModuleMap (n : ℕ) :
    reesAdicProjectiveQuotient (ι := ι) (M := M) I n →ₗ[MvPolynomial ι B]
      reesAdicProjectiveQuotient (ι := ι) (M := N) I n :=
  (reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n).mapQ
    (reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := N) I n) f
    (fun x hx ↦ reesExtendedAdic_map_mem (S := MvPolynomial ι R) I
      (f.restrictScalars R) n x hx)

/-- 商係数の I 進商の写像の係数制限は、元の実際の商写像である。 -/
theorem reesCoefficientAdicQuotientModuleMap_restrictScalars (n : ℕ) :
    (reesCoefficientAdicQuotientModuleMap I f n).restrictScalars (MvPolynomial ι R) =
      reesAdicProjectiveQuotientMap I (f.restrictScalars (MvPolynomial ι R)) n := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) I n x
  rfl

/-- 商係数の I 進商の写像は、商への実際の射影と可換。 -/
theorem reesCoefficientAdicQuotientModuleMap_projection (n : ℕ) :
    (reesCoefficientAdicQuotientModuleMap I f n).comp
        (reesCoefficientAdicProjection (B := B) (ι := ι) (M := M) I n) =
      (reesCoefficientAdicProjection (B := B) (ι := ι) (M := N) I n).comp f := by
  apply LinearMap.ext
  intro m
  rfl

/-- 商係数の I 進商の写像は、実際の I 進遷移と可換。 -/
theorem reesCoefficientAdicQuotientModuleMap_transition (i j : ℕ) (h : j ≤ i) :
    (reesCoefficientAdicQuotientTransition (B := B) (ι := ι) (M := N) I i j h).comp
        (reesCoefficientAdicQuotientModuleMap I f i) =
      (reesCoefficientAdicQuotientModuleMap I f j).comp
        (reesCoefficientAdicQuotientTransition (B := B) (ι := ι) (M := M) I i j h) := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) I i x
  rfl

variable (G : ℕ → Submodule B M) (H : ℕ → Submodule B N)
variable (hf : ∀ d, ∀ m ∈ G d, f m ∈ H d)
include hf

/-- 商係数の I 進商の写像は、元の射が保つ Proj 次数を保つ。 -/
theorem reesCoefficientAdicQuotientModuleMap_preservesPiece (n d : ℕ)
    (x : reesAdicProjectiveQuotient (ι := ι) (M := M) I n)
    (hx : x ∈ reesCoefficientAdicPiece (ι := ι) I G n d) :
    reesCoefficientAdicQuotientModuleMap I f n x ∈
      reesCoefficientAdicPiece (ι := ι) I H n d := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨f m, hf d m hm, rfl⟩

end SerrePositivity.AlgebraicGeometry
