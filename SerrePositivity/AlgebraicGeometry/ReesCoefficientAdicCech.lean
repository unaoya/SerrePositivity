module

public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicQuotient
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatCoefficientNaturality

/-!
概要：I 進閉厚化の係数比較を、実際の遷移と可換な Čech 比較にする。
方針：商の次数成分を変更後の基底環で表し、次数付き加群の自然性を適用する。
規約：係数環を固定したまま各段の商を比較する。
使われ方：閉厚化の商環係数表示を互換族と形式関数へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type}
local instance reesCoefficientAdicCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance reesCoefficientAdicCechPolynomialTower :
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

local instance (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) I n
local instance (n : ℕ) : Module (B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientModule (B := B) (ι := ι) I n
local instance (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n
local instance (n : ℕ) : IsScalarTower R B
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_base_scalarTower (B := B) (ι := ι) I n
local instance (n : ℕ) : IsScalarTower R (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_base_polynomial_scalarTower (B := B) (ι := ι) I n
local instance (n : ℕ) : IsScalarTower B (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_polynomial_scalarTower (B := B) (ι := ι) I n
local instance (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) I n

/-- 変更後の基底環上で見た、実際の I 進商への射影。 -/
def reesCoefficientAdicProjection (n : ℕ) :
    M →ₗ[MvPolynomial ι B] reesAdicProjectiveQuotient (ι := ι) (M := M) I n :=
  (reesCoefficientAdicSubmodule (B := B) (ι := ι) (M := M) I n).mkQ

variable (G : ℕ → Submodule B M)

/-- I 進商の Proj 次数成分を、変更後の係数環上の部分加群として表す。 -/
def reesCoefficientAdicPiece (n d : ℕ) :
    Submodule B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  (G d).map ((reesCoefficientAdicProjection (B := B) (ι := ι) I n).restrictScalars B)

/-- I 進商の次数成分は、係数制限で元の R 上の商次数成分に戻る。 -/
theorem reesCoefficientAdicPiece_restrictScalars (n d : ℕ) :
    (reesCoefficientAdicPiece (ι := ι) I G n d).restrictScalars R =
      reesAdicProjectiveQuotientPiece (ι := ι) I (fun j ↦ (G j).restrictScalars R) n d := rfl

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) G]

/-- 変更後の多項式係数の作用は、I 進商の次数を保つ。 -/
theorem reesCoefficientAdicPieceGradedSMul (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (reesCoefficientAdicPiece (ι := ι) I G n) := by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  refine ⟨p • m, SetLike.GradedSMul.smul_mem hp hm, ?_⟩
  exact (reesCoefficientAdicProjection (B := B) (ι := ι) I n).map_smul p m

/-- 実際の I 進遷移は、変更後の係数環で表した次数成分も保つ。 -/
theorem reesCoefficientAdicTransition_preservesPiece (i j : ℕ) (h : j ≤ i)
    (d : ℕ) (x : reesAdicProjectiveQuotient (ι := ι) (M := M) I i)
    (hx : x ∈ reesCoefficientAdicPiece (ι := ι) I G i d) :
    reesCoefficientAdicQuotientTransition (B := B) (ι := ι) I i j h x ∈
      reesCoefficientAdicPiece (ι := ι) I G j d := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨m, hm, rfl⟩

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (G d).restrictScalars R)]
local instance (n : ℕ) : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
    (reesCoefficientAdicPiece (ι := ι) I G n) :=
  reesCoefficientAdicPieceGradedSMul (ι := ι) I G n
local instance (n : ℕ) : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
    (fun d ↦ (reesCoefficientAdicPiece (ι := ι) I G n d).restrictScalars R) :=
by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨p • m, SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R)
    (B := fun d ↦ (G d).restrictScalars R) hp hm, rfl⟩

variable [DecidableEq ι] [Fintype ι]

/-- I 進商の標準開図式の、変更後の係数環への比較同型。 -/
def reesCoefficientAdicChartIso (n : ℕ) (d : ℤ) :=
  projectiveNatCoefficientChartIso (R := R) (B := B) (ι := ι)
    (reesCoefficientAdicPiece (ι := ι) I G n) d

/-- 変更後の係数環上での、実際の I 進遷移の標準開写像。 -/
def reesCoefficientAdicChartTransition (i j : ℕ) (h : j ≤ i) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (R := B) (ι := ι)
    (reesCoefficientAdicPiece (ι := ι) I G i) (reesCoefficientAdicPiece (ι := ι) I G j)
    (reesCoefficientAdicQuotientTransition (B := B) (ι := ι) I i j h)
    (reesCoefficientAdicTransition_preservesPiece (ι := ι) I G i j h) d

/-- I 進商の係数比較は、実際の I 進遷移と可換。 -/
theorem reesCoefficientAdicChartIso_transition (i j : ℕ) (h : j ≤ i) (d : ℤ) :
    projectiveNatGradedModuleChartMap (ι := ι)
        (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I G i a).restrictScalars R)
        (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I G j a).restrictScalars R)
        (reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j h)
        (reesCoefficientAdicTransition_preservesPiece (ι := ι) I G i j h) d ≫
      (reesCoefficientAdicChartIso (ι := ι) I G j d).hom =
    (reesCoefficientAdicChartIso (ι := ι) I G i d).hom ≫
      Functor.whiskerRight (reesCoefficientAdicChartTransition (ι := ι) I G i j h d)
        (ModuleCat.restrictScalars (algebraMap R B)) := by
  have ht := reesCoefficientAdicQuotientTransition_restrictScalars
    (B := B) (ι := ι) (M := M) I i j h
  simpa only [ht, reesCoefficientAdicChartIso, reesCoefficientAdicChartTransition] using projectiveNatCoefficientChartIso_naturality
    (R := R) (B := B) (ι := ι)
    (reesCoefficientAdicPiece (ι := ι) I G i) (reesCoefficientAdicPiece (ι := ι) I G j)
    (reesCoefficientAdicQuotientTransition (B := B) (ι := ι) I i j h)
    (reesCoefficientAdicTransition_preservesPiece (ι := ι) I G i j h) d

end SerrePositivity.AlgebraicGeometry
