module

public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicCech
public import SerrePositivity.AlgebraicGeometry.LinearCompatibleFamiliesEquiv

/-!
概要：I 進商の Čech 係数比較を、遷移と互換族の比較へ送る。
方針：標準開での自然性を Čech 関手へ送り、互換な成分同型をまとめる。
規約：係数制限による比較であり、非平坦なテンソル交換は使わない。
使われ方：閉厚化の商係数の形式関数への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type}
local instance reesCoefficientAdicTransitionPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance reesCoefficientAdicTransitionPolynomialTower :
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

variable (G : ℕ → Submodule B M)

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) G]
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

/-- 元の R 上で計算する、実際の I 進商の Čech コホモロジー。 -/
abbrev reesCoefficientAdicOriginalCechHomology (n : ℕ) (d : ℤ) (q : ℕ) : ModuleCat.{u} R :=
  (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
    (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I G n a).restrictScalars R) d)).homology q

/-- 元の R 上で計算する、実際の I 進遷移の Čech 写像。 -/
def reesCoefficientAdicOriginalCechTransition (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :=
  projectiveNatGradedModuleCechHomologyMap (R := R) (ι := ι)
    (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I G i a).restrictScalars R)
    (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I G j a).restrictScalars R)
    (reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j h)
    (reesCoefficientAdicTransition_preservesPiece (ι := ι) I G i j h) d q

/-- 変更後の係数環上で計算した Čech コホモロジーの係数制限。 -/
abbrev reesCoefficientAdicRestrictedCechHomology (n : ℕ) (d : ℤ) (q : ℕ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (algebraMap R B)).obj
    ((fullCechComplex (projectiveNatGradedModuleChartDiagram (R := B) (ι := ι)
      (reesCoefficientAdicPiece (ι := ι) I G n) d)).homology q)

/-- I 進商の Čech コホモロジーの係数比較。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesCoefficientAdicCechIso (n : ℕ) (d : ℤ) (q : ℕ) :
    reesCoefficientAdicOriginalCechHomology (ι := ι) I G n d q ≅
      reesCoefficientAdicRestrictedCechHomology (ι := ι) I G n d q :=
  projectiveNatCoefficientCechIso (R := R) (B := B) (ι := ι)
    (reesCoefficientAdicPiece (ι := ι) I G n) d q

/-- 変更後の係数環上の I 進遷移が誘導する Čech 写像の係数制限。 -/
def reesCoefficientAdicRestrictedCechTransition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesCoefficientAdicRestrictedCechHomology (ι := ι) I G i d q ⟶
      reesCoefficientAdicRestrictedCechHomology (ι := ι) I G j d q :=
  (ModuleCat.restrictScalars (algebraMap R B)).map
    (projectiveNatGradedModuleCechHomologyMap (R := B) (ι := ι)
      (reesCoefficientAdicPiece (ι := ι) I G i) (reesCoefficientAdicPiece (ι := ι) I G j)
      (reesCoefficientAdicQuotientTransition (B := B) (ι := ι) I i j h)
      (reesCoefficientAdicTransition_preservesPiece (ι := ι) I G i j h) d q)

/-- I 進商の Čech 係数比較は、実際の I 進遷移と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesCoefficientAdicCechIso_transition (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesCoefficientAdicOriginalCechTransition (ι := ι) I G i j h d q ≫
        (reesCoefficientAdicCechIso (ι := ι) I G j d q).hom =
      (reesCoefficientAdicCechIso (ι := ι) I G i d q).hom ≫
        reesCoefficientAdicRestrictedCechTransition (ι := ι) I G i j h d q := by
  have ht := reesCoefficientAdicQuotientTransition_restrictScalars
    (B := B) (ι := ι) (M := M) I i j h
  simpa only [ht, reesCoefficientAdicOriginalCechTransition,
    reesCoefficientAdicCechIso, reesCoefficientAdicRestrictedCechTransition] using
    projectiveNatCoefficientCechIso_naturality (R := R) (B := B) (ι := ι)
      (reesCoefficientAdicPiece (ι := ι) I G i) (reesCoefficientAdicPiece (ι := ι) I G j)
      (reesCoefficientAdicQuotientTransition (B := B) (ι := ι) I i j h)
      (reesCoefficientAdicTransition_preservesPiece (ι := ι) I G i j h) d q

/-- 変更後の係数環で計算した I 進 Čech コホモロジーの互換族。 -/
def reesCoefficientAdicRestrictedCechFamilies (d : ℤ) (q : ℕ) :=
  compatibleLinearFamilies
    (fun i j h ↦ (reesCoefficientAdicRestrictedCechTransition (ι := ι) I G i j h d q).hom)

/-- 元の R 上の互換族と、変更後の係数環上の計算の互換族との同型。 -/
def reesCoefficientAdicCechFamiliesEquiv (d : ℤ) (q : ℕ) :
    compatibleLinearFamilies
        (fun i j h ↦ (reesCoefficientAdicOriginalCechTransition (ι := ι) I G i j h d q).hom) ≃ₗ[R]
      reesCoefficientAdicRestrictedCechFamilies (ι := ι) I G d q :=
  compatibleLinearFamiliesEquiv _ _
    (fun n ↦ (reesCoefficientAdicCechIso (ι := ι) I G n d q).toLinearEquiv)
    (fun i j h ↦ congrArg ModuleCat.Hom.hom
      (reesCoefficientAdicCechIso_transition (ι := ι) I G i j h d q).symm)

end SerrePositivity.AlgebraicGeometry
