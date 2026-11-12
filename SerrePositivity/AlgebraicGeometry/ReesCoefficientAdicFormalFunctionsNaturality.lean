module

public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicFamiliesNaturality
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechModuleNaturality

/-!
概要：商係数表示の Čech 形式関数を、任意の次数付き加群写像に自然にする。
方針：実際の R 上の互換族写像と照合し、係数比較と既存の形式関数の自然性を合成する。
規約：完備化は元の R 上で取り、各閉厚化の Čech 計算を B 上で表示する。
使われ方：閉厚化を含む射に自然な形式関数の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type}
local instance reesCoefficientAdicFormalPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance reesCoefficientAdicFormalPolynomialTower :
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

local instance coefficientAdicFormalLocal0 (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance coefficientAdicFormalLocal1 (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFormalLocal2 (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFormalLocal3 (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) I n
local instance coefficientAdicFormalLocal4 (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicFormalLocal5 (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := N) I n

local instance coefficientAdicFormalBaseModuleM (n : ℕ) :
    Module B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientModule (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFormalTowerM0 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance coefficientAdicFormalTowerM1 (n : ℕ) :
    IsScalarTower R B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_base_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFormalTowerM2 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_base_polynomial_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFormalTowerM3 (n : ℕ) :
    IsScalarTower B (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_polynomial_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFormalBaseModuleN (n : ℕ) :
    Module B (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotientModule (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicFormalTowerN0 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := N) I n
local instance coefficientAdicFormalTowerN1 (n : ℕ) :
    IsScalarTower R B (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_base_scalarTower (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicFormalTowerN2 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_base_polynomial_scalarTower (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicFormalTowerN3 (n : ℕ) :
    IsScalarTower B (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_polynomial_scalarTower (B := B) (ι := ι) (M := N) I n
variable (G : ℕ → Submodule B M) (H : ℕ → Submodule B N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (G d).restrictScalars R)]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (H d).restrictScalars R)]
local instance coefficientAdicFormalSourceGradedB (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (reesCoefficientAdicPiece (ι := ι) I G n) :=
  reesCoefficientAdicPieceGradedSMul (ι := ι) I G n
local instance coefficientAdicFormalSourceGradedR (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun d ↦ (reesCoefficientAdicPiece (ι := ι) I G n d).restrictScalars R) := by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨p • m, SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R)
    (B := fun d ↦ (G d).restrictScalars R) hp hm, rfl⟩
local instance coefficientAdicFormalTargetGradedB (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (reesCoefficientAdicPiece (ι := ι) I H n) :=
  reesCoefficientAdicPieceGradedSMul (ι := ι) I H n
local instance coefficientAdicFormalTargetGradedR (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun d ↦ (reesCoefficientAdicPiece (ι := ι) I H n d).restrictScalars R) := by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨p • m, SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R)
    (B := fun d ↦ (H d).restrictScalars R) hp hm, rfl⟩
variable [LinearOrder ι] [Fintype ι]
variable [DirectSum.Decomposition (fun d ↦ (G d).restrictScalars R)]
variable [DirectSum.Decomposition (fun d ↦ (H d).restrictScalars R)]

/-- 完備化から実際の I 進 Čech 互換族への標準写像を、B 上の表示へ送る。 -/
def reesCoefficientAdicCompletionMap (d : ℤ) (q : ℕ) :=
  (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I G d q).toLinearMap.comp
    (reesAdicProjectiveClosedCechCompletionMap (ι := ι) I
      (fun a ↦ (G a).restrictScalars R) d q)

variable (f : M →ₗ[MvPolynomial ι B] N) (hf : ∀ d, ∀ m ∈ G d, f m ∈ H d)

/-- 元の R 上の実際の互換族写像は、既存の I 進 Čech 写像に一致する。 -/
theorem reesCoefficientAdicOriginalCechFamiliesMap_eq_native (d : ℤ) (q : ℕ) :
    reesCoefficientAdicOriginalCechFamiliesMap I G H f hf d q =
      reesAdicProjectiveClosedCechModuleFamiliesMap I
        (fun a ↦ (G a).restrictScalars R) (fun a ↦ (H a).restrictScalars R)
        (f.restrictScalars (MvPolynomial ι R)) hf d q := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  rfl

/-- 商係数表示の完備化からの標準 Čech 写像は、任意の次数付き加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数の Čech 版に用いる可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesCoefficientAdicCompletionMap_module_naturality (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι)
      (fun b ↦ (G b).restrictScalars R) d q)) :
    reesCoefficientAdicRestrictedCechFamiliesMap I G H f hf d q
        (reesCoefficientAdicCompletionMap (ι := ι) I G d q a) =
      reesCoefficientAdicCompletionMap (ι := ι) I H d q
        (AdicCompletion.map I (projectiveNatGradedModuleCechHomologyMap
          (fun b ↦ (G b).restrictScalars R) (fun b ↦ (H b).restrictScalars R)
          (f.restrictScalars (MvPolynomial ι R)) hf d q).hom a) := by
  change reesCoefficientAdicRestrictedCechFamiliesMap I G H f hf d q
      (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I G d q
        (reesAdicProjectiveClosedCechCompletionMap (ι := ι) I
          (fun b ↦ (G b).restrictScalars R) d q a)) = _
  rw [← reesCoefficientAdicCechFamiliesEquiv_module_naturality]
  apply congrArg (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I H d q)
  rw [reesCoefficientAdicOriginalCechFamiliesMap_eq_native]
  exact reesAdicProjectiveClosedCechCompletionMap_module_naturality I
    (fun b ↦ (G b).restrictScalars R) (fun b ↦ (H b).restrictScalars R)
    (f.restrictScalars (MvPolynomial ι R)) hf d q a

variable [IsNoetherianRing R]
variable [Module.Finite (MvPolynomial ι R) M] [Module.Finite (MvPolynomial ι R) N]

/-- Čech 形式関数を、B 上で計算した実際の I 進閉厚化の互換族で表す同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesCoefficientAdicFormalFunctions (d : ℤ) (q : ℕ) :
    AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι)
        (fun b ↦ (G b).restrictScalars R) d q) ≃ₗ[R]
      reesCoefficientAdicRestrictedCechFamilies (ι := ι) I G d q :=
  (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I
    (fun b ↦ (G b).restrictScalars R) d q).trans
      (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I G d q)

/-- 商係数表示の形式関数の順写像は、既存の標準 Čech 写像そのものである。 -/
theorem reesCoefficientAdicFormalFunctions_toLinearMap (d : ℤ) (q : ℕ) :
    (reesCoefficientAdicFormalFunctions (ι := ι) I G d q).toLinearMap =
      reesCoefficientAdicCompletionMap (ι := ι) I G d q := rfl

/-- 商係数表示の Čech 形式関数は、任意の次数付き加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数の自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesCoefficientAdicFormalFunctions_module_naturality (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι)
      (fun b ↦ (G b).restrictScalars R) d q)) :
    reesCoefficientAdicRestrictedCechFamiliesMap I G H f hf d q
        (reesCoefficientAdicFormalFunctions (ι := ι) I G d q a) =
      reesCoefficientAdicFormalFunctions (ι := ι) I H d q
        (AdicCompletion.map I (projectiveNatGradedModuleCechHomologyMap
          (fun b ↦ (G b).restrictScalars R) (fun b ↦ (H b).restrictScalars R)
          (f.restrictScalars (MvPolynomial ι R)) hf d q).hom a) := by
  change reesCoefficientAdicRestrictedCechFamiliesMap I G H f hf d q
      (reesCoefficientAdicCompletionMap (ι := ι) I G d q a) =
    reesCoefficientAdicCompletionMap (ι := ι) I H d q _
  exact reesCoefficientAdicCompletionMap_module_naturality I G H f hf d q a

end SerrePositivity.AlgebraicGeometry
