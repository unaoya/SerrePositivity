module

public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicModuleCech

/-!
概要：I 進 Čech 互換族の係数比較を、任意の次数付き加群写像に自然にする。
方針：各段の実際の写像と遷移の可換性から互換族の写像を作り、成分で比較する。
規約：元の R 上と変更後の B 上の互換族を、同じ R 線形な写像で比較する。
使われ方：射に自然な商係数表示の形式関数への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type}
local instance reesCoefficientAdicFamiliesPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance reesCoefficientAdicFamiliesPolynomialTower :
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

local instance coefficientAdicFamiliesLocal0 (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance coefficientAdicFamiliesLocal1 (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFamiliesLocal2 (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFamiliesLocal3 (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) I n
local instance coefficientAdicFamiliesLocal4 (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicFamiliesLocal5 (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := N) I n

local instance coefficientAdicFamiliesBaseModuleM (n : ℕ) :
    Module B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientModule (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFamiliesTowerM0 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance coefficientAdicFamiliesTowerM1 (n : ℕ) :
    IsScalarTower R B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_base_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFamiliesTowerM2 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_base_polynomial_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFamiliesTowerM3 (n : ℕ) :
    IsScalarTower B (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_polynomial_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicFamiliesBaseModuleN (n : ℕ) :
    Module B (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotientModule (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicFamiliesTowerN0 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := N) I n
local instance coefficientAdicFamiliesTowerN1 (n : ℕ) :
    IsScalarTower R B (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_base_scalarTower (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicFamiliesTowerN2 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_base_polynomial_scalarTower (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicFamiliesTowerN3 (n : ℕ) :
    IsScalarTower B (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_polynomial_scalarTower (B := B) (ι := ι) (M := N) I n
variable (G : ℕ → Submodule B M) (H : ℕ → Submodule B N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (G d).restrictScalars R)]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (H d).restrictScalars R)]
local instance coefficientAdicFamiliesSourceGradedB (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (reesCoefficientAdicPiece (ι := ι) I G n) :=
  reesCoefficientAdicPieceGradedSMul (ι := ι) I G n
local instance coefficientAdicFamiliesSourceGradedR (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun d ↦ (reesCoefficientAdicPiece (ι := ι) I G n d).restrictScalars R) := by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨p • m, SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R)
    (B := fun d ↦ (G d).restrictScalars R) hp hm, rfl⟩
local instance coefficientAdicFamiliesTargetGradedB (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (reesCoefficientAdicPiece (ι := ι) I H n) :=
  reesCoefficientAdicPieceGradedSMul (ι := ι) I H n
local instance coefficientAdicFamiliesTargetGradedR (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun d ↦ (reesCoefficientAdicPiece (ι := ι) I H n d).restrictScalars R) := by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨p • m, SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R)
    (B := fun d ↦ (H d).restrictScalars R) hp hm, rfl⟩
variable [DecidableEq ι] [Fintype ι]
variable (f : M →ₗ[MvPolynomial ι B] N) (hf : ∀ d, ∀ m ∈ G d, f m ∈ H d)

/-- 元の R 上の I 進 Čech 互換族の、実際の加群写像が誘導する写像。 -/
def reesCoefficientAdicOriginalCechFamiliesMap (d : ℤ) (q : ℕ) :
    compatibleLinearFamilies
        (fun i j h ↦ (reesCoefficientAdicOriginalCechTransition (ι := ι) I G i j h d q).hom) →ₗ[R]
      compatibleLinearFamilies
        (fun i j h ↦ (reesCoefficientAdicOriginalCechTransition (ι := ι) I H i j h d q).hom) :=
  compatibleLinearFamiliesMap _ _
    (fun n ↦ (reesCoefficientAdicOriginalCechModuleMap I G H f hf n d q).hom)
    (fun i j h ↦ congrArg ModuleCat.Hom.hom
      (reesCoefficientAdicOriginalCechModuleMap_transition I G H f hf i j h d q))

/-- B 上で計算した I 進 Čech 互換族の、実際の加群写像が誘導する写像。 -/
def reesCoefficientAdicRestrictedCechFamiliesMap (d : ℤ) (q : ℕ) :
    reesCoefficientAdicRestrictedCechFamilies (ι := ι) I G d q →ₗ[R]
      reesCoefficientAdicRestrictedCechFamilies (ι := ι) I H d q :=
  compatibleLinearFamiliesMap _ _
    (fun n ↦ (reesCoefficientAdicRestrictedCechModuleMap I G H f hf n d q).hom)
    (fun i j h ↦ congrArg ModuleCat.Hom.hom
      (reesCoefficientAdicRestrictedCechModuleMap_transition I G H f hf i j h d q))

/-- I 進 Čech 互換族の係数比較は、実際の加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesCoefficientAdicCechFamiliesEquiv_module_naturality (d : ℤ) (q : ℕ)
    (x : compatibleLinearFamilies
      (fun i j h ↦ (reesCoefficientAdicOriginalCechTransition (ι := ι) I G i j h d q).hom)) :
    reesCoefficientAdicCechFamiliesEquiv (ι := ι) I H d q
        (reesCoefficientAdicOriginalCechFamiliesMap I G H f hf d q x) =
      reesCoefficientAdicRestrictedCechFamiliesMap I G H f hf d q
        (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I G d q x) := by
  apply Subtype.ext
  funext n
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (reesCoefficientAdicCechIso_module_naturality I G H f hf n d q)) (x.val n)

/-- 互換族の係数比較の自然性を、R 線形写像の可換な合成として述べる。 -/
theorem reesCoefficientAdicCechFamiliesEquiv_module_naturality_linear (d : ℤ) (q : ℕ) :
    (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I H d q).toLinearMap.comp
        (reesCoefficientAdicOriginalCechFamiliesMap I G H f hf d q) =
      (reesCoefficientAdicRestrictedCechFamiliesMap I G H f hf d q).comp
        (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I G d q).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact reesCoefficientAdicCechFamiliesEquiv_module_naturality I G H f hf d q x

/-- 互換族の係数比較の逆写像も、実際の加群写像に自然。 -/
theorem reesCoefficientAdicCechFamiliesEquiv_symm_module_naturality (d : ℤ) (q : ℕ)
    (x : reesCoefficientAdicRestrictedCechFamilies (ι := ι) I G d q) :
    reesCoefficientAdicOriginalCechFamiliesMap I G H f hf d q
        ((reesCoefficientAdicCechFamiliesEquiv (ι := ι) I G d q).symm x) =
      (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I H d q).symm
        (reesCoefficientAdicRestrictedCechFamiliesMap I G H f hf d q x) := by
  apply (reesCoefficientAdicCechFamiliesEquiv (ι := ι) I H d q).injective
  rw [reesCoefficientAdicCechFamiliesEquiv_module_naturality,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end SerrePositivity.AlgebraicGeometry
