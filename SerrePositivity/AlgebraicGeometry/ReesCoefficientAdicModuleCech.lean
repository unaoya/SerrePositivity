module

public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicModuleMap
public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicCechTransition
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMapLaws

/-!
概要：実際の加群写像が誘導する I 進 Čech 写像と、係数比較の可換性。
方針：商写像の遷移との可換性を標準開へ送り、Čech 関手に適用する。
規約：元の R 上の写像と変更後の B 上の写像を区別する。
使われ方：互換族の係数比較を任意の次数付き加群写像に自然にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type}
local instance reesCoefficientAdicModuleCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance reesCoefficientAdicModuleCechPolynomialTower :
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

local instance coefficientAdicModuleCechLocal0 (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance coefficientAdicModuleCechLocal1 (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicModuleCechLocal2 (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicModuleCechLocal3 (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) I n
local instance coefficientAdicModuleCechLocal4 (n : ℕ) : Module (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotientPolynomialModule (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicModuleCechLocal5 (n : ℕ) : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_coefficient_scalarTower (B := B) (ι := ι) (M := N) I n

local instance coefficientAdicModuleCechBaseModuleM (n : ℕ) :
    Module B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotientModule (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicModuleCechTowerM0 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance coefficientAdicModuleCechTowerM1 (n : ℕ) :
    IsScalarTower R B (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_base_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicModuleCechTowerM2 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_base_polynomial_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicModuleCechTowerM3 (n : ℕ) :
    IsScalarTower B (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesCoefficientAdicQuotient_polynomial_scalarTower (B := B) (ι := ι) (M := M) I n
local instance coefficientAdicModuleCechBaseModuleN (n : ℕ) :
    Module B (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotientModule (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicModuleCechTowerN0 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := N) I n
local instance coefficientAdicModuleCechTowerN1 (n : ℕ) :
    IsScalarTower R B (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_base_scalarTower (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicModuleCechTowerN2 (n : ℕ) :
    IsScalarTower R (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_base_polynomial_scalarTower (B := B) (ι := ι) (M := N) I n
local instance coefficientAdicModuleCechTowerN3 (n : ℕ) :
    IsScalarTower B (MvPolynomial ι B) (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesCoefficientAdicQuotient_polynomial_scalarTower (B := B) (ι := ι) (M := N) I n
variable (G : ℕ → Submodule B M) (H : ℕ → Submodule B N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (G d).restrictScalars R)]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (H d).restrictScalars R)]
local instance coefficientAdicModuleCechSourceGradedB (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (reesCoefficientAdicPiece (ι := ι) I G n) :=
  reesCoefficientAdicPieceGradedSMul (ι := ι) I G n
local instance coefficientAdicModuleCechSourceGradedR (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun d ↦ (reesCoefficientAdicPiece (ι := ι) I G n d).restrictScalars R) := by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨p • m, SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R)
    (B := fun d ↦ (G d).restrictScalars R) hp hm, rfl⟩
local instance coefficientAdicModuleCechTargetGradedB (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (reesCoefficientAdicPiece (ι := ι) I H n) :=
  reesCoefficientAdicPieceGradedSMul (ι := ι) I H n
local instance coefficientAdicModuleCechTargetGradedR (n : ℕ) :
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

/-- 実際の加群写像から得られる、B 上の I 進商の標準開の写像。 -/
def reesCoefficientAdicModuleChartMap (n : ℕ) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (R := B) (ι := ι)
    (reesCoefficientAdicPiece (ι := ι) I G n) (reesCoefficientAdicPiece (ι := ι) I H n)
    (reesCoefficientAdicQuotientModuleMap I f n)
    (reesCoefficientAdicQuotientModuleMap_preservesPiece I f G H hf n) d

/-- 元の R 上で計算する、実際の加群写像の I 進商の標準開の写像。 -/
def reesCoefficientAdicOriginalModuleChartMap (n : ℕ) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (R := R) (ι := ι)
    (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I G n a).restrictScalars R)
    (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I H n a).restrictScalars R)
    (reesAdicProjectiveQuotientMap I (f.restrictScalars (MvPolynomial ι R)) n)
    (reesCoefficientAdicQuotientModuleMap_preservesPiece I f G H hf n) d

/-- B 上の I 進標準開写像は、実際の I 進遷移と可換。 -/
theorem reesCoefficientAdicModuleChartMap_transition (i j : ℕ) (h : j ≤ i) (d : ℤ) :
    reesCoefficientAdicModuleChartMap I G H f hf i d ≫
        reesCoefficientAdicChartTransition (ι := ι) I H i j h d =
      reesCoefficientAdicChartTransition (ι := ι) I G i j h d ≫
        reesCoefficientAdicModuleChartMap I G H f hf j d := by
  unfold reesCoefficientAdicModuleChartMap reesCoefficientAdicChartTransition
  rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
  congr 1
  exact reesCoefficientAdicQuotientModuleMap_transition I f i j h

/-- R 上の I 進標準開写像も、実際の I 進遷移と可換。 -/
theorem reesCoefficientAdicOriginalModuleChartMap_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) :
    reesCoefficientAdicOriginalModuleChartMap I G H f hf i d ≫
        projectiveNatGradedModuleChartMap (ι := ι)
          (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I H i a).restrictScalars R)
          (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I H j a).restrictScalars R)
          (reesAdicProjectiveQuotientTransition (ι := ι) (M := N) I i j h)
          (reesCoefficientAdicTransition_preservesPiece (ι := ι) I H i j h) d =
      projectiveNatGradedModuleChartMap (ι := ι)
          (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I G i a).restrictScalars R)
          (fun a ↦ (reesCoefficientAdicPiece (ι := ι) I G j a).restrictScalars R)
          (reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j h)
          (reesCoefficientAdicTransition_preservesPiece (ι := ι) I G i j h) d ≫
        reesCoefficientAdicOriginalModuleChartMap I G H f hf j d := by
  unfold reesCoefficientAdicOriginalModuleChartMap
  rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
  congr 1
  exact reesAdicProjectiveQuotientMap_transition I (f.restrictScalars (MvPolynomial ι R)) i j h

/-- 各 I 進段の標準開係数比較は、実際の加群写像に自然。 -/
theorem reesCoefficientAdicChartIso_module_naturality (n : ℕ) (d : ℤ) :
    reesCoefficientAdicOriginalModuleChartMap I G H f hf n d ≫
        (reesCoefficientAdicChartIso (ι := ι) I H n d).hom =
      (reesCoefficientAdicChartIso (ι := ι) I G n d).hom ≫
        Functor.whiskerRight (reesCoefficientAdicModuleChartMap I G H f hf n d)
          (ModuleCat.restrictScalars (algebraMap R B)) := by
  simpa only [reesCoefficientAdicQuotientModuleMap_restrictScalars,
    reesCoefficientAdicOriginalModuleChartMap, reesCoefficientAdicChartIso,
    reesCoefficientAdicModuleChartMap] using
    projectiveNatCoefficientChartIso_naturality (R := R) (B := B) (ι := ι)
      (reesCoefficientAdicPiece (ι := ι) I G n) (reesCoefficientAdicPiece (ι := ι) I H n)
      (reesCoefficientAdicQuotientModuleMap I f n)
      (reesCoefficientAdicQuotientModuleMap_preservesPiece I f G H hf n) d

/-- 元の R 上での、実際の加群写像からの I 進 Čech コホモロジーの写像。 -/
def reesCoefficientAdicOriginalCechModuleMap (n : ℕ) (d : ℤ) (q : ℕ) :
    reesCoefficientAdicOriginalCechHomology (ι := ι) I G n d q ⟶
      reesCoefficientAdicOriginalCechHomology (ι := ι) I H n d q :=
  (fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
      (reesCoefficientAdicOriginalModuleChartMap I G H f hf n d)

/-- B 上の実際の加群写像からの I 進 Čech 写像の係数制限。 -/
def reesCoefficientAdicRestrictedCechModuleMap (n : ℕ) (d : ℤ) (q : ℕ) :
    reesCoefficientAdicRestrictedCechHomology (ι := ι) I G n d q ⟶
      reesCoefficientAdicRestrictedCechHomology (ι := ι) I H n d q :=
  (fullCechComplexFunctor (R := B) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q ⋙
      ModuleCat.restrictScalars (algebraMap R B)).map
        (reesCoefficientAdicModuleChartMap I G H f hf n d)

/-- R 上の実際の I 進 Čech 写像は遷移と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数の Čech 版に用いる可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesCoefficientAdicOriginalCechModuleMap_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesCoefficientAdicOriginalCechModuleMap I G H f hf i d q ≫
        reesCoefficientAdicOriginalCechTransition (ι := ι) I H i j h d q =
      reesCoefficientAdicOriginalCechTransition (ι := ι) I G i j h d q ≫
        reesCoefficientAdicOriginalCechModuleMap I G H f hf j d q := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  have hK := congrArg (fun η ↦ K.map η)
    (reesCoefficientAdicOriginalModuleChartMap_transition I G H f hf i j h d)
  simp only [Functor.map_comp] at hK
  convert hK using 1 <;> rfl

/-- B 上の実際の I 進 Čech 写像の係数制限も遷移と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数の Čech 版に用いる可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesCoefficientAdicRestrictedCechModuleMap_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesCoefficientAdicRestrictedCechModuleMap I G H f hf i d q ≫
        reesCoefficientAdicRestrictedCechTransition (ι := ι) I H i j h d q =
      reesCoefficientAdicRestrictedCechTransition (ι := ι) I G i j h d q ≫
        reesCoefficientAdicRestrictedCechModuleMap I G H f hf j d q := by
  let K := fullCechComplexFunctor (R := B) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q ⋙
      ModuleCat.restrictScalars (algebraMap R B)
  have hK := congrArg (fun η ↦ K.map η)
    (reesCoefficientAdicModuleChartMap_transition I G H f hf i j h d)
  simp only [Functor.map_comp] at hK
  convert hK using 1 <;> rfl

/-- I 進 Čech コホモロジーの係数比較は、実際の加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesCoefficientAdicCechIso_module_naturality (n : ℕ) (d : ℤ) (q : ℕ) :
    reesCoefficientAdicOriginalCechModuleMap I G H f hf n d q ≫
        (reesCoefficientAdicCechIso (ι := ι) I H n d q).hom =
      (reesCoefficientAdicCechIso (ι := ι) I G n d q).hom ≫
        reesCoefficientAdicRestrictedCechModuleMap I G H f hf n d q := by
  have h := projectiveNatCoefficientCechIso_naturality (R := R) (B := B) (ι := ι)
    (reesCoefficientAdicPiece (ι := ι) I G n) (reesCoefficientAdicPiece (ι := ι) I H n)
    (reesCoefficientAdicQuotientModuleMap I f n)
    (reesCoefficientAdicQuotientModuleMap_preservesPiece I f G H hf n) d q
  convert h using 1 <;> rfl

end SerrePositivity.AlgebraicGeometry
