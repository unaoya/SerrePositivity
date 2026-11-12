module

public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorChartDiagram

/-!
概要：実際の標準開のテンソル比較を、次数を保つ多項式加群の射に自然にする。
方針：純テンソルの分数を用いて成分の四角形を示し、図式の四角形へまとめる。
規約：元の多項式環上で次数を保つ射を、実際の基底変更後の射へ送る。
使われ方：flat な Čech 比較と、閉厚化・I 進系の自然性を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
variable {R B M : Type u} {ι : Type} [CommRing R] [CommRing B] [Algebra R B]
variable [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
local instance projectiveTensorMapNaturalityCoefficientModule {V : Type*}
    [AddCommGroup V] [Module R V] : Module B (V ⊗[R] B) := tensorRightCoefficientModule
local instance projectiveTensorMapNaturalityCoefficientTower {V : Type*}
    [AddCommGroup V] [Module R V] : IsScalarTower R B (V ⊗[R] B) :=
  tensorRightCoefficient_scalarTower
local instance projectiveTensorMapNaturalityPolynomialModule :
    Module (MvPolynomial ι B) (M ⊗[R] B) := projectiveTensorPolynomialModule
local instance projectiveTensorMapNaturalityBPolynomialTower :
    IsScalarTower B (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_coefficient_scalarTower
local instance projectiveTensorMapNaturalityRPolynomialTower :
    IsScalarTower R (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_base_scalarTower
local instance projectiveTensorMapNaturalityPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance projectiveTensorMapNaturalityPolynomialRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R B r) =
    MvPolynomial.map (algebraMap R B) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]
local instance projectiveTensorMapNaturalityPolynomialTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_polynomial_scalarTower

variable (G : ℕ → Submodule R M)


variable {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (H : ℕ → Submodule R N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : M →ₗ[MvPolynomial ι R] N) (hf : ∀ j, ∀ m ∈ G j, f m ∈ H j)
local instance projectiveTensorMapNaturalityGradedAction :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (projectiveTensorPiece (B := B) G) := projectiveTensorPiece_gradedSMul (ι := ι) G
local instance projectiveTensorMapNaturalityIntGradedAction :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt G) := projectiveNatGradingIntSMul (ι := ι) G

/-- 各標準開の実際のテンソル比較は、次数を保つ加群写像に自然。 -/
theorem projectiveTensorChartLinearEquiv_map [Module.Flat R B]
    (T : Finset ι) (d : ℤ) (b : B)
    (u : (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) :
    projectiveTensorChartLinearEquiv (B := B) H T d
        (b ⊗ₜ[R] ((projectiveNatGradedModuleChartMap G H f hf d).app T).hom u) =
      ((projectiveTensorGradedModuleChartMap (B := B) G H f hf d).app T).hom
        (projectiveTensorChartLinearEquiv G T d (b ⊗ₜ[R] u)) := by
  let V (k : ℕ) := projectiveNatGradingInt G (d + k • (T.card : ℤ))
  let W (k : ℕ) := projectiveNatGradingInt H (d + k • (T.card : ℤ))
  obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff
    (projectiveLaurentDenominator R T) V
    (projectiveGradedChart_mul_denominator (projectiveNatGradingInt G) T d) u.val).mp u.property
  let mH : W n := ⟨f m.val,
    projectiveNatGradingInt_map_mem G H f hf _ m.val m.property⟩
  let uH := ((projectiveNatGradedModuleChartMap G H f hf d).app T).hom u
  have hmu : uH.val = projectiveGradedFraction (projectiveLaurentDenominator R T) W n mH := by
    change IsLocalizedModule.map (Submonoid.powers (projectiveLaurentDenominator R T))
      (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) f u.val = _
    rw [← hm, projectiveGradedFraction_apply, projectiveGradedFraction_apply,
      IsLocalizedModule.map_LocalizedModules]
  apply Subtype.ext
  change (projectiveTensorChartLinearEquiv (B := B) H T d (b ⊗ₜ[R] uH)).val =
    IsLocalizedModule.map (Submonoid.powers (projectiveLaurentDenominator B T))
      (LocalizedModule.mkLinearMap _ (M ⊗[R] B))
      (LocalizedModule.mkLinearMap _ (N ⊗[R] B)) (projectiveTensorPolynomialMap f)
      (projectiveTensorChartLinearEquiv G T d (b ⊗ₜ[R] u)).val
  rw [projectiveTensorChartLinearEquiv_fraction H T d n mH b uH hmu,
    projectiveTensorChartLinearEquiv_fraction G T d n m b u hm.symm,
    IsLocalizedModule.map_LocalizedModules, projectiveTensorPolynomialMap_tmul]

/-- 標準開図式の実際のテンソル比較は、次数を保つ加群写像の自然変換と可換。 -/
theorem projectiveTensorChartDiagramIso_naturality (φ : R →+* B) (hφ : φ.Flat)
    (d : ℤ) :
    letI := φ.toAlgebra
    Functor.whiskerRight (projectiveNatGradedModuleChartMap G H f hf d)
        (ModuleCat.extendScalars φ) ≫ (projectiveTensorChartDiagramIso H φ hφ d).hom =
      (projectiveTensorChartDiagramIso G φ hφ d).hom ≫
        projectiveTensorGradedModuleChartMap (B := B) G H f hf d := by
  letI := φ.toAlgebra
  letI : Module.Flat R B := hφ
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b u =>
    change (projectiveTensorChartComponentIso H φ hφ T d).hom.hom
        (((ModuleCat.extendScalars φ).map
          ((projectiveNatGradedModuleChartMap G H f hf d).app T)).hom (b ⊗ₜ[R,φ] u)) =
      ((projectiveTensorGradedModuleChartMap (B := B) G H f hf d).app T).hom
        ((projectiveTensorChartComponentIso G φ hφ T d).hom.hom (b ⊗ₜ[R,φ] u))
    rw [ModuleCat.ExtendScalars.map_tmul,
      projectiveTensorChartComponentIso_hom_tmul, projectiveTensorChartComponentIso_hom_tmul]
    exact projectiveTensorChartLinearEquiv_map (R := R) (B := B) (M := M) (N := N)
      (ι := ι) G H f hf T d b u
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end SerrePositivity.AlgebraicGeometry
