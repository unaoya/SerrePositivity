module

public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorChartComparison
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFlatBaseChange

/-!
概要：標準開のテンソル比較を、基底変更後の係数図式の自然同型にする。
方針：純テンソル分数で制限射との可換性を示し、有限交叉の図式へまとめる。
規約：変更後の図式は B[X] 加群の実際の指定次数の斉次局所化。
使われ方：flat な Čech 底変換を、実際の標準開の Čech 計算へ接続する。
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
local instance projectiveTensorDiagramCoefficientModule {V : Type*}
    [AddCommGroup V] [Module R V] : Module B (V ⊗[R] B) := tensorRightCoefficientModule
local instance projectiveTensorDiagramCoefficientTower {V : Type*}
    [AddCommGroup V] [Module R V] : IsScalarTower R B (V ⊗[R] B) :=
  tensorRightCoefficient_scalarTower
local instance projectiveTensorDiagramPolynomialModule :
    Module (MvPolynomial ι B) (M ⊗[R] B) := projectiveTensorPolynomialModule
local instance projectiveTensorDiagramBPolynomialTower :
    IsScalarTower B (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_coefficient_scalarTower
local instance projectiveTensorDiagramRPolynomialTower :
    IsScalarTower R (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_base_scalarTower
local instance projectiveTensorDiagramPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance projectiveTensorDiagramPolynomialRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R B r) =
    MvPolynomial.map (algebraMap R B) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]
local instance projectiveTensorDiagramPolynomialTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_polynomial_scalarTower

variable (G : ℕ → Submodule R M)


variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance projectiveTensorDiagramGradedAction :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (projectiveTensorPiece (B := B) G) := projectiveTensorPiece_gradedSMul (ι := ι) G
local instance projectiveTensorDiagramIntGradedAction :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt G) := projectiveNatGradingIntSMul (ι := ι) G

/-- 各標準開のテンソル比較は、標準開を狭める制限と可換。 -/
theorem projectiveTensorChartLinearEquiv_restriction [Module.Flat R B]
    (d : ℤ) {T U : Finset ι} (h : T ⟶ U) (b : B)
    (u : (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) :
    projectiveTensorChartLinearEquiv G U d
        (b ⊗ₜ[R] ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).map h).hom u) =
      ((projectiveTensorGradedModuleChartDiagram (B := B) (ι := ι) G d).map h).hom
        (projectiveTensorChartLinearEquiv G T d (b ⊗ₜ[R] u)) := by
  let V (k : ℕ) := projectiveNatGradingInt G (d + k • (T.card : ℤ))
  let W (k : ℕ) := projectiveNatGradingInt G (d + k • (U.card : ℤ))
  obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff
    (projectiveLaurentDenominator R T) V
    (projectiveGradedChart_mul_denominator (projectiveNatGradingInt G) T d) u.val).mp u.property
  let a := projectiveLaurentDenominator R (U \ T)
  let mU : W n := ⟨a ^ n • m.val,
    projectiveGradedChart_mul_mem (projectiveNatGradingInt G) (leOfHom h) d n m⟩
  let uU := ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).map h).hom u
  have hmu : uU.val = projectiveGradedFraction (projectiveLaurentDenominator R U) W n mU := by
    change projectiveModuleAwayRestriction
      (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
        ⟨a, (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm⟩) u.val = _
    rw [← hm, projectiveGradedFraction_apply, projectiveGradedFraction_apply,
      projectiveModuleAwayRestriction_mk (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm]
  apply Subtype.ext
  change (projectiveTensorChartLinearEquiv G U d (b ⊗ₜ[R] uU)).val =
    projectiveModuleAwayRestriction
      (show projectiveLaurentDenominator B T ∣ projectiveLaurentDenominator B U from
        ⟨projectiveLaurentDenominator B (U \ T),
          (projectiveLaurentDenominator_sdiff B (leOfHom h)).symm⟩)
      (projectiveTensorChartLinearEquiv G T d (b ⊗ₜ[R] u)).val
  rw [projectiveTensorChartLinearEquiv_fraction G U d n mU b uU hmu,
    projectiveTensorChartLinearEquiv_fraction G T d n m b u hm.symm,
    projectiveModuleAwayRestriction_mk (projectiveLaurentDenominator_sdiff B (leOfHom h)).symm]
  congr 1
  change (a ^ n • m.val) ⊗ₜ[R] b =
    (projectiveLaurentDenominator B (U \ T)) ^ n • (m.val ⊗ₜ[R] b)
  rw [← projectivePolynomialCoefficientDenominator (R := R) (B := B) (U \ T),
    ← map_pow, algebraMap_smul (MvPolynomial ι B)]
  rfl

/-- 環準同型から係数構造を固定した、各標準開の実際のテンソル比較。 -/
def projectiveTensorChartComponentIso (φ : R →+* B) (hφ : φ.Flat)
    (T : Finset ι) (d : ℤ) :
    letI := φ.toAlgebra
    (ModuleCat.extendScalars φ).obj ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) ≅
      (projectiveTensorGradedModuleChartDiagram (B := B) (ι := ι) G d).obj T := by
  letI := φ.toAlgebra
  letI : Module.Flat R B := hφ
  exact (projectiveTensorChartLinearEquiv (B := B) (ι := ι) G T d).toModuleIso

/-- 各標準開の環準同型による比較は、左純テンソルの既存の比較と一致する。 -/
theorem projectiveTensorChartComponentIso_hom_tmul (φ : R →+* B) (hφ : φ.Flat)
    (T : Finset ι) (d : ℤ) (b : B)
    (u : (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) :
    letI := φ.toAlgebra
    letI : Module.Flat R B := hφ
    (projectiveTensorChartComponentIso G φ hφ T d).hom.hom
        (b ⊗ₜ[R,φ] u) = projectiveTensorChartLinearEquiv G T d (b ⊗ₜ[R] u) := rfl

/-- 元の標準開図式のテンソル底変換と、基底変更後の実際の標準開図式との自然同型。 -/
def projectiveTensorChartDiagramIso (φ : R →+* B) (hφ : φ.Flat) (d : ℤ) :
    letI := φ.toAlgebra
    projectiveNatGradedModuleChartDiagram (ι := ι) G d ⋙
        ModuleCat.extendScalars φ ≅
      projectiveTensorGradedModuleChartDiagram (B := B) (ι := ι) G d := by
  letI := φ.toAlgebra
  letI : Module.Flat R B := hφ
  exact NatIso.ofComponents (fun T ↦ projectiveTensorChartComponentIso G φ hφ T d) (by
    intro T U h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b u =>
      change (projectiveTensorChartComponentIso G φ hφ U d).hom.hom
          (((ModuleCat.extendScalars φ).map
            ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).map h)).hom (b ⊗ₜ[R,φ] u)) =
        ((projectiveTensorGradedModuleChartDiagram (B := B) (ι := ι) G d).map h).hom
          ((projectiveTensorChartComponentIso G φ hφ T d).hom.hom (b ⊗ₜ[R,φ] u))
      rw [ModuleCat.ExtendScalars.map_tmul,
        projectiveTensorChartComponentIso_hom_tmul, projectiveTensorChartComponentIso_hom_tmul]
      exact projectiveTensorChartLinearEquiv_restriction (R := R) (B := B) (M := M)
        (ι := ι) G d h b u
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

end SerrePositivity.AlgebraicGeometry
