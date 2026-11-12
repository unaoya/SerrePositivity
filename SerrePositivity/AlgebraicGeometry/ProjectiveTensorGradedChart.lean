module

public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMap
public import Mathlib.RingTheory.Flat.Basic

/-!
概要：基底変更した B[X] 加群の実際の標準開図式と、次数付き射を構成する。
方針：テンソル像の次数付き作用を使い、既存の斉次局所化の図式へ渡す。
規約：テンソル係数の旧図式との同型は別に示す。ここで両図式を同一視しない。
使われ方：flat な Čech 底変換の比較先を、基底変更後の標準開へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct
universe u
variable {R B M N : Type u} {ι : Type} [CommRing R] [CommRing B] [Algebra R B]
variable [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]

local instance projectiveTensorChartCoefficientModule {V : Type u}
    [AddCommGroup V] [Module R V] : Module B (V ⊗[R] B) := tensorRightCoefficientModule
local instance projectiveTensorChartPolynomialModule :
    Module (MvPolynomial ι B) (M ⊗[R] B) := projectiveTensorPolynomialModule
local instance projectiveTensorChartPolynomialTower :
    IsScalarTower B (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_coefficient_scalarTower

variable (G : ℕ → Submodule R M)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance projectiveTensorChartGradedAction :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (projectiveTensorPiece (B := B) G) := projectiveTensorPiece_gradedSMul (ι := ι) G

/-- 基底変更後の B[X] 加群の、指定次数の実際の標準開図式。 -/
def projectiveTensorGradedModuleChartDiagram (d : ℤ) : Finset ι ⥤ ModuleCat.{u} B :=
  projectiveNatGradedModuleChartDiagram (ι := ι) (projectiveTensorPiece (B := B) G) d

/-- flat な基底変更では、元の次数成分のテンソル積は全体のテンソル積に単射。 -/
theorem projectiveTensorPiece_injective [Module.Flat R B] (j : ℕ) :
    Function.Injective (tensorRightCoefficientMap (B := B) (G j).subtype) :=
  Module.Flat.rTensor_preserves_injective_linearMap (G j).subtype Subtype.val_injective

/-- flat な基底変更後の次数成分は、元の次数成分のテンソル積と同型。 -/
def projectiveTensorPieceEquiv [Module.Flat R B] (j : ℕ) :
    (G j) ⊗[R] B ≃ₗ[B] projectiveTensorPiece (B := B) G j :=
  LinearEquiv.ofBijective (tensorRightCoefficientMap (B := B) (G j).subtype).rangeRestrict
    ⟨fun _ _ h ↦ projectiveTensorPiece_injective (B := B) G j (Subtype.ext_iff.mp h),
      LinearMap.surjective_rangeRestrict _⟩

/-- 次数成分の比較は、純テンソルの元を同じ元へ送る。 -/
theorem projectiveTensorPieceEquiv_tmul [Module.Flat R B] (j : ℕ) (m : G j) (b : B) :
    (projectiveTensorPieceEquiv (B := B) G j (m ⊗ₜ[R] b)).val = m.val ⊗ₜ[R] b := rfl

section Naturality
variable (H : ℕ → Submodule R N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : M →ₗ[MvPolynomial ι R] N) (hf : ∀ j, ∀ m ∈ G j, f m ∈ H j)

/-- 次数付き加群の射から、基底変更後の実際の標準開図式の射を得る。 -/
def projectiveTensorGradedModuleChartMap (d : ℤ) :=
  projectiveNatGradedModuleChartMap (projectiveTensorPiece (B := B) G)
    (projectiveTensorPiece (B := B) H) (projectiveTensorPolynomialMap (B := B) f)
    (projectiveTensorPiece_map_mem G H f hf) d

end Naturality
end SerrePositivity.AlgebraicGeometry
