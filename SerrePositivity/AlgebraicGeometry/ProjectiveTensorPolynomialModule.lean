module

public import SerrePositivity.AlgebraicGeometry.TensorCoefficientAlgebraModule
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
概要：基底変更した加群 M⊗_R B に、B[X] の実際の作用を入れる。
方針：B⊗_R R[X] の作用を、多項式環のテンソル比較で移す。
規約：元の R[X] の作用と右係数 B の作用を共に保つ。
使われ方：基底変更後の次数付き加群の標準開を、テンソル係数の図式と照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R B M N ι : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]

local instance projectiveTensorPolyCoefficientModule : Module B (M ⊗[R] B) :=
  tensorRightCoefficientModule
local instance projectiveTensorPolyTensorModule :
    Module (B ⊗[R] MvPolynomial ι R) (M ⊗[R] B) :=
  tensorRightCoefficientAlgebraModule

/-- 基底変更後の実際の多項式加群構造。 -/
@[instance_reducible]
def projectiveTensorPolynomialModule : Module (MvPolynomial ι B) (M ⊗[R] B) :=
  Module.compHom _ (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R B).symm.toRingHom

local instance projectiveTensorPolyLocalModule : Module (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomialModule

/-- 係数変更した多項式の作用は、元の多項式の作用と一致する。 -/
theorem projectiveTensorPolynomial_map_smul (p : MvPolynomial ι R) (z : M ⊗[R] B) :
    MvPolynomial.map (algebraMap R B) p • z = p • z := by
  change (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R B).symm
    (MvPolynomial.map (algebraMap R B) p) • z = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_map,
    tensorRightCoefficientAlgebra_tmul_smul, one_smul]

/-- 定数多項式の作用は、右係数 B の作用に一致する。 -/
theorem projectiveTensorPolynomial_C_smul (b : B) (z : M ⊗[R] B) :
    MvPolynomial.C (σ := ι) b • z = b • z := by
  have hb : (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R B).symm
      (MvPolynomial.C b) = b ⊗ₜ[R] (1 : MvPolynomial ι R) := by
    exact (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R B).symm.commutes b
  change (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R B).symm (MvPolynomial.C b) • z = _
  rw [hb, tensorRightCoefficientAlgebra_tmul_smul, one_smul]

/-- 単項式の作用は、元の単項式の作用と右係数の乗法で計算できる。 -/
theorem projectiveTensorPolynomial_monomial_tmul (d : ι →₀ ℕ) (b c : B) (m : M) :
    MvPolynomial.monomial d b • (m ⊗ₜ[R] c) =
      (MvPolynomial.monomial d (1 : R) • m) ⊗ₜ[R] (b * c) := by
  change (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R B).symm
    (MvPolynomial.monomial d b) • (m ⊗ₜ[R] c) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_monomial,
    tensorRightCoefficientAlgebra_tmul_tmul]

/-- B[X] の作用は、右係数 B の作用を拡張する。 -/
theorem projectiveTensorPolynomial_coefficient_scalarTower :
    IsScalarTower B (MvPolynomial ι B) (M ⊗[R] B) :=
  IsScalarTower.of_algebraMap_smul (projectiveTensorPolynomial_C_smul (ι := ι))

local instance projectiveTensorPolyLocalCoefficientTower :
    IsScalarTower R B (M ⊗[R] B) := tensorRightCoefficient_scalarTower

/-- B[X] の作用は、元の基底 R の作用と両立する。 -/
theorem projectiveTensorPolynomial_base_scalarTower :
    IsScalarTower R (MvPolynomial ι B) (M ⊗[R] B) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r z
  change MvPolynomial.C (algebraMap R B r) • z = r • z
  rw [projectiveTensorPolynomial_C_smul, algebraMap_smul B]

local instance projectiveTensorPolyRingAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra

/-- 基底変更後の多項式作用は、元の R[X] の作用と両立する。 -/
theorem projectiveTensorPolynomial_polynomial_scalarTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) (M ⊗[R] B) :=
  IsScalarTower.of_algebraMap_smul (projectiveTensorPolynomial_map_smul (ι := ι))

/-- 元の多項式加群の射を、基底変更後の B[X] 線形な射へ送る。 -/
def projectiveTensorPolynomialMap (f : M →ₗ[MvPolynomial ι R] N) :
    M ⊗[R] B →ₗ[MvPolynomial ι B] N ⊗[R] B where
  toFun := tensorRightCoefficientAlgebraMap (B := B) f
  map_add' := (tensorRightCoefficientAlgebraMap (B := B) f).map_add
  map_smul' p z := (tensorRightCoefficientAlgebraMap (B := B) f).map_smul
    ((MvPolynomial.algebraTensorAlgEquiv (σ := ι) R B).symm p) z

/-- 基底変更後の多項式加群の射は、純テンソルの元の因子だけに作用する。 -/
theorem projectiveTensorPolynomialMap_tmul (f : M →ₗ[MvPolynomial ι R] N) (m : M) (b : B) :
    projectiveTensorPolynomialMap f (m ⊗ₜ[R] b) = f m ⊗ₜ[R] b := rfl

end SerrePositivity.AlgebraicGeometry
