module

public import SerrePositivity.AlgebraicGeometry.TensorCoefficientRightModule

/-!
概要：M⊗_R B の二つの作用を、B⊗_R P の作用にまとめる。
方針：P は左因子、B は右因子に作用することから可換性を示す。
規約：元の R と P の作用を保ち、係数の作用だけを追加する。
使われ方：基底変更後の多項式加群に B[X] の作用を入れる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R B P M N : Type*} [CommRing R] [CommRing B] [CommRing P]
variable [Algebra R B] [Algebra R P]
variable [AddCommGroup M] [Module R M] [Module P M] [IsScalarTower R P M]
variable [AddCommGroup N] [Module R N] [Module P N] [IsScalarTower R P N]
local instance tensorCoefficientAlgebraLocalB : Module B (M ⊗[R] B) :=
  tensorRightCoefficientModule
local instance tensorCoefficientAlgebraLocalTower : IsScalarTower R B (M ⊗[R] B) :=
  tensorRightCoefficient_scalarTower

/-- 左因子の P 作用と右係数 B の作用は可換。 -/
theorem tensorRightCoefficient_smulCommClass : SMulCommClass B P (M ⊗[R] B) where
  smul_comm b p z := by
    induction z using TensorProduct.inductionOn with
    | tmul m c =>
      change b • ((p • m) ⊗ₜ[R] c) = p • (b • (m ⊗ₜ[R] c))
      rw [tensorRightCoefficient_smul_tmul, tensorRightCoefficient_smul_tmul]
      rfl
    | add x y hx hy => simp only [smul_add, hx, hy]

local instance tensorCoefficientAlgebraLocalCommute : SMulCommClass B P (M ⊗[R] B) :=
  tensorRightCoefficient_smulCommClass

/-- 二つの可換な作用をまとめた、B⊗_R P 上の加群構造。 -/
@[instance_reducible]
def tensorRightCoefficientAlgebraModule : Module (B ⊗[R] P) (M ⊗[R] B) :=
  TensorProduct.Algebra.module (R := R) (A := B) (B := P) (M := M ⊗[R] B)

local instance tensorCoefficientAlgebraLocalModule : Module (B ⊗[R] P) (M ⊗[R] B) :=
  tensorRightCoefficientAlgebraModule

/-- テンソル代数の純テンソルの作用は、元の二つの作用の合成。 -/
theorem tensorRightCoefficientAlgebra_tmul_smul (b : B) (p : P) (z : M ⊗[R] B) :
    (b ⊗ₜ[R] p) • z = b • p • z := rfl

/-- 二重の純テンソル上の作用は、元の P 作用と B の乗法で計算できる。 -/
theorem tensorRightCoefficientAlgebra_tmul_tmul (b c : B) (p : P) (m : M) :
    (b ⊗ₜ[R] p) • (m ⊗ₜ[R] c) = (p • m) ⊗ₜ[R] (b * c) := by
  rw [tensorRightCoefficientAlgebra_tmul_smul]
  exact tensorRightCoefficient_smul_tmul b (p • m) c

/-- テンソル代数の作用は、右係数 B の作用を拡張する。 -/
theorem tensorRightCoefficientAlgebra_coefficient_scalarTower :
    IsScalarTower B (B ⊗[R] P) (M ⊗[R] B) := by
  apply IsScalarTower.of_algebraMap_smul
  intro b z
  change (b ⊗ₜ[R] (1 : P)) • z = b • z
  rw [tensorRightCoefficientAlgebra_tmul_smul, one_smul]

/-- テンソル代数の作用は、元の基底 R の作用と両立する。 -/
theorem tensorRightCoefficientAlgebra_scalarTower :
    IsScalarTower R (B ⊗[R] P) (M ⊗[R] B) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r z
  change (algebraMap R B r ⊗ₜ[R] (1 : P)) • z = r • z
  rw [tensorRightCoefficientAlgebra_tmul_smul, one_smul, algebraMap_smul B]

/-- P 線形な写像は、係数変更後のテンソル代数上でも線形。 -/
def tensorRightCoefficientAlgebraMap (f : M →ₗ[P] N) :
    M ⊗[R] B →ₗ[B ⊗[R] P] N ⊗[R] B where
  toFun := (f.restrictScalars R).rTensor B
  map_add' := ((f.restrictScalars R).rTensor B).map_add
  map_smul' r z := by
    induction r using TensorProduct.inductionOn with
    | tmul b p =>
      simp only [RingHom.id_apply, tensorRightCoefficientAlgebra_tmul_smul]
      change tensorRightCoefficientMap (f.restrictScalars R) (b • p • z) =
        b • p • tensorRightCoefficientMap (f.restrictScalars R) z
      rw [(tensorRightCoefficientMap (f.restrictScalars R)).map_smul]
      congr 1
      exact (TensorProduct.AlgebraTensorModule.rTensor R B f).map_smul p z
    | add x y hx hy => simp only [add_smul, map_add, hx, hy]

end SerrePositivity.AlgebraicGeometry
