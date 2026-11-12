module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
概要：通常の代数のテンソル積と extendScalars のスカラー作用を明示的に比較する。
方針：両因子の恒等線形同型でテンソル積を移す。
規約：元に対しては恒等だが、基底環の作用の表示を区別する。
使われ方：Čech の切断部分代数と実際の複体の底変換。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open TensorProduct
open scoped TensorProduct ChangeOfRings
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (M : ModuleCat.{u} R)

local instance tensorExtendScalarTower :
    IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) where
  smul_assoc r a b := by
    change (r • a) * (show A from b) = (algebraMap R A r) * (a * (show A from b))
    rw [Algebra.smul_def, mul_assoc]

/-- 通常の代数のテンソル積と、圏論的なスカラー拡大の比較。 -/
def tensorExtendScalarsEquiv :
    A ⊗[R] M ≃ₗ[A] (ModuleCat.extendScalars (algebraMap R A)).obj M :=
  AlgebraTensorModule.congr (LinearEquiv.refl A A) (LinearEquiv.refl R M)

/-- 比較は純テンソルの二つの因子を保つ。 -/
theorem tensorExtendScalarsEquiv_tmul (a : A) (m : M) :
    tensorExtendScalarsEquiv M (a ⊗ₜ[R] m) = a ⊗ₜ[R,algebraMap R A] m := rfl

end SerrePositivity.AlgebraicGeometry
