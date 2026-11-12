module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
概要：M⊗_R B に、右の係数環 B の作用を明示する。
方針：テンソル積の交換同型で B⊗_R M の作用を移し、純テンソルで計算する。
規約：元の R 作用は保ち、B の作用だけを追加する。
使われ方：局所化と右テンソル積の比較を、B 線形な標準開の比較へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R B M N : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 右係数のテンソル積に、交換同型から B 加群構造を入れる。 -/
@[instance_reducible]
def tensorRightCoefficientModule : Module B (M ⊗[R] B) :=
  (TensorProduct.comm R M B).toAddEquiv.module B

local instance tensorRightCoefficientLocalModule : Module B (M ⊗[R] B) :=
  tensorRightCoefficientModule

/-- 係数 B の作用は、純テンソルの右因子への乗法で計算できる。 -/
theorem tensorRightCoefficient_smul_tmul (b : B) (m : M) (c : B) :
    b • (m ⊗ₜ[R] c) = m ⊗ₜ[R] (b * c) := by
  change (TensorProduct.comm R B M)
    (b • ((TensorProduct.comm R M B) (m ⊗ₜ[R] c))) = _
  rw [TensorProduct.comm_tmul]
  change (TensorProduct.comm R B M) ((b * c) ⊗ₜ[R] m) = _
  exact TensorProduct.comm_tmul R B M (b * c) m

/-- 右係数の B 作用は、元の R 作用と両立する。 -/
theorem tensorRightCoefficient_scalarTower : IsScalarTower R B (M ⊗[R] B) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r z
  induction z using TensorProduct.inductionOn with
  | tmul m b =>
    rw [tensorRightCoefficient_smul_tmul]
    change m ⊗ₜ[R] (algebraMap R B r * b) = (r • m) ⊗ₜ[R] b
    rw [← Algebra.smul_def]
    exact (TensorProduct.smul_tmul r m b).symm
  | add x y hx hy => simp only [smul_add, hx, hy]

/-- テンソル積の交換同型は、右係数の B 加群構造について B 線形。 -/
def tensorRightCoefficientComm : (M ⊗[R] B) ≃ₗ[B] B ⊗[R] M :=
  (TensorProduct.comm R M B).toAddEquiv.linearEquiv B

/-- B 線形な交換同型の、純テンソル上の計算式。 -/
theorem tensorRightCoefficientComm_tmul (m : M) (b : B) :
    tensorRightCoefficientComm (m ⊗ₜ[R] b) = b ⊗ₜ[R] m :=
  TensorProduct.comm_tmul R M B m b

/-- 元の R 線形写像を、右係数テンソル積の B 線形写像として扱う。 -/
def tensorRightCoefficientMap (f : M →ₗ[R] N) : M ⊗[R] B →ₗ[B] N ⊗[R] B where
  toFun := f.rTensor B
  map_add' := (f.rTensor B).map_add
  map_smul' b z := by
    induction z using TensorProduct.inductionOn with
    | tmul m c =>
      simp only [RingHom.id_apply, tensorRightCoefficient_smul_tmul,
        LinearMap.rTensor_tmul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

end SerrePositivity.AlgebraicGeometry
