module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LinearMapTensorImage
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
概要：KST §5、Stacks 0815 の有限自由加群を標的とする写像の基底変更。
方針：有限直積とテンソル積の同型を使い、係数環上のベクトルを標的とする。
規約：列の有限添字集合を固定する。
使われ方：行列式中心での純変換の自由化。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R C M ι : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  (g : M →ₗ[R] (ι → R))

/--
概要：有限自由加群への写像を基底変更し、係数環上のベクトルを標的とする。
方針：基底変更と有限直積に関するテンソル積の同型を合成する。
規約：KST §5、Stacks 0815、基底変更の平坦性は不要。
使われ方：純変換をチャート上の像加群に同定する写像。
-/
def linearMapTensorToPi : C ⊗[R] M →ₗ[C] (ι → C) :=
  (TensorProduct.piScalarRight R C C ι).toLinearMap ∘ₗ g.baseChange C

/--
概要：ベクトルへの基底変更写像の純テンソル上の値。
方針：有限直積のテンソル同型の公式を使う。
規約：KST §5、Stacks 0815、ベクトルの成分ごとに係数を移す。
使われ方：像加群の列による生成の検証。
-/
@[simp] theorem linearMapTensorToPi_tmul (c : C) (m : M) :
    linearMapTensorToPi g (c ⊗ₜ m) = fun i => c * algebraMap R C (g m i) := by
  ext i
  simp [linearMapTensorToPi, TensorProduct.piScalarRightHom_tmul, Algebra.smul_def, mul_comm]

/--
概要：冪倍の左逆元を持つ写像の基底変更の核は同じ冪で消える。
方針：基底変更の関手性で合成式を移し、直積のテンソル同型で核を検出する。
規約：KST §5、Stacks 0815、基礎環の任意のスカラーを許す。
使われ方：行列式中心上の像加群と純変換の比較。
-/
theorem linearMapTensorToPi_ker_annihilated
    (h : (ι → R) →ₗ[R] M) (r : R) (hh : h.comp g = r • LinearMap.id)
    (z : C ⊗[R] M) (hz : linearMapTensorToPi g z = 0) :
    algebraMap R C r • z = 0 := by
  have hgzero : g.baseChange C z = 0 := by
    apply (TensorProduct.piScalarRight R C C ι).injective
    exact hz.trans (map_zero _).symm
  have heq := congrArg (fun k : M →ₗ[R] M => k.baseChange C) hh
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_smul, LinearMap.baseChange_id] at heq
  have hz' := LinearMap.congr_fun heq z
  simpa only [LinearMap.comp_apply, hgzero, map_zero, LinearMap.smul_apply,
    LinearMap.id_apply, algebraMap_smul] using hz'.symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
