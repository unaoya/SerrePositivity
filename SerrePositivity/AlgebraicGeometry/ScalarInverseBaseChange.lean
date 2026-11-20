module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
概要：KST §5、Stacks 0815 の分母倍の左逆元を持つ写像の基底変更。
方針：合成式を基底変更の関手性で移し、核の元に適用する。
規約：加群の平坦性を仮定しない。
使われ方：純変換とその追加基底変更の比較での核の消滅。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：スカラー倍の左逆元を持つ写像の基底変更の核は同じスカラーで消える。
方針：合成式を基底変更して核の元に適用する。
規約：KST §5、Stacks 0815、係数環の任意の拡大を扱う。
使われ方：平坦な純変換の追加 blowup に対する安定性。
-/
theorem baseChange_ker_annihilated_of_scalar_leftInverse
    {R C M N : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (h : N →ₗ[R] M) (r : R)
    (hh : h.comp g = r • LinearMap.id) (z : C ⊗[R] M) (hz : g.baseChange C z = 0) :
    algebraMap R C r • z = 0 := by
  have heq := congrArg (fun k : M →ₗ[R] M => k.baseChange C) hh
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_smul, LinearMap.baseChange_id] at heq
  have hz' := LinearMap.congr_fun heq z
  simpa only [LinearMap.comp_apply, hz, map_zero, LinearMap.smul_apply,
    LinearMap.id_apply, algebraMap_smul] using hz'.symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
