module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
概要：KST §5、Stacks 0815 の自由化した基底変更からの自由性の移送。
方針：テンソル積の係数の打ち消し同型で自由な加群を移す。
規約：中間係数環 B と最終係数環 K を区別する。
使われ方：境界外の自由な基本開からチャートの境界外への自由性の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：中間の基底変更加群がさらに係数拡大で自由になれば元の加群の同じ係数拡大も自由。
方針：基底変更の同型とテンソル積の係数の打ち消し同型を合成する。
規約：KST §5、Stacks 0815、自由性は最終の係数環について仮定する。
使われ方：二段の局所化を経由してチャートの境界外を自由にする。
-/
theorem free_tensor_of_free_baseChange
    {R B K M N : Type*} [CommRing R] [CommRing B] [CommRing K]
    [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module B N] [IsScalarTower R B N] (μ : M →ₗ[R] N) (hμ : IsBaseChange B μ)
    [Module.Free K (K ⊗[B] N)] : Module.Free K (K ⊗[R] M) := by
  let e := (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) hμ.equiv.symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B K K M)
  exact Module.Free.of_equiv e

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
