module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraModuleFinite
public import SerrePositivity.AlgebraicGeometry.BoundaryTorsionFiniteAlgebra
public import Mathlib.RingTheory.FiniteStability

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の有限型加群の基底変更後の境界ねじれの一様性。
方針：基底変更代数の Noether 性と基底変更加群の同代数上の有限性を使う。
規約：元の加群の基礎環上の有限性は要求しない。
使われ方：有限型の一般形でチャート上の追加基底変更を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：Noether 係数環への基底変更後、有限型代数上有限な加群の境界ねじれは一様な冪で消える。
方針：C ⊗_R B の Noether 性と C ⊗_R M の同代数上の有限性から一様な指数を得る。
規約：KST §5、Stacks 0815, Theorem 38.30.7、境界元は C の任意の元。
使われ方：一般の有限型特殊形の純変換の基底変更安定性。
-/
theorem tensorAlgebraModule_boundaryTorsion_bounded
    (R B C M : Type*) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [Module.Finite B M] [Algebra.FiniteType R B] [IsNoetherianRing C]
    (f : C) :
    ∃ n : ℕ, ∀ z ∈ boundaryTorsion f (C ⊗[R] M), f ^ n • z = 0 := by
  let : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
  have : Module.Finite (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule_finite R B C M
  have : IsScalarTower C (C ⊗[R] B) (C ⊗[R] M) :=
    tensorAlgebraModule_isScalarTower_left R B C M
  have : Algebra.FiniteType C (C ⊗[R] B) := inferInstance
  have : IsNoetherianRing (C ⊗[R] B) := Algebra.FiniteType.isNoetherianRing C _
  exact exists_pow_annihilates_boundaryTorsion_of_finite_algebra (B := C ⊗[R] B) f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
