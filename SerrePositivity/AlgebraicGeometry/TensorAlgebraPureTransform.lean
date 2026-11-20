module

public import SerrePositivity.AlgebraicGeometry.PureTransformScalarRestriction
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraModuleFinite
public import Mathlib.RingTheory.FiniteStability

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の基底変更代数上の純変換の有限表示性と基礎環上の表示。
方針：基底変更代数上の商を取り、スカラー制限で基礎環上の純変換と比較する。
規約：基底変更代数の作用は明示的に選ぶ。
使われ方：一般の有限型特殊形の純変換を有限型の加群として扱う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable (R B C M : Type*) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M] [Module B M]
  [IsScalarTower R B M]

/--
概要：基底変更代数上の商による純変換と係数環 C 上の純変換の実際の線形同型。
方針：明示的な代数作用のスカラー塔で商のスカラー制限の同型を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、境界元は C の元。
使われ方：平坦性と有限表示性を異なる係数環について照合する。
-/
def tensorAlgebraPureTransformEquiv (f : C) :
    letI : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
    letI : IsScalarTower C (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule_isScalarTower_left R B C M
    modulePureTransform f (C ⊗[R] M) ≃ₗ[C]
      modulePureTransform (algebraMap C (C ⊗[R] B) f) (C ⊗[R] M) := by
  letI : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
  letI : IsScalarTower C (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule_isScalarTower_left R B C M
  exact modulePureTransformScalarRestrictionEquiv (B := C ⊗[R] B) (M := C ⊗[R] M) f

/--
概要：有限型代数上有限な加群の基底変更の純変換は基底変更代数上有限表示。
方針：同代数の Noether 性、元の基底変更加群の有限性、商の有限表示性を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、Noether 条件は C に課す。
使われ方：チャート上の純変換の有限型・有限表示条件。
-/
theorem tensorAlgebraPureTransform_finitePresentation [Module.Finite B M]
    [Algebra.FiniteType R B] [IsNoetherianRing C] (f : C) :
    letI : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
    Module.FinitePresentation (C ⊗[R] B)
      (modulePureTransform (algebraMap C (C ⊗[R] B) f) (C ⊗[R] M)) := by
  let : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
  have : Module.Finite (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule_finite R B C M
  have : IsNoetherianRing (C ⊗[R] B) := Algebra.FiniteType.isNoetherianRing C _
  exact modulePureTransform_finitePresentation (algebraMap C (C ⊗[R] B) f) (C ⊗[R] M)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
