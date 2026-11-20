module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BoundaryTorsionFiniteAlgebra
public import SerrePositivity.AlgebraicGeometry.FlatPureTransformBaseChangeOfBound

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の代数上有限な加群の平坦な純変換の追加基底変更。
方針：拡大環の Noether 性から境界ねじれの一様な指数を得て比較同型を作る。
規約：基礎環上の有限性は要求せず、拡大環上の有限性を使う。
使われ方：有限型代数上の有限加群の局所平坦化を共通細分で保存する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R : Type*} [CommRing R] (B C : Type*) [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] (f : R) (M : Type*) [AddCommGroup M]
  [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
  [Module.Flat R (modulePureTransform f M)]

include B

/--
概要：Noether 代数上有限な加群の純変換は追加基底変更で元の平坦な商の基底変更と同型。
方針：拡大環上で一様に消える境界ねじれの指数を選び、比較同型を適用する。
規約：KST §5、Stacks 0815, Theorem 38.30.7、境界の像は追加係数環で正則。
使われ方：基礎環上有限ではない加群に対する純変換の比較。
-/
def finiteAlgebraFlatPureTransformBaseChangeEquiv [IsNoetherianRing B]
    (hf : IsRegular (algebraMap R C f)) :
    modulePureTransform (algebraMap R C f) (C ⊗[R] M) ≃ₗ[C]
      C ⊗[R] modulePureTransform f M := by
  let n := Classical.choose
    (exists_pow_annihilates_boundaryTorsion_of_finite_algebra (B := B) (M := M) f)
  have hn := Classical.choose_spec
    (exists_pow_annihilates_boundaryTorsion_of_finite_algebra (B := B) (M := M) f)
  exact flatPureTransformBaseChangeEquivOfBound C f M n hn hf

/--
概要：Noether 代数上有限な加群の平坦な純変換は追加基底変更後も平坦。
方針：元の平坦な商の基底変更との実際の線形同型で平坦性を移す。
規約：KST §5、Stacks 0815, Theorem 38.30.7、有限性は B 加群としての有限性。
使われ方：一般の有限型特殊形の局所平坦化の安定性。
-/
theorem finiteAlgebraFlatPureTransform_baseChange [IsNoetherianRing B]
    (hf : IsRegular (algebraMap R C f)) :
    Module.Flat C (modulePureTransform (algebraMap R C f) (C ⊗[R] M)) :=
  Module.Flat.of_linearEquiv (finiteAlgebraFlatPureTransformBaseChangeEquiv B C f M hf)

/--
概要：Noether 基礎環の有限型代数上有限な加群の平坦な純変換は追加基底変更後も平坦。
方針：有限型代数の Noether 性を導いて比較同型を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、元の加群の基礎環上の有限性を仮定しない。
使われ方：Raynaud–Gruson の Noether・有限型特殊形の純変換の比較。
-/
theorem finiteTypeFlatPureTransform_baseChange [IsNoetherianRing R] [Algebra.FiniteType R B]
    (hf : IsRegular (algebraMap R C f)) :
    Module.Flat C (modulePureTransform (algebraMap R C f) (C ⊗[R] M)) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  exact finiteAlgebraFlatPureTransform_baseChange B C f M hf

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
