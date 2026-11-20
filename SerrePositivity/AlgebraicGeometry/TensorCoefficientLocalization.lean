module

public import SerrePositivity.AlgebraicGeometry.PureTransformBaseLocalization
public import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：KST §5、Stacks 0815 のチャート上の基底変更加群の係数局所化。
方針：係数写像の右テンソル積が局所化であることを使い、純変換の比較へ接続する。
規約：元の基礎環 R、チャート環 A、その局所化 B を区別する。
使われ方：行列式チャートの重なりで平坦性を移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable (R A B M : Type*) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [AddCommGroup M] [Module R M]

/--
概要：係数拡大による基底変更加群の間の実際の線形写像。
方針：係数環の代数写像に元の加群を右からテンソルする。
規約：KST §5、Stacks 0815、A 上線形な射とする。
使われ方：チャートの局所化に沿う純変換の比較。
-/
def tensorCoefficientLocalizationMap : A ⊗[R] M →ₗ[A] B ⊗[R] M :=
  TensorProduct.AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)

/--
概要：係数拡大のテンソル写像の純テンソル上の公式。
方針：右テンソル積の定義を使う。
規約：KST §5、Stacks 0815、元の加群の元はそのまま保持する。
使われ方：重なり上の元の加群からの写像の交換式。
-/
theorem tensorCoefficientLocalizationMap_tmul (a : A) (m : M) :
    tensorCoefficientLocalizationMap R A B M (a ⊗ₜ m) = algebraMap A B a ⊗ₜ m := rfl

/--
概要：係数環が局所化ならその係数拡大のテンソル写像も局所化。
方針：局所化写像の右テンソル積についての既存の普遍条件を使う。
規約：KST §5、Stacks 0815、元の加群の平坦性は不要。
使われ方：純変換の局所化の比較の入力。
-/
instance tensorCoefficientLocalizationMap_isLocalizedModule (S : Submonoid A)
    [IsLocalization S B] :
    IsLocalizedModule S (tensorCoefficientLocalizationMap R A B M) :=
  inferInstanceAs (IsLocalizedModule S
    (TensorProduct.AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)))

/--
概要：基底変更加群の純変換を係数局所化先の純変換へ送る比較写像。
方針：純変換の係数拡大の商写像をテンソル写像に適用する。
規約：KST §5、Stacks 0815、境界元はチャート環 A の元で指定する。
使われ方：異なる標準チャートの重なりでの比較。
-/
def tensorPureTransformLocalizationMap (f : A) :
    modulePureTransform f (A ⊗[R] M) →ₗ[A]
      modulePureTransform (algebraMap A B f) (B ⊗[R] M) :=
  pureTransformBaseLocalizationMap f (tensorCoefficientLocalizationMap R A B M)

/--
概要：基底変更加群の純変換の係数拡大写像は局所化。
方針：テンソル写像と純変換の局所化についての二つの普遍条件を合成する。
規約：KST §5、Stacks 0815、有限性を要求しない。
使われ方：一般チャートへの平坦性の移送。
-/
instance tensorPureTransformLocalizationMap_isLocalizedModule (S : Submonoid A)
    [IsLocalization S B] (f : A) :
    IsLocalizedModule S (tensorPureTransformLocalizationMap R A B M f) :=
  inferInstanceAs (IsLocalizedModule S
    (pureTransformBaseLocalizationMap (A := B) f (tensorCoefficientLocalizationMap R A B M)))

/--
概要：チャート上の平坦な純変換は係数環の局所化後にも平坦。
方針：純変換の係数局所化の平坦性保存を適用する。
規約：KST §5、Stacks 0815、平坦性は A と B についてそれぞれ主張する。
使われ方：自由な生成元チャートから重なりへの平坦性の移送。
-/
theorem tensorPureTransformLocalization_flat (S : Submonoid A) [IsLocalization S B]
    (f : A) [Module.Flat A (modulePureTransform f (A ⊗[R] M))] :
    Module.Flat B (modulePureTransform (algebraMap A B f) (B ⊗[R] M)) :=
  pureTransformBaseLocalization_flat S f (tensorCoefficientLocalizationMap R A B M)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
