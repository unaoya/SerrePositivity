module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FreeLocusLocalizationBaseChange
public import Mathlib.RingTheory.Localization.BaseChange
public import SerrePositivity.AlgebraicGeometry.TensorCoefficientLocalization

/-!
概要：KST §5、Stacks 0811 の任意の実現の局所化加群に対する自由 locus の比較。
方針：局所化写像の基底変更同型で標準テンソル表示へ戻す。
規約：加群の局所化の実現を固定せず、実際の線形写像を保持する。
使われ方：係数局所化後の純変換の自由性を元の自由 locus へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：任意の局所化加群の自由 locus は元の加群の自由 locus の逆像。
方針：局所化写像の基底変更同型と、テンソル表示での自由 locus の局所化比較を使う。
規約：KST §5、Stacks 0811、有限性・Noether 性・加群の平坦性は不要。
使われ方：純変換の係数局所化の自由性を基底の基本開から戻す。
-/
theorem mem_freeLocus_iff_of_isLocalizedModule
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N]
    (S : Submonoid R) [IsLocalization S A]
    (η : M →ₗ[R] N) [IsLocalizedModule S η] (Q : PrimeSpectrum A) :
    Q ∈ Module.freeLocus A N ↔
      Q.comap (algebraMap R A) ∈ Module.freeLocus R M := by
  let E := (IsLocalizedModule.isBaseChange S A η).equiv
  rw [← Module.freeLocus_congr E]
  exact mem_freeLocus_baseChange_iff_of_isLocalization S Q

/--
概要：係数局所化後の基底変更加群の純変換の自由性は縮約素点での元の純変換の自由性と同値。
方針：純変換の係数変更写像が加群の局所化であることを自由 locus の比較へ渡す。
規約：KST §5、Stacks 0811、境界の正則性と加群の有限性は不要。
使われ方：自由化基本開の存在を基礎環の基本開ごとに照合する。
-/
theorem mem_freeLocus_tensorPureTransform_iff_of_isLocalization
    (R A B M : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M] (S : Submonoid A) [IsLocalization S B]
    (f : A) (Q : PrimeSpectrum B) :
    Q ∈ Module.freeLocus B
        (modulePureTransform (algebraMap A B f) (B ⊗[R] M)) ↔
      Q.comap (algebraMap A B) ∈
        Module.freeLocus A (modulePureTransform f (A ⊗[R] M)) :=
  mem_freeLocus_iff_of_isLocalizedModule S
    (tensorPureTransformLocalizationMap R A B M f) Q

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
