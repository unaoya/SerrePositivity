module

public import SerrePositivity.AlgebraicGeometry.PureTransformModule
public import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
概要：Stacks 0815 の加群の純変換は境界の補開集合上で元の加群と一致する。
方針：純変換を局所化へ埋め込み、その写像の局所化の普遍条件を証明する。
規約：境界元の正則性・Noether 性・平坦性をここでは仮定しない。
使われ方：KST §5、Stacks 081T の平坦化における開部分上の不変性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (f : R) (M : Type*) [AddCommGroup M] [Module R M]

/--
概要：純変換から元の加群の局所化への線形写像。
方針：局所化写像をその核による商へ降ろす。
規約：Stacks 0815、環上線形な写像として保持する。
使われ方：純変換の局所化の比較同型。
-/
def modulePureTransformToLocalization : modulePureTransform f M →ₗ[R]
    LocalizedModule (Submonoid.powers f) M :=
  (boundaryTorsion f M).liftQ
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M) le_rfl

/--
概要：純変換から局所化への写像は単射。
方針：局所化の核で割った商の消滅判定を使う。
規約：Stacks 0815、局所化への全射性は主張しない。
使われ方：純変換の局所化の普遍条件。
-/
theorem modulePureTransformToLocalization_injective :
    Function.Injective (modulePureTransformToLocalization f M) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact hx

/--
概要：元の加群の局所化は純変換の局所化でもある。
方針：境界元の可逆性・分母消去・単射性から普遍条件を確認する。
規約：Stacks 0815、局所化の写像は純変換からの写像を指定する。
使われ方：純変換が中心の外で元の加群を保つことの実証明。
-/
instance modulePureTransformToLocalization_isLocalizedModule :
    IsLocalizedModule.Away f (modulePureTransformToLocalization f M) := by
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · exact IsLocalizedModule.Away.isUnit_algebraMap
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) f
  · intro x
    obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) f x
    exact ⟨n, Submodule.Quotient.mk m, hm⟩
  · intro x hx
    refine ⟨0, ?_⟩
    have hzero := modulePureTransformToLocalization_injective f M
      (hx.trans (map_zero _).symm)
    simpa using hzero

/--
概要：純変換と元の加群の局所化の間の実際の線形同型。
方針：二つの局所化写像の普遍条件を比較する。
規約：Stacks 0815、同型は元の環上線形。
使われ方：Cartier 境界の外での純変換の不変性。
-/
def modulePureTransformLocalizationEquiv :
    LocalizedModule (Submonoid.powers f) (modulePureTransform f M) ≃ₗ[R]
      LocalizedModule (Submonoid.powers f) M :=
  IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) (modulePureTransform f M))
    (modulePureTransformToLocalization f M)

/--
概要：純変換の局所化の比較同型は元の加群からの写像を保存する。
方針：局所化の比較同型の生成元での公式を使う。
規約：Stacks 0815、商写像と局所化写像を明示する。
使われ方：開部分上での写像の交換式。
-/
theorem modulePureTransformLocalizationEquiv_mk (m : M) :
    modulePureTransformLocalizationEquiv f M
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (modulePureTransform f M)
        (Submodule.Quotient.mk m)) =
      LocalizedModule.mkLinearMap (Submonoid.powers f) M m :=
  IsLocalizedModule.linearEquiv_apply _ _ _ _

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
