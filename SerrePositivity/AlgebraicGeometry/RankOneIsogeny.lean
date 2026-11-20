module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalizationIsogeny
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
概要：KST §5、Stacks 0815 の境界外で階数一自由な加群の分母消去。
方針：局所化された加群と環の同型に、有限表示加群の分母倍同型を適用する。
規約：有限表示性は元の基礎環上で仮定する。
使われ方：実際の像イデアルを平坦化中心として選ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [Module.FinitePresentation R M]

/--
概要：境界外で階数一自由な有限表示加群と環を冪倍で互いに比較する。
方針：一般の局所化同型の分母消去で得た分母を境界元の冪に書く。
規約：KST §5、Stacks 0815、同型は元の環上線形で十分。
使われ方：境界冪を含む実際の像イデアルの構成。
-/
theorem exists_rankOne_isogeny (f : R) (μ : M →ₗ[R] M')
    [IsLocalizedModule.Away f μ] (e : M' ≃ₗ[R] Localization.Away f) :
    ∃ (n : ℕ) (g : M →ₗ[R] R) (h : R →ₗ[R] M),
      h.comp g = f ^ n • LinearMap.id ∧ g.comp h = f ^ n • LinearMap.id := by
  obtain ⟨s, g, h, hg, hh⟩ := exists_localization_isogeny (Submonoid.powers f)
    μ (Algebra.linearMap R (Localization.Away f)) e
  obtain ⟨r, ⟨n, rfl⟩⟩ := s
  exact ⟨n, g, h, hg, hh⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
