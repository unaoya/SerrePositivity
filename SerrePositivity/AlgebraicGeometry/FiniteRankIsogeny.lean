module

public import SerrePositivity.AlgebraicGeometry.LocalizationIsogeny
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
概要：KST §5、Stacks 0815 の境界外で有限階数自由な加群の分母倍同型。
方針：自由加群の局所化を有限直積の局所化で表し、同型の分母を払う。
規約：階数零も同じ有限添字集合の形式で扱う。
使われ方：行列式中心を実際に選ぶ平坦化の特殊形。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R M M' ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [Module.FinitePresentation R M]
  [Finite ι]

/--
概要：境界外で有限階数自由な有限表示加群と自由加群を冪倍で互いに比較する。
方針：有限直積への局所化写像を指定して一般の分母倍同型を使う。
規約：KST §5、Stacks 0815、同じ指数が両合成に使われる。
使われ方：行列式中心が境界の冪を含むことと純変換の核の消滅。
-/
theorem exists_finiteRank_isogeny (f : R) (μ : M →ₗ[R] M')
    [IsLocalizedModule.Away f μ] (e : M' ≃ₗ[R] (ι → Localization.Away f)) :
    ∃ (n : ℕ) (g : M →ₗ[R] (ι → R)) (h : (ι → R) →ₗ[R] M),
      h.comp g = f ^ n • LinearMap.id ∧ g.comp h = f ^ n • LinearMap.id := by
  let ν : (ι → R) →ₗ[R] (ι → Localization.Away f) :=
    LinearMap.pi (fun i => (Algebra.linearMap R (Localization.Away f)).comp (LinearMap.proj i))
  have : IsLocalizedModule.Away f ν := inferInstance
  obtain ⟨s, g, h, hg, hh⟩ := exists_localization_isogeny (Submonoid.powers f) μ ν e
  obtain ⟨r, ⟨n, rfl⟩⟩ := s
  exact ⟨n, g, h, hg, hh⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
