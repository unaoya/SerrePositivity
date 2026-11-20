module

public import SerrePositivity.AlgebraicGeometry.FiniteFlatLocalCenters
public import SerrePositivity.AlgebraicGeometry.AffineFlatPureComposition

/-!
概要：KST §5、Stacks 0815 の Noether 環上有限な加群の Cartier 境界に沿う平坦化。
方針：自由な境界外のチャート被覆、局所中心、共通細分、二段 blowup の支配を合成する。
規約：有限性は基礎環上の加群としての有限性。一般の有限型代数上の有限加群とは区別する。
使われ方：一般の平坦化定理に向けた有限加群の場合の実際の中心。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：境界外で平坦な有限加群に、純変換を全標準チャート上で平坦にする実際の admissible 中心が存在。
方針：分子中心の有限チャート上で平坦化し、その局所中心を一つの基礎環上の中心へ降ろす。
規約：KST §5、Stacks 0815、基礎環は Noether で境界元は非零因子。
使われ方：Noether・有限加群の場合の平坦化の結論。
-/
theorem exists_noetherian_finite_flattening_center {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ nonZeroDivisors R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module (Localization.Away f) N] [IsScalarTower R (Localization.Away f) N]
    (μ : M →ₗ[R] N) [IsLocalizedModule.Away f μ] [Module.Flat (Localization.Away f) N] :
    ∃ J : Ideal R, J.FG ∧ PrimeSpectrum.basicOpen f ≤ affineCenterComplement J ∧
      ∀ b : J, letI : Algebra R (BlowupChartRing J b) := (chartBaseMap J b).toAlgebra
        Module.Flat (BlowupChartRing J b)
          (modulePureTransform (chartBaseMap J b f) (BlowupChartRing J b ⊗[R] M)) := by
  classical
  obtain ⟨s, _, hU, hlocal⟩ := exists_noetherian_finite_local_flattening_centers f hf μ
  choose K hKfg hK hflat using hlocal
  exact exists_affine_flatPure_center_of_local_centers
    (freeCoverNumeratorIdeal f s) (freeCoverNumeratorGenerator f s) rfl f hf M hU K hK hflat

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
