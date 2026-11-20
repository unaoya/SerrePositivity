module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FiniteRankFlattening
public import SerrePositivity.AlgebraicGeometry.GeneratorChartFlatness

/-!
概要：KST §5、Stacks 0815 の Noether 環上の有限加群の自由な補開集合に沿う平坦化。
方針：行列式生成元の被覆上の自由化を、重なりの局所化によって全標準チャートへ移す。
規約：補開集合上の自由加群との同型を入力し、一般の有限型代数上の有限加群とは区別する。
使われ方：平坦化定理の有限加群の特殊形の実際の中心。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R M M' ι : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup M'] [Module R M'] [Finite ι]

/--
概要：境界外で有限階数自由な有限加群を全標準チャートで平坦にする admissible 中心が存在。
方針：行列式中心を選び、その生成元チャートから任意のチャートへ平坦性を移す。
規約：KST §5、Stacks 0815、正則な境界元と実際の局所化同型を仮定する。
使われ方：Noether 特殊形の平坦化に向けた有限加群の場合の完成形。
-/
theorem exists_finiteRank_flattening_center (f : R) (hf : f ∈ nonZeroDivisors R)
    (μ : M →ₗ[R] M') [IsLocalizedModule.Away f μ]
    (e : M' ≃ₗ[R] (ι → Localization.Away f)) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen f ≤ affineCenterComplement I ∧
      ∀ a : I, letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
        Module.Flat (BlowupChartRing I a)
          (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨g, hg, hU, hflat⟩ := exists_finiteRank_determinantal_flattening f hf μ e
  refine ⟨determinantalCenter g, hg, hU, ?_⟩
  exact pureTransform_flat_of_generatorCharts (determinantalCenter g)
    (determinantalCenterGenerator g) f M rfl hflat

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
